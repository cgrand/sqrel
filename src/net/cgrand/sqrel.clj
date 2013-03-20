(ns net.cgrand.sqrel
  "The SQL library that won't drive you nuts."
  (:require [clojure.java.jdbc :as sql])
  (:require [clojure.string :as str]))

(defn- reduce-by [k f init coll]
  (reduce (fn [m x]
            (let [k (k x)]
              (assoc m k (f (m k init) x))))
    {} coll))

(defmacro ^:private cond-let
  ([x] x)
  ([t x & more]
    (cond 
      (= t :let) `(let ~x (cond-let ~@more))
      (= t :else) x
      (vector? t) `(if-let ~t ~x (cond-let ~@more))
      :else `(if ~t ~x (cond-let ~@more)))))

(defprotocol Rel
  (spec [r]))

(defn rel? [x]
  (satisfies? Rel x))

(defn aggregated? [x]
  (boolean (seq (:manies (:expr (spec x))))))

(declare -project)

(deftype SQRel [m]
  Rel
  (spec [r] m)
  clojure.lang.ILookup
  (valAt [r k]
    (SQRel. (-project m k)))
  clojure.lang.IFn
  (invoke [this x]
    (SQRel. (-project m x)))
  Object
  (equals [this that]
    (and (rel? that) (= (spec this) (spec that))))
  (hashCode [this]
    (unchecked-int (bit-xor 36rSQREL (hash m)))))

(def ^:private impossible-constraint [:impossible])

(defn- impossible? [cs]
  (contains? cs impossible-constraint))

(def ^:private impossible-constraints #{impossible-constraint})

; no constraint simplification for now
#_((defmulti -refine-constraint (fn [[tag1] [tag2]] [tag1 tag2]))

(defmethod -refine-constraint :default [c1 c2] [c1 c2])

(defn refine-constraint [[tag1 :as c1] [tag2 :as c2]]
  (if (or (nil? c2) (= :impossible tag2))
    [c1 c2]
    (-refine-constraint c1 c2)))

(defn simplify-constraints
  ([] #{})
  ([cs] cs)
  ([csa csb]
    (if (or (impossible? csa) (impossible? csb))
      impossible-constraints
      (let [csa (or csa #{})
            csb (or csb #{})
            [csa csb] 
              (reduce 
                (fn [[csa csb] cb]
                  (let [[csa cb]
                        (reduce 
                          (fn [[csa cb :as x] ca]
                            (let [[ca' cb] (refine-constraint ca cb)
                                  csa (cond-let
                                        (= ca' ca) csa 
                                        :let [csa (disj csa ca)]
                                        (nil? ca') csa
                                        :else (conj csa ca'))]
                              [csa cb])) 
                          [csa cb] csa)]
                    [csa (if cb (conj csb cb) csb)]))
                [csa #{}] csb)
              cs (into csa csb)]
        (if (impossible? cs) impossible-constraints cs)))))

(defmethod -refine-constraint [:eq :eq] [[_ eqsa :as ca] [_ eqsb :as cb]]
  (if (some eqsa eqsb)
    [nil [:eq (into eqsa eqsb)]]
    [ca cb]))

(defmethod -refine-constraint [:eq :neq] [[_ eqs :as ca] [_ neqs :as cb]]
  (if-let [x (some eqs neqs)]
    (let [neqs (reduce disj neqs (disj eqs x))]
      [ca (if (next neqs) 
            [:neq neqs]
            [:impossible])])
    [ca cb]))

(defmethod -refine-constraint [:neq :eq] [[_ neqs :as ca] [_ eqs :as cb]]
  (if-let [x (some eqs neqs)]
    (let [neqs (reduce disj neqs (disj eqs x))]
      (if (next neqs) 
        [[:neq neqs] cb]
        [ca [:impossible]]))
    [ca cb])))

(defn rel [& rs]
  (let [rs (map spec rs)]
    (SQRel. {:table-aliases (reduce into {} (map :table-aliases rs))
             :constraints (reduce into #{} (map :constraints rs))})))

(defn maybe [r]
  (let [r (spec r)]
    (SQRel. (assoc r :maybe true))))

(defn another [r]
  ; TODO very crude, works only on tables
  (let [s (spec r)
        tbl (-> s :table-aliases vals first)]
    (SQRel. (assoc s :table-aliases {(name (gensym tbl)) tbl}))))

(def ^:private ground-ts "The ground pseudo table's table spec."
  [::ground ::ground])

(defn- col-spec [x]
  (when-let [{col :col
              tbls :table-aliases
              {cols :cols} :expr} (and (rel? x) (spec x))]
    (if col
      (let [[alias tbl] (first tbls)]
        [alias tbl col])
      (get cols ()))))

(defn- col-rel [[alias tbl col]]
  (SQRel. {:table-aliases {alias tbl} :col col}))

(defn- complain [& xs]
  (throw (RuntimeException. (apply str xs))))

(defn- entries [x]
  (if (map? x) 
    (seq x)
    (map-indexed vector x)))

(defn- paths-to [x key-fn]
  (let [ks+paths (fn ks+paths [x]
                   (if-let [k (key-fn x)]
                     (list [k ()])
                     (when (associative? x)
                       (for [[p v] (entries x)
                             [k path] (ks+paths v)]
                         [k (conj path p)]))))]
    (reduce-by first #(conj %1 (second %2)) #{} (ks+paths x))))

(defn many [x] (with-meta [x] {::many true}))
(defn many? [x] (-> x meta ::many))

(defn- nested-expr-rels [expr]
  (-> expr (paths-to #(and (rel? %) (-> % spec :expr :expr)))
    (dissoc nil false)))

(defn- expand-expr [expr]
  (let [expr+ps (nested-expr-rels expr)] 
    {:expr (if (= (-> expr+ps vals first) #{()})
             (-> expr+ps keys first)
             (reduce-kv (fn [expr sub-expr ps]
                          (reduce (fn [expr p] (assoc-in expr p sub-expr))
                            expr ps)) 
               expr expr+ps))
     :rels (for [ps (vals expr+ps), p ps] (get-in expr p))}))

;; 1. find all path to rels BUT those that are below Many
;; 2. find all paths to Many instances
(defn expr-spec
  ([expr] (expr-spec expr col-spec))
  ([expr cols-fn]
    (let [{:keys [expr rels]} (expand-expr expr)
          {maniesp :many relsp :rel}
          (paths-to expr #(cond 
                            (many? %) :many
                            (rel? %) :rel))
          cols (into {} (for [p relsp] [p (cols-fn (get-in expr p))]))
          manies (into {} (for [p maniesp] 
                            (let [[sub-expr] (get-in expr p)]
                              [p (expr-spec sub-expr cols-fn)])))]
      {:cols cols
       :manies manies
       :expr expr
       :rels rels})))

(defn- -project [m x]
  (let [{tbls :table-aliases expr :expr col-name :col-name-fn} m
        explicit-col (fn [x] (or (get expr x)
                               (when-let [[tbl :as cs] (col-spec x)]
                                 (if (tbls tbl) 
                                   cs
                                   (complain "Column not present in rel: " cs)))))
        cols (if col-name
               #(or (explicit-col %) 
                  (let [[alias tbl] (first tbls)
                        col (or (col-name %)
                              (complain (format "No column found for %s in table %s." % tbl)))]
                    [alias tbl col]))
               #(or (explicit-col %) (complain "Can't map alias " %)))
        ids (get (paths-to x keyword?) true)
        x (if (= ids #{()})
            (col-rel (cols x))
            (reduce (fn [x p]
                      (update-in x p (comp col-rel cols))) x ids))
        expr (expr-spec (if (set? x) (zipmap x x) x) cols)]
    (assoc m
      :expr expr)))

(defn- expr-cols [{:keys [manies cols]}]
  (distinct (concat (vals cols) (mapcat expr-cols (vals manies)))))

(defn- expr-rels [{:keys [manies cols expr rels]}]
  (let [col-rels (map #(get-in expr %) (keys cols))]
    (concat rels col-rels (mapcat expr-rels (vals manies)))))

(defn expr-rel [x]
  (let [expr (expr-spec x)
        rels (expr-rels expr)
        r (spec (apply rel rels))]
    (SQRel. (assoc r :expr expr))))

(defn sqlified-name [x]
  (if (or (keyword? x) (symbol? x))
    (str/replace (name x) \- \_)
    x))

(defn cols-fn [cols]
  (if (or (set? cols) (sequential? cols))
    (comp sqlified-name (set cols))
    (or cols sqlified-name)))

(defn some-cols [& more-cols]
  (apply some-fn (map cols-fn more-cols)))

(defn table [tblname & {alias :as cols :cols}]
  (SQRel. {:table-aliases {(or alias tblname) tblname}
           :col-name-fn (cols-fn cols)}))

(defn- spec-any [x]
  (if (rel? x) 
    (spec x)
    {:expr {:expr x}}))

(defn- table-spec [col-spec]
  (let [[alias tbl col] col-spec]
    [alias tbl]))

(defn- commutative-constraints [tag rels]
  (cond-let
    :let [exprs (map :expr rels)
          sure-exprs (map :expr (remove :maybe rels))]
    (some (comp seq :manies) exprs)
      (throw (RuntimeException. "Can't compare aggregates"))
    :let [cols (mapcat :cols exprs)
          ps (set (keys cols))
          tss-of (fn [expr]
                   (map #(if-let [c (get (:cols expr) %)]
                           (table-spec c)
                           ground-ts) ps))
          sures (set (mapcat tss-of sure-exprs))
          all (set (mapcat tss-of exprs))
          mts (set (for [a all b all :when (and (not= a b) (sures b))] [:mt a b]))]
    :else
      (reduce into mts
        (for [[p cols] (reduce-by key (fn [s kv] (conj s (val kv))) #{} cols)
              :let [vs (remove rel? (map #(get-in (:expr %) p) exprs))]]
          #{[tag (into cols vs)]}))))

(defn eq [& rs]
  (apply rel 
    (let [rs (map spec-any rs)] 
      (SQRel. 
        {:constraints (commutative-constraints :eq rs)}))
    (filter rel? rs)))

(defn neq [& rs]
  (apply rel 
    (let [rs (map spec-any rs)] 
      (SQRel. {:constraints (commutative-constraints :neq rs)}))
    (filter rel? rs)))

(defmulti join-constraints (fn [[ta a] [tb b]] [ta tb]))

#_(
;; outdated, not working
(defmethod join-constraints [:map :map] [[ta a] [tb b]]
  (reduce merge-constraints
    (for [[k va] a :when (and (contains? b k)
                           (not= va (get b k)))] 
      #{[:eq #{va (get b k)}]})))

(defmethod join-constraints :default [a b]
  (eq-constraints a b))

(defn join [& rs]
  (apply rel 
    (let [rs (map (comp :expr spec-any) rs)] 
      (SQRel. 
        {:constraints ; it's heavy handed n^2 instead of n
         (reduce merge-constraints
           (for [[a & bs :as rs] (iterate next rs)
                 :while bs
                 b bs]
             (join-constraints (:expr a) (:expr b))))}))
    rs)))

(defmulti join-order (fn [tag x] tag))

(defmulti constraint-to-sql (fn [tag x] tag))

(defn expr-sql [x]
  (if (vector? x)
    (str (nth x 0) \. (nth x 2))
    (str x)))

(defmethod constraint-to-sql :impossible [tag _]
  "FALSE")

(defmethod constraint-to-sql :mt [tag _]
  nil)

(defmethod constraint-to-sql :eq [tag xs]
  (let [[x & xs] (seq xs)] 
    (str/join " AND " 
      (for [y xs] (str (expr-sql x) "=" (expr-sql y))))))

(defmethod constraint-to-sql :neq [tag xs]
  (let [[x & xs] (seq xs)] 
    (str "(" (str/join " OR " 
               (for [y xs] (str (expr-sql x) "!=" (expr-sql y)))) ")")))

(defn- constraints-to-sql [cs]
  (when-let [exprs (seq (keep (fn [[tag x]] (constraint-to-sql tag x)) cs))]
    (str/join " AND " exprs)))

(declare constraints-to-from-where-sql)

(defn sql-from [rel]
  (-> rel spec :constraints constraints-to-from-where-sql))

(defn sql-order-by [rel]
  (let [{:keys [manies cols]} (:expr (spec rel))]
    (when (seq manies)
      (str " ORDER BY " (str/join ", " (map expr-sql (vals cols)))))))

(defn ^String sql [rel]
  (let [r (spec rel)
        cols (cond-let
               [[alias _ col] (col-spec rel)]
                 (str alias \. col)
               [cols (seq (expr-cols (:expr r)))]
                 (str/join ", " (map expr-sql cols))
               :else "*") ]
    (str "SELECT " cols " FROM " (sql-from rel)
      (sql-order-by rel))))

(defmethod print-method SQRel [r ^java.io.Writer w]
  (.write w  "#<SQRel ")
  (.write w (sql r))
  (.write w  ">"))

(defn- map-rs [f ^java.sql.ResultSet rs]
  (lazy-seq
    (when (.next rs)
      (cons (f rs) (map-rs f rs)))))

(declare fill-fn keyed-fill-fn merge-aggregate-fn unkey-aggregate-fn)

(defn collect [expr & rs]
  (let [r1 (expr-rel expr)
        r (apply rel r1 rs)]
    (SQRel. (assoc (spec r) :expr (:expr (spec r1))))))

(defn select
  ([r]
    (let [{expr :expr} (spec r)
          col-pos (into {} (map-indexed (fn [i x] [x (inc i)]) (expr-cols expr)))
          f (cond
              (aggregated? r) (keyed-fill-fn expr true)
              expr (fill-fn expr))
          aggregate (if (aggregated? r)
                      (let [merge (merge-aggregate-fn expr)
                            unkey (unkey-aggregate-fn expr)]
                        (fn [s]
                          (->> s
                            (partition-by first)
                            (map (fn [kvs]
                                   (unkey (reduce merge
                                            (map second kvs))))))))
                      identity)
          rs-f (if f
                 (fn [rs]
                   (->> rs
                     (map-rs (fn [^java.sql.ResultSet rs]
                               (f #(.getObject rs (int (col-pos %))))))
                     aggregate))
                 resultset-seq)]
      (doall (rs-f (-> (sql/connection) (.prepareStatement (sql r)) .executeQuery)))))
  ([expr & rs]
    (let [r1 (expr-rel expr)
          r (apply rel r1 rs)]
      (select (apply collect expr rs)))))

;; filling and aggregating

(defn- balance [n f & args] 
  (if (> (count args) n)
    (apply balance n f (map #(apply f %) (partition-all n args)))
    (apply f args)))

(defn- comp-first
  ([] (fn [x _] x))
  ([f] f)
  ([f g] (fn [a b] (f (g a b) b))))

(defn merge-aggregate-fn 
  "Returns a function which merge two similarly keyed values."
  [{manies :manies}]
  (let [sub-merges 
        (for [[p spec] manies]
          (let [sub-merge (merge-aggregate-fn spec)]
            (cond ; optimization
              (next p)
                (fn [a b]
                  (assoc-in a p (merge-with sub-merge (get-in a p) (get-in b p))))
              (seq p)
                (let [[k] p]
                  (fn [a b]
                    (assoc a k (merge-with sub-merge (get a k) (get b k)))))
              :else
                (fn [a b]
                  (merge-with sub-merge a b)))))]
    (apply balance 2 comp-first sub-merges)))

(defn unkey-aggregate-fn 
  "Returns a function which finalizes aggregates by turning them into sets 
   (effectively removing the keys of the map)."
  [{manies :manies}]
  (let [sub-unkeys 
        (for [[p spec] manies]
          (let [sub-unkey (unkey-aggregate-fn spec)
                unkey #(->> % vals (map sub-unkey) set)]
            (cond ; optimization
              (next p)
                (fn [a]
                  (assoc-in a p (unkey (get-in a p))))
              (seq p)
                (let [[k] p]
                  (fn [a]
                    (assoc a k (unkey (get a k)))))
              :else
                (fn [a]
                  (unkey a)))))]
    (apply balance 3 comp sub-unkeys)))

(declare keyed-fill-fn)

(defn fill-fn 
  "Returns a function which takes a data function (from [\"tbl-alias\" \"colname\"]
   to column value) and returns an instanciated expression -- including keyed
   many-maps."
  [{:keys [manies cols expr]}]
  (let [fills
        (for [[p col] cols]
          (cond ; optimization
            (next p)
              (fn [a data]
                (assoc-in a p (data col)))
            (seq p)
              (let [[k] p]
                (fn [a data]
                  (assoc a k (data col))))
            :else
              (fn [a data]
                (data col))))
        fill-manies
        (for [[p spec] manies]
          (let [subfill (keyed-fill-fn spec)]
            (cond ; optimization
              (next p)
                (fn [a data]
                  (assoc-in a p (subfill data)))
              (seq p)
                (let [[k] p]
                  (fn [a data]
                    (assoc a k (subfill data))))
              :else
                (fn [a data]
                  (conj {} (subfill a data))))))
        fill (apply balance 2 comp-first (concat fills fill-manies))]
    (fn [data]
      (fill expr data))))

(defn keyed-fill-fn
  "Like fill-fn but instead of returning only the instanciated value, the map
   [key instanciated-value] or {key instanciated-value} is returned."
  ([spec] (keyed-fill-fn spec false))
  ([{:keys [cols] :as spec} as-entry]
    (let [fill-keys
          (for [[p col] cols]
            (fn [k data]
              (conj k (data col))))
          fill-key (apply balance 2 comp-first fill-keys)
          fill-val (fill-fn spec)]
      (if as-entry
        (fn [data]
          [(fill-key () data) (fill-val data)])
        (fn [data]
          (let [k (fill-key () data)]
            (if (every?  nil? k) ; testing a single not-null column would be better
              {}
              {(fill-key () data) (fill-val data)})))))))

(defn eval-expr [spec]
  (fill-fn spec))

(defmacro ^:private =>
  [x y]
  `(or ~y (not ~x)))

(defn- validate-rel-spec 
  "Some invariants." 
  [{:keys [expr] :as spec}]
  (and
    (=> expr 
      (and 
        (empty? (nested-expr-rels (:expr expr)))
        (every? (fn [[p _]] (many? (get-in expr p)))
          (:manies expr))
        (every? (fn [[p _]] (rel? (get-in expr p)))
          (:cols expr))))
    (=> (:col spec) (nil? expr))
    (=> (:col spec) (= 1 (count (:table-aliases))))
    (=> (:col-name-fn spec) (= 1 (count (:table-aliases))))))
 
(defn- scc 
  "Returns the strongly connected components of a graph specified by its nodes
   and a successor function succs from node to nodes.
   The used algorithm is Tarjan's one."
  ([g]
    (scc (keys g) g))
  ([nodes succs]
    (letfn [(sc [env node]
              ; env is a map from nodes to stack length or nil, nil means the node is known to belong to another SCC
              ; there are two special keys: ::stack for the current stack and ::sccs for the current set of SCCs
              #_{:post [(contains? % node)]}
              (if (contains? env node)
                env
                (let [stack (::stack env)
                      n (count stack)
                      env (assoc env node n ::stack (conj stack node))
                      env (reduce (fn [env succ]
                                    (let [env (sc env succ)]
                                      (assoc env node (min (or (env succ) n) (env node)))))
                            env (succs node))]
                  (if (= n (env node)) ; no link below us in the stack, call it a SCC
                    (let [nodes (::stack env)
                          scc (set (take (- (count nodes) n) nodes))
                          env (reduce #(assoc %1 %2 nil) env scc)] ; clear all stack lengths for these nodes since this SCC is done
                      (assoc env ::stack stack ::sccs (conj (::sccs env) scc)))
                    env))))]
      (::sccs (reduce sc {::stack () ::sccs #{}} nodes)))))

(defn- edges [nodes succs]
  (for [node nodes, succ (succs node)]
    [node succ]))

(defn- graph-map 
  "Takes a collection of edges [from to] and returns a map such that (get m x)
   returns the successors of x."
  [edges]
  (reduce-by first #(conj %1 (second %2)) #{} edges))

(defn- scc-graph
  ([g] (scc-graph (keys g) g))
  ([nodes succs]
    (let [sccs (scc nodes succs)
          scc-of (into {} (for [nodes sccs
                                node nodes] [node nodes]))
          empty-graph (zipmap sccs (repeat #{}))]
      (->> (edges nodes succs)
        (map #(map scc-of %))
        (remove (fn [[x y]] (= x y)))
        graph-map
        (merge empty-graph)))))

(defn- roots
  ([g] (roots (keys g) g))
  ([nodes succs]
    (reduce disj (set nodes) (mapcat succs nodes))))

#_(defn- rand-graph [n density]
  (let [g (zipmap (range n) (repeat #{}))
        m (Math/ceil (* n (dec n) density))]
    (reduce (fn [g [x y]]
              (update-in g [x] conj y))
      g (take m (distinct (repeatedly (juxt #(rand-int n) #(rand-int n))))))))

(defn- lmt-graph 
  "Returns a graph as map of the
    \"less maybe than\" relation."
  [mts]
  (graph-map (keep (fn [[tag mx y]] [y mx]) mts)))

(defmulti split-applicable-constraint (fn [[tag] tss new-tss] tag))

(defn- known-pred [tss]
  (fn [x]
    (if-let [[alias tbl col] (when (vector? x) x)]
      (contains? tss [alias tbl])
      true)))

(defmethod split-applicable-constraint :eq [[tag xs :as c] tss new-tss]
  (let [axs (filter (known-pred tss) xs)
        naxs (reduce disj xs axs)
        naxs (conj naxs (first (remove (known-pred new-tss) axs)))]
    (if (next axs)
      [[:eq axs] (when (next naxs) [:eq naxs])]
      [nil c])))

(defmethod split-applicable-constraint :neq [[tag xs :as c] tss new-tss]
  (if (every? (known-pred tss) xs)
    [c nil]
    [nil c]))

(defmethod split-applicable-constraint :impossible [c tss new-tss]
  [c c])

(defn- split-applicable-cs [cs tss new-tss]
  (if (= tss new-tss)
    [nil cs]
    (let [scs (map #(split-applicable-constraint % tss new-tss) cs)]
      [(keep first scs) (keep second scs)])))

(defn- scc-joins
  "Returns [cs joins] where cs is the remaining (not applied yet)
   constraints, joins is a collection of [ts cs] where ts is a table-spec
   and cs a collection of applicable constraints."
  [table-specs cs]
  (let [[cs joins _] (reduce (fn [[cs joins seen] ts]
                               (let [seen (conj seen ts)
                                     [acs nacs] (split-applicable-cs cs seen #{ts})]
                                 [nacs (conj joins [ts acs]) seen])) 
                       [cs [] #{}] (remove #{ground-ts} table-specs))]
    [cs joins]))

(defn- left-joins [r g cs]
  (letfn [(walk [tss cs seen]
            (let [[cs joins] (scc-joins tss cs)
                  seen (into seen tss)
                  [acs nacs] (split-applicable-cs cs seen tss)]
              (reduce (fn [[cs ljoins] tss]
                        (let [[cs ljs] (walk tss cs seen)]
                          [cs (into ljoins ljs)]))
                [nacs [[joins acs]]] (g tss))))]
    (walk r cs #{})))

(defn- scc-joins-sql [joins]
  (str/join " JOIN "
    (map (fn [[[alias tbl] cs]]
           (str tbl " " alias (when-let [on (constraints-to-sql cs)]
                                (str " ON " on))))
      joins)))

(defn- left-joins-sql [ljoins]
  (str/join " LEFT JOIN "
    (map (fn [[joins cs]]
           (str "(" (scc-joins-sql joins) ")"
             (when-let [on (constraints-to-sql cs)] (str " ON " on))))
      ljoins)))

(defn- constraints-to-from-where-sql [cs]
  (let [{mts true cs false} (group-by #(= (first %) :mt) cs)
        g (scc-graph (lmt-graph mts))
        rs (roots g)
        _ (when (next rs) (throw (Exception. "TODO")))
        [cs ljoins] (left-joins (first rs) g cs)
        from (left-joins-sql ljoins)
        where (constraints-to-sql cs)]
    (if where 
      (str from " WHERE " where) ; not so fast
      from)))


