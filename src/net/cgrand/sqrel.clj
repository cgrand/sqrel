(ns net.cgrand.sqrel
  "The SQL library that won't drive you nuts."
  (:require [clojure.java.jdbc :as sql])
  (:require [clojure.string :as str]))

(defn maybe [])
(defn many [])

(defprotocol Rel
  (spec [r]))

(defn rel? [x]
  (satisfies? Rel x))

(defn aggregated? [x]
  (boolean (seq (:manies (:expr (spec x))))))

(declare -restrict)

(deftype SQRel [m]
  Rel
  (spec [r] m)
  clojure.lang.ILookup
  (valAt [r k]
    (SQRel. (-restrict m k)))
  clojure.lang.IFn
  (invoke [this x]
    (SQRel. (-restrict m x)))
  Object
  (equals [this that]
    (= (spec this) (spec that)))
  (hashCode [this]
    (unchecked-int (bit-xor 36rSQREL (hash m)))))

(defmulti merge-constraint (fn [tag a b] tag))

(defn merge-constraints
  ([] {})
  ([c] c)
  ([ca cb]
    (persistent!
      (reduce (fn [c [k v]]
                (assoc! c k (let [w (c k c)]
                              (if (identical? w c)
                                v
                                (merge-constraint k (c k) v)))))
        (transient ca) cb))))

(defn rel [& rs]
  (let [rs (map spec rs)]
    (SQRel. {:table-aliases (reduce into {} (map :table-aliases rs))
              :constraints (reduce merge-constraints {} 
                             (map :constraints rs))})))

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

(defn- reduce-by [k f init coll]
  (reduce (fn [m x]
            (let [k (k x)]
              (assoc m k (f (m k init) x))))
    {} coll))

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

;; 1. find all path to rels BUT those that are below Many
;; 2. find all paths to Many instances
(defn expr-spec
  ([expr] (expr-spec expr col-spec))
  ([expr cols-fn]
    (let [{maniesp :many relsp :rel}
          (paths-to expr #(cond 
                            (many? %) :many
                            (rel? %) :rel))
          cols (into {} (for [p relsp] [p (cols-fn (get-in expr p))]))
          manies (into {} (for [p maniesp] 
                            (let [[sub-expr] (get-in expr p)]
                              [p (expr-spec sub-expr cols-fn)])))]
      {:cols cols
       :manies manies
       :expr expr})))

(defn- -restrict [m x]
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

(defn- expr-rels [{:keys [manies cols expr]}]
  (let [rels (map #(get-in expr %) (keys cols))]
    (concat rels (mapcat expr-rels (vals manies)))))

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

(defn- pair [a b] ; to circumvent the createWithCheck in < 1.5
  (conj #{a} b))

(defn- blank-expr 
  ([expr cols]
    (reduce (fn [expr [p]] (if (seq p)
                             (assoc-in expr p nil)
                             nil)) expr cols))
  ([expr cola colb]
    (-> expr (blank-expr cola) (blank-expr colb))))

(defn eq-constraints [{ea :expr ma :manies ca :cols}
                      {eb :expr mb :manies cb :cols}]
  (cond
    (or (seq ma) (seq ma))
      (throw (RuntimeException. "Can't compare aggregates"))
    (not= (blank-expr ea ca cb) (blank-expr eb ca cb))
      {:eq #{#{0 1}}}
    :else
    {:eq (reduce #(merge-constraint :eq %1 %2) #{}
           (concat 
             (for [[pa ta] ca
                   :let [tb (get cb pa)]
                   :when (and tb (not= ta tb))]
               #{#{ta tb}})
             (for [[c e] [[ca eb] [cb ea]]
                   [p t] c
                   :let [x (get-in e p)]
                   :when (not (or (rel? x) (many? x)))]
               #{#{t x}})))}))

(defn- spec-expr [x]
  (if (rel? x) 
    (:expr (spec x))
    {:expr x}))

(defn eq [& rs]
  (apply rel 
    (let [rs (map spec-expr rs)] 
      (SQRel. 
        {:constraints 
         (reduce merge-constraints 
           (map #(eq-constraints (first rs) %) (next rs)))}))
    (filter rel? rs)))

(defmulti join-constraints (fn [[ta a] [tb b]] [ta tb]))

(defmethod join-constraints [:map :map] [[ta a] [tb b]]
  {:eq (reduce #(merge-constraint :eq %1 %2) #{}
         (for [[k va] a :when (contains? b k)] 
           #{(pair va (get b k))}))})

(defmethod join-constraints :default [a b]
  (eq-constraints a b))

(defn join [& rs]
  (apply rel 
    (let [rs (map spec rs)] 
      (SQRel. 
        {:constraints ; it's heavy handed n^2 instead of n
         (reduce merge-constraints
           (for [[a & bs :as rs] (iterate next rs)
                 :while bs
                 b bs]
             (join-constraints (:expr a) (:expr b))))}))
    rs))

(defmethod merge-constraint :eq [tag partition-a partition-b]
  (reduce (fn [partition xs] 
            (let [ps (filter (fn [s] (some #(contains? s %) xs)) partition)]
              (conj (reduce disj partition ps)
                (reduce into xs ps)))) 
    partition-a partition-b))

(defmulti constraint-to-sql (fn [tag x] tag))

(defn expr-sql [x]
  (if (vector? x)
    (str (nth x 0) \. (nth x 2))
    (str x)))

(defmethod constraint-to-sql :eq [tag partition]
  (when-let [exprs (seq (for [xs partition :let [x (first xs)] y (next xs)]
                          (str (expr-sql x) "=" (expr-sql y))))]
    (str/join " AND " exprs)))

(defn sql-from [rel]
  (let [r (spec rel)
        tables (str/join ", " (for [[alias table] (:table-aliases r)] 
                                (str table " " alias)))
        where-exprs (keep (fn [[tag x]] (constraint-to-sql tag x))
                      (:constraints r))
        sql (if (seq where-exprs) 
              (str tables " WHERE " (str/join " AND " where-exprs))
              tables)]
    sql))

(defn sql-order-by [rel]
  (let [{:keys [manies cols]} (:expr (spec rel))]
    (when (seq manies)
      (str " ORDER BY " (str/join ", " (map expr-sql (vals cols)))))))

(defn ^String sql [rel]
  (let [r (spec rel)
        cols (if-let [[alias _ col] (col-spec rel)]
               (str alias \. col)
               (if-let [cols (seq (expr-cols (:expr r)))]
                 (str/join ", " (map expr-sql cols))
                 "*")) ]
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

(defn project [expr & rs]
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
      (select (SQRel. (assoc (spec r) :expr (:expr (spec r1))))))))

;; filling ane aggregating

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
          {(fill-key () data) (fill-val data)})))))

(defn eval-expr [spec]
  (fill-fn spec))

(defn- validate-rel-spec 
  "Rudimentary invariants." 
  [{:keys [expr] :as spec}]
  (and
    (and (:col spec) (= 1 (count (:table-aliases))))
    (and (:col-name-fn spec) (= 1 (count (:table-aliases))))
    (every? (fn [[p _]] (many? (get-in expr p)))
      (:manies (:expr spec)))
    (every? (fn [[p _]] (rel? (get-in expr p)))
      (:cols (:expr spec)))))
