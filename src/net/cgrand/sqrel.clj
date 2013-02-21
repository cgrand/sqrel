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

(defn- col-spec [x]
  (when-let [[t v] (and (rel? x) (:expr (spec x)))]
    (when (= t :val) v)))

(defn- complain [& xs]
  (throw (RuntimeException. (apply str xs))))

(defn- -restrict [m x]
  (let [{tbls :table-aliases cols :cols col-name :col-name-fn} m
        explicit-col (fn [x] (or (get cols x)
                               (when-let [[tbl :as cs] (col-spec x)]
                                 (if (tbls tbl) 
                                   cs
                                   (complain "Column not present in rel: " cs)))))
        cols (if col-name
               #(or (explicit-col %) 
                  (let [tbl (first (keys tbls))
                        col (or (col-name %)
                              (complain (format "No column found for %s in table %s." % tbl)))]
                    [tbl col]))
               #(or (explicit-col %) (complain "Can't map alias " %)))
        aliases (into {} 
                  (for [[k v] (cond
                                (map? x) x
                                (or (set? x) (vector? x)) (zipmap x x)
                                (keyword? x) {x x})]
                    [k (cols v)]))
        expr (cond
               (map? x) [:map (zipmap (keys x) (map cols (vals x)))]
               (set? x) [:map (zipmap x (map cols x))] 
               (vector? x) [:vector (vec (map cols x))]
               (keyword? x) [:val (cols x)])]
    (assoc m
      :cols aliases
      :expr expr)))

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
    (bit-xor 36rSQREL (hash m))))

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

(defmulti eq-constraints (fn [[ta a] [tb b]] [ta tb]))

(defn- pair [a b] ; to circumvent the createWithCheck in < 1.5
  (conj #{a} b))

(defmethod eq-constraints [:val :val] [[ta a] [tb b]]
  {:eq #{(pair a b)}})

(defmethod eq-constraints [:vector :vector] [[ta a] [tb b]]
  (when-not (= (count a) (count b))
    (complain "Can't compare"))
  {:eq (reduce #(merge-constraint :eq %1 %2) #{} 
         (map (fn [a b] #{(pair a b)}) a b))})

(defmethod eq-constraints [:map :map] [[ta a] [tb b]]
  (when-not (= (set (keys a)) (set (keys b)))
    (throw (RuntimeException. "Can't compare")))
  {:eq (reduce #(merge-constraint :eq %1 %2) #{}
         (map (fn [[k va]] #{(pair va (get b k))}) a))})

(defn- spec-expr [x]
  (cond
    (rel? x) (spec x)
    (map? x) {:expr [:map x]}
    (vector? x) {:expr [:vector x]}
    :else {:expr [:val x]}))

(defn eq [& rs]
  (apply rel 
    (let [rs (map spec-expr rs)] 
      (SQRel. 
        {:constraints 
         (reduce merge-constraints 
           (map #(eq-constraints (:expr (first rs)) (:expr %)) (next rs)))}))
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
    (str (nth x 0) \. (nth x 1))
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

(defn sql [rel]
  (let [r (spec rel)
        cols (if-let [cols (seq (vals (:cols r)))]
               (str/join ", " (map expr-sql cols))
               "*")]
    (str "SELECT " cols " FROM " (sql-from rel))))

(defmethod print-method SQRel [r ^java.io.Writer w]
  (.write w  "#<SQRel ")
  (if (and (= :val (-> r spec :expr first))
        (-> r spec :constraints nil?))
    (print-method (-> r spec :expr second expr-sql) w)
    (do
      (print-method (-> r spec :expr) w)
      (.write w  ", ")
      (print-method (sql-from r) w)))
  (.write w  ">"))

(defmulti eval-expr (fn [tag v col-pos] tag))

(defmethod eval-expr :val [tag x col-pos]
  (fn [^java.sql.ResultSet rs] 
    (if-let [i (col-pos x)] (.getObject rs (int i)) x)))

(defmethod eval-expr :vector [tag v col-pos]
  (fn [^java.sql.ResultSet rs] 
    (mapv #(if-let [i (col-pos %)] (.getObject rs (int i)) %) v)))

(defmethod eval-expr :map [tag m col-pos]
  (fn [^java.sql.ResultSet rs] 
    (reduce-kv #(if-let [i (col-pos %3)]
                  (assoc %1 %2 (.getObject rs (int i)))
                  %1) m m)))

(defn- map-rs [f ^java.sql.ResultSet rs]
  (lazy-seq
    (when (.next rs)
      (cons (f rs) (map-rs f rs)))))

(defn select
  ([r]
    (let [{cols :cols [type v] :expr} (spec r)
          col-pos (into {} (map-indexed (fn [i x] [x (inc i)]) (vals cols)))
          f (eval-expr type v col-pos)]
      (doall (map-rs f (-> (sql/connection) (.prepareStatement (sql r)) .executeQuery)))))
  ([expr r]
    (select (r expr)))
  ([expr r & rs]
    (select ((apply rel r rs) expr))))
