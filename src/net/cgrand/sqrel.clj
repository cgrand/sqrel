(ns net.cgrand.sqrel
  "The SQL library that won't drive you nuts."
  (:require [clojure.java.jdbc :as sql])
  (:require [clojure.string :as str]))

#_((def db {:classname "org.h2.Driver"
         :subprotocol "h2"
         :subname "mem:test;DB_CLOSE_DELAY=-1"})

(sql/with-connection db
  (sql/create-table :employee
    [:id "INT"]
    [:name "VARCHAR"]
    [:dept_id "INT"])
  (sql/create-table :dept
    [:id "INT"]
    [:name "VARCHAR"])
  (sql/insert-values :employee [:id :name :dept_id]
    [1 "John Doe" 1]
    [2 "Jane Doe" 1]
    [3 "Homer Simpson" 2])
  (sql/insert-values :dept [:id :name]
    [1 "Sales"]
    [2 "Maintenance"]))

(table "employee")
{:table-aliases {"employee" "employee"}}
"SELECT * FROM employee employee"


(:id (table "employee"))
{:table-aliases {"employee" "employee"}
 :cols {:id ["employee" "id"]}
 :expr [identity :id] ; or :expr [identity ["employee" "id"]]
 }
"SELECT employee.id FROM employee employee"

(eq (:dept_id (table "employee")) (:id (table "dept")))
{:table-aliases {"employee" "employee" "dept" "dept"}
 :constraints #{[:eq ["employee" "dept_id"] ["dept" "id"]]}
 }
"SELECT * FROM employee employee, dept dept WHERE dept.id = employee.dept_id"

); a rel has an expression

(defn restrict []
  )

(defn maybe [])
(defn many [])

(defn- -restrict [m x]
  (let [{tbls :table-aliases cols :cols} m
        cols (if (next tbls)
               (fn [k] (or (get cols k) 
                         (throw (RuntimeException. (str "Can't map alias " k)))))
               (let [tbl (first (keys tbls))]
                 (fn [k]
                   (or (get cols k) [tbl (name k)]))))
        aliases (into {} 
                  (for [[k v] (cond
                                (map? x) x
                                (or (set? x) (vector? x)) (zipmap x x)
                                (keyword? x) {x x})]
                    [k (cols v)]))
        expr (cond
               (map? x) [:map (zipmap (keys x) (map cols (vals x)))]
               (set? x) [:map x (zipmap x (map cols x))] 
               (vector? x) [:vector (vec (map cols x))]
               (keyword? x) [:val (cols x)])]
    (assoc m
      :cols aliases
      :expr expr)))

(defprotocol Rel
  (spec [r]))

(defn rel? [x]
  (satisfies? Rel x))

(deftype SQLRel [m]
  Rel
  (spec [r] m)
  clojure.lang.ILookup
  (valAt [r k]
    (SQLRel. (-restrict m k)))
  clojure.lang.IFn
  (invoke [this x]
    (SQLRel. (-restrict m x)))
  Object
  (toString [r]
    (pr-str (str "#" (class r) [m]))))

(defmethod print-method SQLRel [r w]
  (.write w  (str "#" (.getName ^Class (class r)) "["))
  (print-method (spec r) w)
  (.write w  "]"))

(defmethod print-dup SQLRel [r ^java.io.Writer w]
  (.write w  (str "#" (.getName ^Class (class r)) "["))
  (print-dup (spec r) w)
  (.write w  "]"))

(defn table [tblname]
  (SQLRel. {:table-aliases {tblname tblname}}))

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
    (SQLRel. {:table-aliases (reduce into {} (map :table-aliases rs))
              :constraints (reduce merge-constraints {} 
                             (map :constraints rs))})))

(defmulti eq-constraints (fn [[ta a] [tb b]] [ta tb]))

(defn- pair [a b] ; to circumvent the createWithCheck in < 1.5
  (conj #{a} b))

(defmethod eq-constraints [:val :val] [[ta a] [tb b]]
  {:eq #{(pair a b)}})

(defmethod eq-constraints [:vector :vector] [[ta a] [tb b]]
  (when-not (= (count a) (count b))
    (throw (RuntimeException. "Can't compare")))
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
      (SQLRel. 
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
      (SQLRel. 
        {:constraints 
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

(defn sql [r]
  (let [r (spec r)
        cols (if-let [cols (seq (vals (:cols r)))]
               (str/join ", " (map expr-sql cols))
               "*")
        tables (str/join ", " (for [[alias table] (:table-aliases r)] 
                                (str table " " alias)))
        where-exprs (keep (fn [[tag x]] (constraint-to-sql tag x))
                      (:constraints r))
        sql (str "SELECT " cols " FROM " tables)
        sql (if (seq where-exprs) 
              (str sql " WHERE " (str/join " AND " where-exprs))
              sql)]
    sql))