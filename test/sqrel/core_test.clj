(ns sqrel.core-test
  (:use clojure.test
    sqrel.core)
  (:require [clojure.java.jdbc :as sql]))

(defmacro with-tmp-db [& body]
  `(sql/with-connection {:classname "org.h2.Driver"
                         :subprotocol "h2"
                         :subname "mem:foo"}
     ~@body))

(defn setup []
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





