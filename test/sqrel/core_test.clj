(ns sqrel.core-test
  (:use clojure.test
    net.cgrand.sqrel
    [net.cgrand.replay :only [replay]])
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

;; the #1 asbtraction is the rel. #'table returns rels.
(def employee (table "employee"))
(def dept (table "dept"))

(replay basic-select :wrap-with with-tmp-db :before (setup)
^:eg => (sql (eq (:id dept) 42))
"SELECT * FROM dept dept WHERE 42=dept.id"

^:eg => (sql (eq (:dept_id employee) (:id dept)))
"SELECT * FROM employee employee, dept dept WHERE employee.dept_id=dept.id"

=> (select (eq (:id dept) 2))
({:id 2, :name "Maintenance"}))

;; (:id dept) is also a rel
;; #'eq returns rels too
(def dept42 (eq (:id dept) 42))
(def employee+dept (eq (:dept_id employee) (:id dept)))

(replay test-rel :wrap-with with-tmp-db :before (setup)
;; #'rel merges rels together
^:eg => (sql (rel dept42 employee+dept))
"SELECT * FROM dept dept, employee employee WHERE 42=employee.dept_id AND 42=dept.id"

;; as the (:colname relation) forms have hinted to, rels are lookup-able and support #'get (and can laso be used as functions)
^:eg => (sql (employee+dept {:name (:name employee)}))
"SELECT employee.name FROM employee employee, dept dept WHERE employee.dept_id=dept.id"

^:eg => (sql (get (rel dept42 employee+dept) {:name (:name employee)}))
"SELECT employee.name FROM dept dept, employee employee WHERE 42=employee.dept_id AND 42=dept.id"

^:eg => (sql (get (rel dept42 employee+dept) {:name (:name employee) 
                                         :dname (:name dept)}))
"SELECT employee.name, dept.name FROM dept dept, employee employee WHERE 42=employee.dept_id AND 42=dept.id"

;; (select expr rel1 .. relN) is a short-hand for (select (project expr rel1 .. relN))
;;
;; expr can be a vector and the resulting sequence is then made of vectors
^:nd => (select [(:name dept) (:name employee)]
     (eq (:dept-id employee) (:id dept)))
(["Sales" "John Doe"] ["Sales" "Jane Doe"] ["Maintenance" "Homer Simpson"])

;; expr can be a map and the resulting sequence is then made of maps
^:nd => (select {:dept (:name dept) :employee (:name employee)}
     (eq (:dept-id employee) (:id dept)))
({:employee "John Doe", :dept "Sales"} {:employee "Jane Doe", :dept "Sales"} {:employee "Homer Simpson", :dept "Maintenance"})

;; expr can be a set and the resulting sequence is then made of maps whose keys are fields (i.e. the rels of the original set)
=> (select (get (eq (:dept-id employee) (:id dept))
             #{(:name dept) (:name employee)}))
; ({#<SQRel "employee.name"> "John Doe", #<SQRel "dept.name"> "Sales"} {#<SQRel "employee.name"> "Jane Doe", #<SQRel "dept.name"> "Sales"} {#<SQRel "employee.name"> "Homer Simpson", #<SQRel "dept.name"> "Maintenance"})

;; and yes, maps keys are the columns rels themselves!
^:nd => (map #(get % (:name employee)) *1)
("John Doe" "Jane Doe" "Homer Simpson")

;; and now let's aggregate!
^:nd => (select {:dept (:name dept) 
            :employees (many (:name employee))}
     (eq (:dept-id employee) (:id dept)))
({:dept "Maintenance", :employees #{"Homer Simpson"}}
 {:dept "Sales", :employees #{"Jane Doe" "John Doe"}})

;; and the SQL for this was:
^:eg => (sql (project {:dept (:name dept) 
                  :employees (many (:name employee))}
          (eq (:dept-id employee) (:id dept))))
"SELECT dept.name, employee.name FROM dept dept, employee employee WHERE employee.dept_id=dept.id ORDER BY dept.name")
