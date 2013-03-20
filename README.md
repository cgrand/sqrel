# sqrel

The Clojure SQL library that won't drive you nuts.

## Usage

Alpha subject to changes. See the tests http://github.com/cgrand/sqrel/blob/master/test/net/cgrand/sqrel/test.clj

```clojure
=> (let [colleague (maybe (another employee))]
     (select {:dept (:name dept)
              :employees (many {:name (:name employee)
                                :colleagues (many (:name colleague))})}
       (eq (:dept-id employee) (:id dept) (:dept-id colleague))
       (neq (:id employee) (:id colleague))))
({:dept "Maintenance",
  :employees #{{:name "Homer Simpson", :colleagues #{}}}}
 {:dept "Sales",
  :employees #{{:name "Jane Doe", :colleagues #{"John Doe"}}
               {:name "John Doe", :colleagues #{"Jane Doe"}}}}))

=> (let [colleague (maybe (another employee))]
     (sql (collect {:dept (:name dept)
                    :employees (many {:name (:name employee)
                                      :colleagues (many (:name colleague))})}
            (eq (:dept-id employee) (:id dept) (:dept-id colleague))
            (neq (:id employee) (:id colleague)))))
"SELECT dept.name, employee.name, employee27734.name 
 FROM (dept dept JOIN employee employee ON employee.dept_id=dept.id) 
      LEFT JOIN (employee employee27734) ON (employee27734.id!=employee.id) AND employee27734.dept_id=dept.id 
 ORDER BY dept.name"
```

## License

Copyright © 2013 FIXME

Distributed under the Eclipse Public License, the same as Clojure.
