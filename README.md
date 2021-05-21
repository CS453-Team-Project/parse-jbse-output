# parse-jbse-output

Python scripts to parse a JBSE output.


```sh
$ python src/main.py -t examples/1/path2.txt -m "com/cs453/group5/examples/Calculator:getLength:(Ljava/lang/String;)I:s"
Concatenation of all clauses:
And(0 <= {V3}, Not({V3} <= 0), Not({V6} == 40))

Simplification using ctx-solver-simplify:
[[Not({V3} <= 0), Not({V6} == 40)]]

In Java syntax:
And(0 <= {V3}, Not({V3} <= 0), Not({V6} == 40)) --->
 ((0<=s.value.length)&&(!(s.value.length<=0))&&(!(s.value[0]==(char)40)))

Models:
Model 0 ==========================================
([{V6} = 65495, {V3} = 1073741824], [])
Model 1 ==========================================
([{V6} = 0, {V3} = 1], [])
Model 2 ==========================================
([{V6} = 1, {V3} = 3], [])
Model 3 ==========================================
([{V6} = 1, {V3} = 1048579], [])
Model 4 ==========================================
([{V6} = 1, {V3} = 34603011], [])
Model 5 ==========================================
([{V6} = 1, {V3} = 34603139], [])
Model 6 ==========================================
([{V6} = 1, {V3} = 101712003], [])
Model 7 ==========================================
([{V6} = 1, {V3} = 101777539], [])
Model 8 ==========================================
([{V6} = 1, {V3} = 103874691], [])
Model 9 ==========================================
([{V6} = 1, {V3} = 103874707], [])
```


## TODO

* Parse returned value and raised exceptions
