# parse-jbse-output

Python scripts to parse a JBSE output.


```sh
$ python src/main.py -v -t examples/1/path2.txt -m "com/cs453/group5/examples/Calculator:getLength:(Ljava/lang/String;)I:s"
Concatenation of all clauses:
And(0 <= {V3}, Not({V3} <= 0), Not({V6} == 40))

Simplification using ctx-solver-simplify:
[[Not({V3} <= 0), Not({V6} == 40)]]

Path condition in Java syntax:
And(0 <= {V3}, Not({V3} <= 0), Not({V6} == 40)) --->
 ((0<=s.value.length)&&(!(s.value.length<=0))&&(!(s.value[0]==(char)40)))

Models:
Model 0:
    Assignments:
        s.value[0] = (char)65495; 
        s.value.length = 1073741824; 
Model 1:
    Assignments:
        s.value[0] = (char)0; 
        s.value.length = 1; 
Model 2:
    Assignments:
        s.value[0] = (char)1; 
        s.value.length = 3; 
Model 3:
    Assignments:
        s.value[0] = (char)1; 
        s.value.length = 1048579; 
Model 4:
    Assignments:
        s.value[0] = (char)1; 
        s.value.length = 34603011; 
Model 5:
    Assignments:
        s.value[0] = (char)1; 
        s.value.length = 34603139; 
Model 6:
    Assignments:
        s.value[0] = (char)1; 
        s.value.length = 101712003; 
Model 7:
    Assignments:
        s.value[0] = (char)1; 
        s.value.length = 101777539; 
Model 8:
    Assignments:
        s.value[0] = (char)1; 
        s.value.length = 103874691; 
Model 9:
    Assignments:
        s.value[0] = (char)1; 
        s.value.length = 103874707; 
```


## TODO

* Parse returned value and raised exceptions
