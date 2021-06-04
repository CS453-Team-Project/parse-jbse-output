# parse-jbse-output

Python scripts to parse a JBSE output.


```sh
$ python src/main.py -a parse -p examples/1 -m 0 -f "path3.txt"
((0<=s.value.length)&&(!(s.value.length<=0))&&(!(s.value[0]==(char)40)))
```

```sh
$ python src/main.py -v -a parse -p examples/1 -m 0 -f "path4.txt"
Concatenation of all clauses:
True

Simplification using ctx-solver-simplify:
[[]]

Path condition in Java syntax:
True --->
    true

Models:
Model 0:
    Assignments:
        s == null;
```

# TODO
* Additional assumption clauses
    + Length of String instances
    + Length of array primitives
* Java test code generation?

