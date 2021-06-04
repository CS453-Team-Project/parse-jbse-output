# parse-jbse-output

Python scripts to parse a JBSE output.


```sh
$ python src/main.py -a parse -p examples/1 -m 0 -f "path3.txt"
s.value[0] = (char)65495 && s.value.length = 1073741824;
s.value[0] = (char)0 && s.value.length = 1;
s.value[0] = (char)1 && s.value.length = 3;
s.value[0] = (char)1 && s.value.length = 1048579;
s.value[0] = (char)1 && s.value.length = 34603011;
s.value[0] = (char)1 && s.value.length = 34603139;
s.value[0] = (char)1 && s.value.length = 101712003;
s.value[0] = (char)1 && s.value.length = 101777539;
s.value[0] = (char)1 && s.value.length = 103874691;
s.value[0] = (char)1 && s.value.length = 103874707;
```

```sh
python src/main.py -v -a parse -p examples/1 -m 0 -f "path4.txt"
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
* Java test code generation?

