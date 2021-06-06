# parse-jbse-output

Python scripts to parse a JBSE output.


```sh
$ python src/main.py -a parse -p examples/1 -m 0
[Path: path1.txt]
((0<=s.value.length)&&(s.value.length<=0))
[Path: path2.txt]
((0<=s.value.length)&&(!(s.value.length<=0))&&(s.value[0]==(char)40))
[Path: path3.txt]
((0<=s.value.length)&&(!(s.value.length<=0))&&(!(s.value[0]==(char)40)))
[Path: path4.txt]
(s == null)
```

```sh
$ python src/main.py -a parse -p examples/2 -m 0 -f path8.txt path2.txt path6.txt
[Path: path8.txt]
((!(10<=n))&&(1<=n)&&(1<=(-1+n))&&(1<=(-2+n))&&(1<=(-3+n))&&(1<=(-4+n))&&(1<=(-5+n))&&(1<=(-6+n))&&(!(1<=(-7+n))))
[Path: path2.txt]
((!(10<=n))&&(1<=n)&&(!(1<=(-1+n))))
[Path: path6.txt]
((!(10<=n))&&(1<=n)&&(1<=(-1+n))&&(1<=(-2+n))&&(1<=(-3+n))&&(1<=(-4+n))&&(!(1<=(-5+n))))
```

```sh
$ python src/main.py -a parse -p examples/2 -m 0 -f path8.txt path2.txt path6.txt -v
[Path: path8.txt]
Result of the path:
JBSEPathResultReturn(value=4294967275 + 4294967291*{V0})

Concatenation of all clauses:
And(Not(10 <= {V0}),
    1 <= {V0},
    1 <= 4294967295 + {V0},
    1 <= 4294967294 + {V0},
    1 <= 4294967293 + {V0},
    1 <= 4294967292 + {V0},
    1 <= 4294967291 + {V0},
    1 <= 4294967290 + {V0},
    Not(1 <= 4294967289 + {V0}))

Simplification using ctx-solver-simplify:
[[1 <= 4294967290 + {V0}, Not(1 <= 4294967289 + {V0})]]

Path condition in Java syntax:
And(Not(10 <= {V0}),
    1 <= {V0},
    1 <= 4294967295 + {V0},
    1 <= 4294967294 + {V0},
    1 <= 4294967293 + {V0},
    1 <= 4294967292 + {V0},
    1 <= 4294967291 + {V0},
    1 <= 4294967290 + {V0},
    Not(1 <= 4294967289 + {V0})) --->
    ((!(10<=n))&&(1<=n)&&(1<=(-1+n))&&(1<=(-2+n))&&(1<=(-3+n))&&(1<=(-4+n))&&(1<=(-5+n))&&(1<=(-6+n))&&(!(1<=(-7+n))))

Models:
Model 0:
    Assignments:
        n = 7;

[Path: path2.txt]
Result of the path:
JBSEPathResultReturn(value={V0})

Concatenation of all clauses:
And(Not(10 <= {V0}), 1 <= {V0}, Not(1 <= 4294967295 + {V0}))

Simplification using ctx-solver-simplify:
[[1 <= {V0}, Not(1 <= 4294967295 + {V0})]]

Path condition in Java syntax:
And(Not(10 <= {V0}), 1 <= {V0}, Not(1 <= 4294967295 + {V0})) --->
    ((!(10<=n))&&(1<=n)&&(!(1<=(-1+n))))

Models:
Model 0:
    Assignments:
        n = 1;

[Path: path6.txt]
Result of the path:
JBSEPathResultReturn(value=4294967286 + 4294967293*{V0})

Concatenation of all clauses:
And(Not(10 <= {V0}),
    1 <= {V0},
    1 <= 4294967295 + {V0},
    1 <= 4294967294 + {V0},
    1 <= 4294967293 + {V0},
    1 <= 4294967292 + {V0},
    Not(1 <= 4294967291 + {V0}))

Simplification using ctx-solver-simplify:
[[1 <= 4294967292 + {V0}, Not(1 <= 4294967291 + {V0})]]

Path condition in Java syntax:
And(Not(10 <= {V0}),
    1 <= {V0},
    1 <= 4294967295 + {V0},
    1 <= 4294967294 + {V0},
    1 <= 4294967293 + {V0},
    1 <= 4294967292 + {V0},
    Not(1 <= 4294967291 + {V0})) --->
    ((!(10<=n))&&(1<=n)&&(1<=(-1+n))&&(1<=(-2+n))&&(1<=(-3+n))&&(1<=(-4+n))&&(!(1<=(-5+n))))

Models:
Model 0:
    Assignments:
        n = 5;

```

```sh
$ python src/main.py -v -a kill -p examples/1 -m 0
[{'mutant_pathname': '.1.1.1[331]',
  'mutant_result': 'java/lang/StringIndexOutOfBoundsException',
  'origin_pathname': '.1.2[2]',
  'origin_result': 'java/lang/NullPointerException',
  'path_condition': '((0<=s.value.length)&&(s.value.length<=0))'},
 {'mutant_pathname': '.1.1.2.1[7]',
  'mutant_result': 'JBSEPathResultReturn(value=s.value.length)',
  'origin_pathname': '.1.1.2.2[2]',
  'origin_result': 'JBSEPathResultReturn(value=-2)',
  'path_condition': '((0<=s.value.length)&&(!(s.value.length<=0))&&(s.value[0]==(char)40)&&(!(s.value.length==-2)))'},
 {'mutant_pathname': '.1.1.2.1[7]',
  'mutant_result': 'JBSEPathResultReturn(value=s.value.length)',
  'origin_pathname': '.1.2[2]',
  'origin_result': 'java/lang/NullPointerException',
  'path_condition': '((0<=s.value.length)&&(!(s.value.length<=0))&&(s.value[0]==(char)40))'},
 {'mutant_pathname': '.1.1.2.2[2]',
  'mutant_result': 'JBSEPathResultReturn(value=-2)',
  'origin_pathname': '.1.1.2.1[7]',
  'origin_result': 'JBSEPathResultReturn(value=s.value.length)',
  'path_condition': '((0<=s.value.length)&&(!(s.value.length<=0))&&(!(s.value[0]==(char)40))&&(!(s.value.length==-2)))'},
 {'mutant_pathname': '.1.1.2.2[2]',
  'mutant_result': 'JBSEPathResultReturn(value=-2)',
  'origin_pathname': '.1.2[2]',
  'origin_result': 'java/lang/NullPointerException',
  'path_condition': '((0<=s.value.length)&&(!(s.value.length<=0))&&(!(s.value[0]==(char)40)))'},
 {'mutant_pathname': '.1.2[2]',
  'mutant_result': 'java/lang/NullPointerException',
  'origin_pathname': '.1.1.1[331]',
  'origin_result': 'java/lang/StringIndexOutOfBoundsException',
  'path_condition': '((0<=s.value.length)&&(s.value.length<=0))'},
 {'mutant_pathname': '.1.2[2]',
  'mutant_result': 'java/lang/NullPointerException',
  'origin_pathname': '.1.1.2.1[7]',
  'origin_result': 'JBSEPathResultReturn(value=s.value.length)',
  'path_condition': '((0<=s.value.length)&&(!(s.value.length<=0))&&(!(s.value[0]==(char)40)))'},
 {'mutant_pathname': '.1.2[2]',
  'mutant_result': 'java/lang/NullPointerException',
  'origin_pathname': '.1.1.2.2[2]',
  'origin_result': 'JBSEPathResultReturn(value=-2)',
  'path_condition': '((0<=s.value.length)&&(!(s.value.length<=0))&&(s.value[0]==(char)40))'}]
[]
```

# TODO
* Additional assumption clauses
    + Length of String instances
    + Length of array primitives
* Java test code generation?

