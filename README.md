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
[{'inputs': [{'s': ('"("', Ljava/lang/String;)},
             {'s': ('"(??"', Ljava/lang/String;)},
             {'s': ('"(?"', Ljava/lang/String;)},
             {'s': ('"(???"', Ljava/lang/String;)}],
  'mutant_pathname': '.1.1.2.1[7]',
  'mutant_result_description': 'returned s.value.length',
  'mutant_result_string': 'JBSEPathResultReturn(value=s.value.length)',
  'origin_pathname': '.1.1.2.2[2]',
  'origin_result_description': 'returned -2',
  'origin_result_string': 'JBSEPathResultReturn(value=-2)',
  'path_condition': '((0<=s.value.length)&&(!(s.value.length<=0))&&(s.value[0]==(char) '
                    '40)&&(!(s.value.length==-2)))'},
 {'inputs': [{'s': ('"\\u0000?"', Ljava/lang/String;)},
             {'s': ('"\\u0000"', Ljava/lang/String;)},
             {'s': ('"\\u0002"', Ljava/lang/String;)},
             {'s': ('"\\u0002?"', Ljava/lang/String;)}],
  'mutant_pathname': '.1.1.2.2[2]',
  'mutant_result_description': 'returned -2',
  'mutant_result_string': 'JBSEPathResultReturn(value=-2)',
  'origin_pathname': '.1.1.2.1[7]',
  'origin_result_description': 'returned s.value.length',
  'origin_result_string': 'JBSEPathResultReturn(value=s.value.length)',
  'path_condition': '((0<=s.value.length)&&(!(s.value.length<=0))&&(!(s.value[0]==(char) '
                    '40))&&(!(s.value.length==-2)))'}]
[]

JUnit tests:

@Test
@DisplayName("Original path .1.1.2.2[2] (returned -2) <-> Mutant 0's path .1.1.2.1[7] (returned s.value.length)")
public void test0() {
    com.cs453.group5.examples.Calculator myCalculator = com.cs453.group5.examples.Calculator();

    java.lang.String s;
    s = "(";
    assertEquals(myCalculator.getLength(s), -2);
    s = "(??";
    assertEquals(myCalculator.getLength(s), -2);
    s = "(?";
    assertEquals(myCalculator.getLength(s), -2);
    s = "(???";
    assertEquals(myCalculator.getLength(s), -2);
}

@Test
@DisplayName("Original path .1.1.2.1[7] (returned s.value.length) <-> Mutant 0's path .1.1.2.2[2] (returned -2)")
public void test1() {
    com.cs453.group5.examples.Calculator myCalculator = com.cs453.group5.examples.Calculator();

    java.lang.String s;
    s = "\u0000?";
    assertEquals(myCalculator.getLength(s), s.value.length);
    s = "\u0000";
    assertEquals(myCalculator.getLength(s), s.value.length);
    s = "\u0002";
    assertEquals(myCalculator.getLength(s), s.value.length);
    s = "\u0002?";
    assertEquals(myCalculator.getLength(s), s.value.length);
}
```

```sh
$ python src/main.py -a kill -p examples/6 -m 0
@Test
@DisplayName("Original path .1.1.1.1.1.1[5] (returned (3+this.a)) <-> Mutant 0's path .1.1.1.1.1.1[5] (returned (3+(-1*this.a)))")
public void test0() {
    com.cs453.group5.examples.Calculator myCalculator = com.cs453.group5.examples.Calculator();

    boolean[][] z;
    int this.a;

    z = [[true, false], []];
    this.a = 1073741824;
    assertEquals(myCalculator.arrarr(z), (3+this.a));

    z = [[true, false], [], []];
    this.a = 1073741824;
    assertEquals(myCalculator.arrarr(z), (3+this.a));

    z = [[true]];
    this.a = 1073741824;
    assertEquals(myCalculator.arrarr(z), (3+this.a));

    z = [[true, false, false], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []];
    this.a = 1073741824;
    assertEquals(myCalculator.arrarr(z), (3+this.a));
}
```
