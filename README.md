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

