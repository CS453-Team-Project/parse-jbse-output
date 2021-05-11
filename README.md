# parse-jbse-output

Python scripts to parse a JBSE output.


```sh
$ python src/main.py -t "examples/5.txt" -m "com/cs453/group5/examples/Calculator:getSign:(J[CC)I:number:longs:b"
The path is satisfiable with the following model(s).
1. [{V7} = 65487,
 {V6} = 65487,
 {V1} = 65495,
 {V0} = 3,
 {V3} = 3]
2. [{V1} = 0, {V0} = 3, {V6} = 0, {V7} = 0, {V3} = 6]
3. [{V1} = 32768, {V0} = 3, {V6} = 1, {V7} = 1, {V3} = 6]
4. [{V1} = 32769, {V0} = 3, {V6} = 1, {V7} = 1, {V3} = 6]
```


## Current status

* Parse a JBSE path
    + Almost done. Supported fields are as follows:
        ```python
        @dataclass
        class JBSEPath:
            name: str
            ret_val: Optional[str]  # TODO: parse ret val
            symmap: dict[JBSESymbol, str]  # TODO: parse value type of symmap
            clauses: list[PathConditionClause]
            heap: dict[int, JBSEHeapValue]
            # static_store: TODO
            # stack: TODO
        ```
    + Refer to TODOs and FIXMEs in the source code.
* Generate satisfying model for the path condition: done.
* Linking Z3 variables to Java variables: TODO.
