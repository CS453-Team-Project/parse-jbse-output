# parse-jbse-output

Python scripts to parse a JBSE output.


```sh
$ python src/main.py
JBSEPATH(
    name='.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.39[3980]'
    ret_val=None
    symmap={
        {R0}: {ROOT}:this
        {V0}: {ROOT}:number
        {R1}: {ROOT}:longs
        {V2}: {ROOT}:longs.length
        {V5}: {ROOT}:longs[0]
        {V6}: {ROOT}:longs[1]
        {V7}: {ROOT}:longs[2]
    }
    clauses=[
        {R0} == Object[4326] (fresh),
        ({V0}) < (4),
        (0) < ({V0}),
        {R1} == Object[4329] (fresh),
        ({V2}) >= (0),
        (0) < ({V2}),
        ({V5}) >= (-128),
        ({V5}) <= (127),
        ({V5}) + (128) == (0),
        (1) < ({V0}),
        (1) < ({V2}),
        ({V6}) >= (-128),
        ({V6}) <= (127),
        ({V6}) + (128) == (0),
        (2) < ({V0}),
        (2) < ({V2}),
        ({V7}) >= (-128),
        ({V7}) <= (127),
        ({V7}) + (128) == (132)
    ]
    heap={
        1895: JBSEHeapValueClass(
            index=1895
            origin=None
            class_desc=(0, 'java/lang/Integer')
            fields=[
                JBSEHeapClassField(name='value', type_desc='I', value=JavaValueSimple(type_desc=I, value=-128))
            ]
        )
        2027: JBSEHeapValueClass(
            index=2027
            origin=None
            class_desc=(0, 'java/lang/Integer')
            fields=[
                JBSEHeapClassField(name='value', type_desc='I', value=JavaValueSimple(type_desc=I, value=4))
            ]
        )
        4326: JBSEHeapValueClass(
            index=4326
            origin=None
            class_desc=(2, 'com/cs453/group5/examples/Calculator')
            fields=[
                
            ]
        )
        4327: JBSEHeapValueClass(
            index=4327
            origin=None
            class_desc=(0, 'java/util/ArrayList')
            fields=[
                JBSEHeapClassField(name='modCount', type_desc='I', value=JavaValueSimple(type_desc=I, value=3)),
                JBSEHeapClassField(name='elementData', type_desc='[Ljava/lang/Object;', value=JavaValueFromHeap(index=4330)),
                JBSEHeapClassField(name='size', type_desc='I', value=JavaValueSimple(type_desc=I, value=3))
            ]
        )
        4328: JBSEHeapValueArray(
            index=4328
            origin=None
            type_desc=(0, '[I')
            length=JavaValueSymbolic(symbol={V2})
            items=[
                JBSEHeapValueArrayItem(
                    index=0
                    value=JavaValueSymbolic(symbol={V5})
                ),
                JBSEHeapValueArrayItem(
                    index=1
                    value=JavaValueSymbolic(symbol={V6})
                ),
                JBSEHeapValueArrayItem(
                    index=2
                    value=JavaValueSymbolic(symbol={V7})
                )
            ]
        )
        4329: JBSEHeapValueArray(
            index=4329
            origin=None
            type_desc=(0, '[I')
            length=JavaValueSymbolic(symbol={V2})
            items=[
                JBSEHeapValueArrayItem(
                    index=None
                    value=JavaValueSubscriptUnderscore(operand=JavaValueFromHeap(index=4328), index='_ + 0')
                )
            ]
        )
        4330: JBSEHeapValueArray(
            index=4330
            origin=None
            type_desc=(0, '[Ljava/lang/Object;')
            length=JavaValueSimple(type_desc=I, value=10)
            items=[
                JBSEHeapValueArrayItem(
                    index=0
                    value=JavaValueFromHeap(index=1895)
                ),
                JBSEHeapValueArrayItem(
                    index=1
                    value=JavaValueFromHeap(index=1895)
                ),
                JBSEHeapValueArrayItem(
                    index=2
                    value=JavaValueFromHeap(index=2027)
                ),
                JBSEHeapValueArrayItem(
                    index=3
                    value=JavaValueSimple(type_desc=Ljava/lang/Object;, value=None)
                ),
                JBSEHeapValueArrayItem(
                    index=4
                    value=JavaValueSimple(type_desc=Ljava/lang/Object;, value=None)
                ),
                JBSEHeapValueArrayItem(
                    index=5
                    value=JavaValueSimple(type_desc=Ljava/lang/Object;, value=None)
                ),
                JBSEHeapValueArrayItem(
                    index=6
                    value=JavaValueSimple(type_desc=Ljava/lang/Object;, value=None)
                ),
                JBSEHeapValueArrayItem(
                    index=7
                    value=JavaValueSimple(type_desc=Ljava/lang/Object;, value=None)
                ),
                JBSEHeapValueArrayItem(
                    index=8
                    value=JavaValueSimple(type_desc=Ljava/lang/Object;, value=None)
                ),
                JBSEHeapValueArrayItem(
                    index=9
                    value=JavaValueSimple(type_desc=Ljava/lang/Object;, value=None)
                )
            ]
        )
    }
)
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


