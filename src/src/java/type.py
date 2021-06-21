from abc import ABC, abstractmethod
from typing import Optional, Sequence, Tuple
import re


class JavaType(ABC):
    @staticmethod
    def parse_method_signature(
        sig: str,
    ) -> Optional[Tuple[Sequence["JavaType"], "JavaType"]]:
        matched = re.match(r"\((.*)\)(.*)$", sig)
        if matched is None:
            return None

        param = JavaType.parse_multiple(matched.group(1))
        ret = JavaType.parse(matched.group(2))

        if param is None or ret is None:
            return None

        return param, ret

    @staticmethod
    def parse_multiple(type_desc: str) -> Optional[Sequence["JavaType"]]:
        if type_desc == "":
            return []

        type_desc_to_java_type = {
            "V": JavaTypeVoid,
            "Z": JavaTypeBoolean,
            "B": JavaTypeByte,
            "C": JavaTypeChar,
            "D": JavaTypeDouble,
            "F": JavaTypeFloat,
            "S": JavaTypeShort,
            "I": JavaTypeInt,
            "J": JavaTypeLong,
        }

        if type_desc[0] == "[":
            nested_count = len(re.match("^(\[+)", type_desc).group(1))

            matched = re.match(r"(V|Z|B|C|D|F|S|I|J|L(.*?);)", type_desc[nested_count:])
            if not matched:
                return None

            tail_call = JavaType.parse_multiple(
                type_desc[nested_count + len(matched.group(1)) :]
            )
            if tail_call is None:
                return None

            if matched.group(1)[0] != "L":
                t = type_desc_to_java_type[matched.group(1)]()
                for _ in range(nested_count):
                    t = JavaTypeArray(t)

                return [
                    t,
                    *tail_call,
                ]

            if matched.group(2) is None:
                return None

            t = JavaTypeClass(matched.group(2))
            for _ in range(nested_count):
                t = JavaTypeArray(t)

            return [t, *tail_call]

        matched = re.match(r"(V|Z|B|C|D|F|S|I|J|L(.*?);)", type_desc)
        if not matched:
            return None

        tail_call = JavaType.parse_multiple(type_desc[len(matched.group(1)) :])
        if tail_call is None:
            return None

        if matched.group(1)[0] != "L":
            return [type_desc_to_java_type[matched.group(1)](), *tail_call]

        if matched.group(2) is None:
            return None

        return [JavaTypeClass(matched.group(2)), *tail_call]

    @staticmethod
    def parse(type_desc: str) -> Optional["JavaType"]:
        return (
            None
            if (r := JavaType.parse_multiple(type_desc)) is None or len(r) != 1
            else r[0]
        )

    def __eq__(self, o):
        if type(self) in [
            JavaTypeVoid,
            JavaTypeBoolean,
            JavaTypeByte,
            JavaTypeChar,
            JavaTypeShort,
            JavaTypeInt,
            JavaTypeLong,
            JavaTypeFloat,
            JavaTypeDouble,
        ]:
            return type(self) == type(o)

        if type(self) == JavaTypeClass:
            return type(o) == JavaTypeClass and self.binary_name == o.binary_name

        if type(self) == JavaTypeArray:
            return type(o) == JavaTypeArray and self.inner == o.inner

        return False


class JavaTypeVoid(JavaType):
    def __repr__(self):
        return "V"

    def to_string(self):
        return "void"


class JavaTypeBoolean(JavaType):
    def __repr__(self):
        return "Z"

    def to_string(self):
        return "boolean"


class JavaTypeByte(JavaType):
    def __repr__(self):
        return "B"

    def to_string(self):
        return "byte"


class JavaTypeChar(JavaType):
    def __repr__(self):
        return "C"

    def to_string(self):
        return "char"


class JavaTypeDouble(JavaType):
    def __repr__(self):
        return "D"

    def to_string(self):
        return "double"


class JavaTypeFloat(JavaType):
    def __repr__(self):
        return "F"

    def to_string(self):
        return "float"


class JavaTypeShort(JavaType):
    def __repr__(self):
        return "S"

    def to_string(self):
        return "short"


class JavaTypeInt(JavaType):
    def __repr__(self):
        return "I"

    def to_string(self):
        return "int"


class JavaTypeLong(JavaType):
    def __repr__(self):
        return "J"

    def to_string(self):
        return "long"


class JavaTypeClass(JavaType):
    def __init__(self, binary_name: str):
        self.binary_name = binary_name

    def __repr__(self):
        return f"L{self.binary_name};"

    def to_string(self):
        return self.binary_name.replace("/", ".")


class JavaTypeArray(JavaType):
    def __init__(self, inner: JavaType):
        self.inner = inner

    def __repr__(self):
        return f"[{repr(self.inner)}"

    def to_string(self):
        return f"{self.inner.to_string()}[]"
