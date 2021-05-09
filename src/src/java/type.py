from abc import ABC, abstractmethod
from typing import Optional


class JavaType(ABC):
    @staticmethod
    def parse(type_desc: str) -> Optional["JavaType"]:
        # TODO: support multiple types?

        type_desc = type_desc.split(";")[0]

        if type_desc == "Z":
            return JavaTypeBoolean()
        if type_desc == "B":
            return JavaTypeByte()
        if type_desc == "C":
            return JavaTypeChar()
        if type_desc == "D":
            return JavaTypeDouble()
        if type_desc == "F":
            return JavaTypeFloat()
        if type_desc == "I":
            return JavaTypeInt()
        if type_desc == "J":
            return JavaTypeLong()
        # class
        if type_desc[0] == "L":
            return JavaTypeClass(type_desc[1:])
        # array
        if type_desc[0] == "[":
            return JavaTypeArray(JavaType.parse(type_desc[1:]))

    def __eq__(self, o):
        if type(self) in [JavaTypeBoolean, JavaTypeByte, JavaTypeChar, JavaTypeDouble, JavaTypeFloat, JavaTypeInt, JavaTypeLong]:
            return type(self) == type(o)

        if type(self) == JavaTypeClass:
            return type(o) == JavaTypeClass and self.binary_name == o.binary_name

        if type(self) == JavaTypeArray:
            return type(o) == JavaTypeArray and self.inner == o.inner

        return False
        


class JavaTypeBoolean(JavaType):
    def __repr__(self):
        return "Z"


class JavaTypeByte(JavaType):
    def __repr__(self):
        return "B"


class JavaTypeChar(JavaType):
    def __repr__(self):
        return "C"


class JavaTypeDouble(JavaType):
    def __repr__(self):
        return "D"


class JavaTypeFloat(JavaType):
    def __repr__(self):
        return "F"


class JavaTypeInt(JavaType):
    def __repr__(self):
        return "I"


class JavaTypeLong(JavaType):
    def __repr__(self):
        return "J"


class JavaTypeClass(JavaType):
    def __init__(self, binary_name: str):
        self.binary_name = binary_name

    def __repr__(self):
        return f"L{self.binary_name};"


class JavaTypeArray(JavaType):
    def __init__(self, inner: JavaType):
        self.inner = inner

    def __repr__(self):
        return f"[{repr(self.inner)}"
