from abc import ABC, abstractmethod


class JavaType(ABC):
    # TODO: static method parse
    pass


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
    def __init__(self, type_desc: JavaType):
        self.type_desc = type_desc

    def __repr__(self):
        return f"[{repr(self.type_desc)}"
