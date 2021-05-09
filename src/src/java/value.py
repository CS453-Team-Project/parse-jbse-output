from abc import ABC
from dataclasses import dataclass
from typing import Any, Optional
import re


from .type import *
from ..jbse.symbol import JBSESymbol
from ..jbse.symbol_manager import symmgr


class JavaValue(ABC):
    @staticmethod
    def parse(string: str, type_desc: Optional[str] = None):
        for c in [
            JavaValueSymbolic,
            JavaValueSimple,
            JavaValueFromHeap,
            JavaValueSubscript,
            JavaValueSubscriptUnderscore,
            JavaValueUnknown,
        ]:
            parsed = c.parse(string, type_desc)
            if parsed is not None:
                return parsed

        raise ValueError("Invalid input")


@dataclass
class JavaValueSymbolic(JavaValue):
    symbol: JBSESymbol

    @staticmethod
    def parse(string: str, type_desc: Optional[str] = None):
        try:
            return JavaValueSymbolic(symmgr.get_parse(string))
        except:
            return None


@dataclass
class JavaValueSimple(JavaValue):
    type_desc: Optional[str]
    value: Any

    @staticmethod
    def parse(string: str, type_desc: Optional[str] = None):
        # TODO: object, NaN and ±Infinities are not implemented
        # null
        if type_desc not in list("ZBDFICJ") and string == "null":
            # FIXME: type? value?
            return JavaValueSimple(JavaTypeClass(type_desc or "java/lang/Object"), None)
        # boolean
        if (type_desc in ["Z", None]) and (string in ["true", "false"]) is not None:
            return JavaValueSimple(JavaTypeBoolean(), string == "true")
        # byte
        if (type_desc in ["B", None]) and (
            type_descmatched := re.search("^\(byte\) (-?(\d+))$", string)
        ) is not None:
            return JavaValueSimple(JavaTypeByte(), int(matched.group(1)))
        # double
        if (type_desc in ["D", None]) and (
            matched := re.search("^(-?(\d+)(.(\d*))?)d$", string)
        ) is not None:
            return JavaValueSimple(JavaTypeDouble(), float(matched.group(1)))
        # float
        if (type_desc in ["F", None]) and (
            matched := re.search("^(-?(\d+)(.(\d*))?)f$", string)
        ) is not None:
            return JavaValueSimple(JavaTypeFloat(), float(matched.group(1)))
        # int
        if (type_desc in ["I", None]) and (
            matched := re.search("^(-?(\d+))$", string)
        ) is not None:
            return JavaValueSimple(JavaTypeInt(), int(matched.group(1)))
        # char
        if (type_desc in ["C", None]) and (
            matched := re.search("^(.)$", string)
        ) is not None:
            return JavaValueSimple(JavaTypeChar(), int(matched.group(1)))
        # long
        if (type_desc in ["J", None]) and (
            matched := re.search("^(-?(\d+))L$", string)
        ) is not None:
            return JavaValueSimple((JavaTypeLong()), int(matched.group(1)))

        return None


@dataclass
class JavaValueFromHeap(JavaValue):
    index: int

    @staticmethod
    def parse(string: str, type_desc: Optional[str] = None):
        matched = re.search(r"^Object\[(\d+)\]$", string)
        if matched is not None:
            return JavaValueFromHeap(int(matched.group(1)))

        return None


@dataclass
class JavaValueSubscript(JavaValue):
    operand: JavaValue
    index: JavaValue

    @staticmethod
    def parse(string: str, type_desc: Optional[str] = None):
        matched = re.search(r"^([^\[]*?)\s*\[\s*(.*)\s*\]$", string)
        if matched is not None and matched.group(1) != "Object":
            operand = JavaValue.parse(matched.group(1))
            index = JavaValue.parse(matched.group(2))
            if operand is not None and index is not None:
                return JavaValueSubscript(operand, index)

        return None


@dataclass
class JavaValueSubscriptUnderscore(JavaValue):
    operand: JavaValue
    index: str

    @staticmethod
    def parse(string: str, type_desc: Optional[str] = None):
        matched = re.search(r"^(.*)\s*\[(([^\]]*?)\b_\b([^\]]*?))\]$", string)
        if matched is not None and matched.group(1) != "Object":
            operand = JavaValue.parse(matched.group(1))
            if operand is not None:
                return JavaValueSubscriptUnderscore(operand, matched.group(2))

        return None


@dataclass
class JavaValueUnknown(JavaValue):
    string: str

    # TODO: reduce the range of unknown

    @staticmethod
    def parse(string: str, type_desc: Optional[str] = None):
        return JavaValueUnknown(string)
