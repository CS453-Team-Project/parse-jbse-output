from abc import ABC
from dataclasses import dataclass
from typing import Any, Optional
import re

from .type import *
from ..jbse.symbol import JBSESymbol
from ..jbse.symbol_manager import JBSESymbolManager


class JavaValue(ABC):
    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str, type_desc: Optional[str] = None):
        for c in [
            JavaValueSymbolic,
            JavaValueSimple,
            JavaValueFromHeap,
            JavaValueSubscript,
            JavaValueSubscriptUnderscore,
            JavaValueUnknown,
        ]:
            parsed = c.parse(symmgr, string, type_desc)
            if parsed is not None:
                return parsed

        raise ValueError("Invalid input")


@dataclass
class JavaValueSymbolic(JavaValue):
    symbol: JBSESymbol

    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str, type_desc: Optional[str] = None):
        pattern = r"== Object\[\d+\]$"
        matched = re.search(pattern, string)
        if matched is not None:
            string = re.sub(pattern, "", string).strip()

            try:
                return JavaValueSymbolic(symmgr.get_parse(string))
            except:
                pass

        try:
            return JavaValueSymbolic(symmgr.get_parse(string))
        except:
            return None


@dataclass
class JavaValueSimple(JavaValue):
    type_desc: Optional[JavaType]
    value: Any

    def unparse(self) -> str:
        """Reverse of `parse`."""
        if self.value is None:
            return "null"

        if self.type_desc == JavaTypeBoolean():
            return "true" if self.value else "false"

        if self.type_desc == JavaTypeByte():
            return f"(byte) {self.value}"

        if self.type_desc == JavaTypeDouble():
            return f"{self.value}d"

        if self.type_desc == JavaTypeFloat():
            return f"{self.value}f"

        if self.type_desc == JavaTypeInt():
            return f"{self.value}"

        if self.type_desc == JavaTypeLong():
            return f"{self.value}L"

        if self.type_desc == JavaTypeChar():
            return "\\u0000" if self.value == 0 else chr(self.value)


    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str, type_desc: Optional[str] = None):
        # TODO: object, NaN and ±∞ are not implemented
        # null
        if type_desc not in list("ZBDFSICJ") and string == "null":
            # FIXME: type? value?
            return JavaValueSimple(
                JavaType.parse(type_desc)
                if type_desc is not None
                else JavaTypeClass("java/lang/Object"),
                None,
            )
        # boolean
        if (type_desc in ["Z", None]) and (string in ["true", "false"]):
            return JavaValueSimple(JavaTypeBoolean(), string == "true")
        # byte
        if (type_desc in ["B", None]) and (
            matched := re.search(r"^\(byte\) (-?(\d+))$", string)
        ) is not None:
            return JavaValueSimple(JavaTypeByte(), int(matched.group(1)))
        # double
        if (type_desc in ["D", None]) and (
            matched := re.search(r"^(-?(\d+)(.(\d*))?)d$", string)
        ) is not None:
            return JavaValueSimple(JavaTypeDouble(), float(matched.group(1)))
        # float
        if (type_desc in ["F", None]) and (
            matched := re.search(r"^(-?(\d+)(.(\d*))?)f$", string)
        ) is not None:
            return JavaValueSimple(JavaTypeFloat(), float(matched.group(1)))
        # int
        if (type_desc in ["I", None]) and (
            matched := re.search(r"^(-?(\d+))$", string)
        ) is not None:
            return JavaValueSimple(JavaTypeInt(), int(matched.group(1)))
        # char
        if (type_desc in ["C", None]) and (
            matched := re.search(r"^(\\u0000|.)$", string)
        ) is not None:
            return JavaValueSimple(
                JavaTypeChar(), 0 if string == "\\u0000" else ord(matched.group(1))
            )
        # long
        if (type_desc in ["J", None]) and (
            matched := re.search(r"^(-?(\d+))L$", string)
        ) is not None:
            return JavaValueSimple((JavaTypeLong()), int(matched.group(1)))
        # XXX: short is not implemented

        return None


@dataclass
class JavaValueFromHeap(JavaValue):
    index: int

    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str, type_desc: Optional[str] = None):
        matched = re.search(r"^Object\[(\d+)\]$", string)
        if matched is not None:
            return JavaValueFromHeap(int(matched.group(1)))

        return None


@dataclass
class JavaValueSubscript(JavaValue):
    operand: JavaValue
    index: JavaValue

    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str, type_desc: Optional[str] = None):
        matched = re.search(r"^([^\[]*?)\s*\[\s*(.*)\s*\]$", string)
        if matched is not None and matched.group(1) != "Object":
            operand = JavaValue.parse(symmgr, matched.group(1))
            index = JavaValue.parse(symmgr, matched.group(2))
            if operand is not None and index is not None:
                return JavaValueSubscript(operand, index)

        return None


@dataclass
class JavaValueSubscriptUnderscore(JavaValue):
    operand: JavaValue
    index: str

    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str, type_desc: Optional[str] = None):
        matched = re.search(r"^(.*)\s*\[(([^\]]*?)\b_\b([^\]]*?))\]$", string)
        if matched is not None and matched.group(1) != "Object":
            operand = JavaValue.parse(symmgr, matched.group(1))
            if operand is not None:
                return JavaValueSubscriptUnderscore(operand, matched.group(2))

        return None


@dataclass
class JavaValueUnknown(JavaValue):
    string: str

    # TODO: reduce the range of unknown

    @staticmethod
    def parse(symmgr: JBSESymbolManager, string: str, type_desc: Optional[str] = None):
        return JavaValueUnknown(string)
