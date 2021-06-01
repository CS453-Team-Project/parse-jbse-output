from abc import ABC, abstractmethod
from copy import deepcopy
from dataclasses import dataclass
from typing import Any, Tuple, Union, Optional, Literal, Sequence, Callable
import re

from ..java.value import JavaValue, JavaValueSimple, JavaValueSymbolic
from ..java.type import *
from .symbol import JBSESymbol
from .symbol_manager import JBSESymbolManager


class JBSEHeapValue(ABC):
    @staticmethod
    def parse(
        symmgr: JBSESymbolManager,
        string: str,
        symmap: dict[Sequence[Tuple[Optional[str], str]], JBSESymbol],
    ):
        for c in [
            JBSEHeapValueClass,
            JBSEHeapValueArray,
        ]:
            parsed = c.parse(symmgr, string, symmap)
            if parsed is not None:
                return parsed

        raise ValueError("Invalid input")


class JBSEHeapValueArrayItem:
    def __init__(
        self,
        index: Union[int, Callable[[int], int]],
        value: Union[JavaValue, Tuple[int, str]],
    ):
        self.index = index
        self.value = value

    def __repr__(self) -> str:
        return (
            "JBSEHeapValueArrayItem(\n"
            f"                    index={self.index}\n"
            f"                    value={repr(self.value)}\n"
            "                )"
        )

    @staticmethod
    def parse(
        symmgr: JBSESymbolManager, string: str, type_desc: Optional[str] = None
    ) -> list:
        """
        Typical form of input will be
        `"My string"`,
        `Object[1895], Object[1895], Object[2027], null, null, null, null, null, null, null`
        or
        `({INDEX-1591058047}) >= (0) && ({INDEX-1591058047}) < ({V2}) && ({INDEX-1591058047}) == (0) -> {V5}`
        """

        if re.search(r"^\(no assumption on (other )?values\)$", string):
            return None

        if re.search(r"^\"(.*)\"$", string):
            return [
                JBSEHeapValueArrayItem(i, JavaValueSimple("C", ord(c)))
                for (i, c) in enumerate(
                    string[1:-1].encode("utf8").decode("unicode_escape")
                )
            ]

        if " -> " not in string:
            # Object[1895], Object[1895], Object[2027], null, null, null, ...
            return [
                JBSEHeapValueArrayItem(i, JavaValue.parse(symmgr, s.strip(), type_desc))
                for (i, s) in enumerate(string.split(","))
            ]

        assumption, value = string.split(" -> ")[:2]

        # Split by &&
        index = next(
            (
                int(search.group(1))
                for entry in assumption.split(" && ")
                if (search := re.search(r"^\(\{INDEX-\d+\}\) == \((\d+)\)$", entry))
                is not None
            ),
            None,
        )
        if index is not None:
            # ({INDEX-??}) == (<index>) -> <value>
            return [
                JBSEHeapValueArrayItem(index, JavaValue.parse(symmgr, value, type_desc))
            ]

        # <misc assumptions> -> ???
        # if ??? is of the form Object[<heap pos>][some lambda]
        matched = re.search(r"Object\[(\d+)\]\[((.*?)_(.*?))\]$", value)
        if matched is not None:
            heap_pos = int(matched.group(1))
            return [
                JBSEHeapValueArrayItem(index, JavaValue.parse(symmgr, value, type_desc))
            ]

        raise ValueError("Not supported")


class JBSEHeapValueArray(JBSEHeapValue):
    def __init__(
        self,
        index: int,
        origin: str,
        type_desc: Tuple[int, JavaType],
        length: JBSESymbol,
        items: list[JBSEHeapValueArrayItem],
    ):
        self.index = index
        self.origin = origin
        self.type_desc = type_desc
        self.length = length
        self.items = items

    def __repr__(self) -> str:
        items_str = ",\n                ".join([repr(c) for c in self.items])
        return (
            "JBSEHeapValueArray(\n"
            f"            index={self.index}\n"
            f"            origin={repr(self.origin)}\n"
            f"            type_desc={self.type_desc}\n"
            f"            length={repr(self.length)}\n"
            f"            items=[\n                {items_str}\n            ]\n"
            "        )"
        )

    def __eq__(self, o):
        return type(o) == JBSEHeapValueArray and self.index == o.index

    @staticmethod
    def parse(
        symmgr: JBSESymbolManager,
        string: str,
        symmap: dict[Sequence[Tuple[Optional[str], str]], JBSESymbol],
    ):
        pattern = r"^Object\[(\d+)\]: \{(.|\r|\n)*\tType: \((\d+),(.*?)\)\s*\n\t+Length: (.*?)\s*\n\t+Items: \{((.|\r|\n)*)\}\n\t\}"
        matched = re.search(pattern, string)

        if matched is None:
            return None

        (
            index,
            _,
            type_desc_index,
            type_desc_name,
            length,
            items_str,
            _,
        ) = matched.groups()

        origin_pattern = r"\s+Origin: (.*?)\s*\n"
        matched = re.search(origin_pattern, string)
        origin = None if matched is None else matched.group(1)

        length = JavaValue.parse(symmgr, length)

        array_type = JavaType.parse(type_desc_name)
        assert type(array_type) == JavaTypeArray
        array_inner_type = array_type.inner

        items = [
            a
            for item in items_str.split("\n")
            if (stripped := item.lstrip()) != ""
            if (
                array_item := JBSEHeapValueArrayItem.parse(
                    symmgr, stripped, type_desc_name[1:]
                )
            )
            is not None
            for a in array_item
        ]

        # symbolic length
        if type(length) == JavaValueSymbolic:
            length.symbol.type = JavaTypeInt()

        # symbolic array items
        for item in items:
            if type(item.value) == JavaValueSymbolic:
                item.value.symbol.type = deepcopy(array_inner_type)

        return JBSEHeapValueArray(
            index,
            origin,
            (int(type_desc_index), array_type),
            length,
            items,
        )


@dataclass
class JBSEHeapClassField:
    name: str
    type_desc: str
    value: Any


class JBSEHeapValueClass(JBSEHeapValue):
    def __init__(
        self,
        index: int,
        origin: Optional[str],
        class_desc: Tuple[int, str],
        fields: list[JBSEHeapClassField],
    ):
        self.index = index
        self.origin = origin
        self.class_desc = class_desc
        self.fields = fields

    def __repr__(self) -> str:
        fields_str = ",\n                ".join([repr(c) for c in self.fields])
        return (
            "JBSEHeapValueClass(\n"
            f"            index={self.index}\n"
            f"            origin={repr(self.origin)}\n"
            f"            class_desc={self.class_desc}\n"
            f"            fields=[\n                {fields_str}\n            ]\n"
            "        )"
        )

    def __eq__(self, o):
        return type(o) == JBSEHeapValueClass and self.index == o.index

    @staticmethod
    def parse(
        symmgr: JBSESymbolManager,
        string: str,
        symmap: dict[Sequence[Tuple[Optional[str], str]], JBSESymbol],
    ):
        pattern = (
            r"^Object\[(\d+)\]: \{(.|\r|\n)*Class: \((\d+),(.*?)\)(.|\r|\n)*\n\t\}"
        )
        matched = re.search(pattern, string)

        if matched is None:
            return None

        index, _, class_desc_index, class_desc_name, _ = matched.groups()

        fields = []
        field_pattern = (
            r"\t+Field\[\d+]: Name: (.*?), Type: (.*?), Value: (.*?) \(type: .\)"
        )
        for name, type_desc, value in re.findall(field_pattern, string):
            field = JBSEHeapClassField(
                name, type_desc, JavaValue.parse(symmgr, value, type_desc)
            )
            if isinstance(field.value, JavaValueSymbolic):
                field.value.symbol.type = JavaType.parse(type_desc)

            fields.append(field)

        origin_pattern = r"\t+Origin: (.*?)\s*\n"
        matched = re.search(origin_pattern, string)
        origin = None if matched is None else matched.group(1)
        if origin is not None:
            origin = tuple(
                [
                    (a[0], a[1]) if len(a) >= 2 else (None, a[0])
                    for a in [s.split(":") for s in origin.split(".")]
                ]
            )

        if origin in symmap:
            symbol = symmap[origin]
            symbol.type = JavaTypeClass(class_desc_name)

        return JBSEHeapValueClass(
            index, origin, (int(class_desc_index), class_desc_name), fields
        )
