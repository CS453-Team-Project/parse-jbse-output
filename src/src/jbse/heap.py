from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Any, Tuple, Union, Optional
import re

from ..java.value import JavaValue
from ..java.type import JavaType
from .symbol import JBSESymbol


class JBSEHeapValue(ABC):
    @staticmethod
    def parse(string: str):
        for c in [
            JBSEHeapValueClass,
            JBSEHeapValueArray,
        ]:
            parsed = c.parse(string)
            if parsed is not None:
                return parsed

        raise ValueError("Invalid input")


class JBSEHeapValueArrayItem:
    def __init__(
        self,
        index: int,
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
    def parse(string: str) -> list:
        """
        Typical form of input will be
        `Object[1895], Object[1895], Object[2027], null, null, null, null, null, null, null`
        or
        `({INDEX-1591058047}) >= (0) && ({INDEX-1591058047}) < ({V2}) && ({INDEX-1591058047}) == (0) -> {V5}`
        """

        if re.search("^\(no assumption on (other )?values\)$", string):
            return None

        if " -> " not in string:
            # Object[1895], Object[1895], Object[2027], null, null, null, ...
            return [
                JBSEHeapValueArrayItem(i, JavaValue.parse(s.strip()))
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
            return [JBSEHeapValueArrayItem(index, JavaValue.parse(value))]

        # <misc assumptions> -> ???
        # if ??? is of the form Object[<heap pos>][some lambda]
        matched = re.search(r"Object\[(\d+)\]\[((.*?)_(.*?))\]$", value)
        if matched is not None:
            heap_pos = int(matched.group(1))
            return [JBSEHeapValueArrayItem(index, JavaValue.parse(value))]

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

    @staticmethod
    def parse(string: str):
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
        items = [
            a
            for item in items_str.split("\n")
            if (stripped := item.strip()) != ""
            if (array_item := JBSEHeapValueArrayItem.parse(stripped)) is not None
            for a in array_item
        ]

        origin_pattern = r"\t+Origin: (.*?)\s\n"
        matched = re.search(origin_pattern, string)
        origin = None if matched is None else origin_pattern.group(1)

        return JBSEHeapValueArray(
            index,
            origin,
            (int(type_desc_index), type_desc_name),
            JavaValue.parse(length),
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

    @staticmethod
    def parse(string: str):
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
            fields.append(
                JBSEHeapClassField(name, type_desc, JavaValue.parse(value, type_desc))
            )

        origin_pattern = r"\t+Origin: (.*?)\s\n"
        matched = re.search(origin_pattern, string)
        origin = None if matched is None else matched.group(1)

        return JBSEHeapValueClass(
            index, origin, (int(class_desc_index), class_desc_name), fields
        )