import json
import re
from typing import Tuple, Union

from src.java.type import JavaType


def inputs_to_junits(
    test_index: int,
    origin_pathname: str,
    origin_result_string: str,
    origin_result_description: str,
    mutant_index: int,
    mutant_pathname: str,
    mutant_result_description: str,
    inputs: list[dict[str, Tuple[Union[list, str], JavaType]]],
    methods: list[Tuple[str, str, dict, JavaType]],
) -> str:
    """
    inputs: list[dict[str, Tuple[T, JavaType]]] where
    T is defined as the following free monad:
        T = Union[str, list[T]]

    First, one needs to flatten the inputs into `list[dict[str, str]]`.
    Then, one needs to declare parameters
    """

    if inputs == []:
        return

    lines = []

    def flatten_input_value(val: Union[list, str]) -> str:
        if type(val) == str:
            return val

        return f"[{', '.join([flatten_input_value(item) for item in val])}]"

    binary_name, method_name, params, return_type = methods[0]
    binary_name = binary_name.replace("/", ".")
    basename = binary_name.split(".")[-1]

    origin_result_description = json.dumps(origin_result_description)[1:-1]
    mutant_result_description = json.dumps(mutant_result_description)[1:-1]

    # Test description
    lines.append("@Test")
    lines.append(
        f'@DisplayName("Original path {origin_pathname} ({origin_result_description})'
        f" <-> Mutant {mutant_index}'s path {mutant_pathname} ({mutant_result_description})\")"
    )

    lines.append(f"public void test{test_index}() {{")

    # XXX: assume that the class constructor takes no parameters
    # XXX: and every member variable of the class is public
    lines.append(f"    {binary_name} my{basename} = {binary_name}();\n")

    local_variables = list(inputs[0])
    local_variables.sort(key=lambda w: (0 if w.startswith("this.") else 1, w))

    # declare local variables first
    for var, (val, var_type) in inputs[0].items():
        lines.append(f"    {var_type.to_string()} {var};")

    for input in inputs:
        for var, (val, _) in input.items():
            lines.append(f"    {var} = {flatten_input_value(val)};")

        matched = re.match(
            r"^JBSEPathResultReturn\(value=(.*)\)$", origin_result_string
        )
        if matched and matched.group(1) != "null":
            lines.append(
                f"    assertEquals(my{basename}.{method_name}({', '.join(list(params))}), {matched.group(1)});"
            )
        else:
            matched = re.match(
                r"^JBSEPathResultException\(exception=(.*)\)$", origin_result_string
            )
            if matched:
                lines.append(
                    f"    assertThrows({matched.group(1)}.class, () -> {{ my{basename}.{method_name}({', '.join(list(params))}); }});"
                )

    lines.append(f"}}")

    return "\n".join(lines)
