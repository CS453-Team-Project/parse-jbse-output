from array import ArrayType
import json
import re
from typing import Tuple, Sequence, Union

import z3
from src.java.type import (
    JavaType,
    JavaTypeArray,
    JavaTypeBoolean,
    JavaTypeByte,
    JavaTypeChar,
    JavaTypeClass,
    JavaTypeDouble,
    JavaTypeInt,
    JavaTypeLong,
)
from src.util.arg import parse_method
from src.util.z3_to_java import z3_to_java_without_symmap
from src.jbse.path import JBSEPath, JBSEPathAux, JBSEPathResultReturn
from src.jbse.path_condition import (
    PathConditionClauseAssumeNull,
)
from src.jbse.symbol import JBSESymbol, JBSESymbolRef
from src.util.arg import parse_method
from src.util.math import get_n_models

from src.util.z3_to_java import (
    z3_to_java_without_symmap,
    z3_traverse_unparse_symbol,
)


class KillConditionFinder:
    def __init__(
        self,
        origin_paths: Sequence[str],
        mutant_paths: Sequence[str],
        methods: Sequence[str],
        num_models: int,
    ):
        self.methods = [parse_method(method) for method in methods]
        self.num_models = num_models

        self.origin_paths: list[JBSEPath] = [
            JBSEPath.parse(target_path, JBSEPathAux(self.methods))
            for target_path in origin_paths
        ]
        self.mutant_paths: list[JBSEPath] = [
            JBSEPath.parse(target_path, JBSEPathAux(self.methods))
            for target_path in mutant_paths
        ]
        self.kill_conditions = list()
        self.unknown_conditions = list()

    def find_kill(self):
        for mutant_path in self.mutant_paths:
            for origin_path in self.origin_paths:
                # Check null references
                def get_null_refs(path: JBSEPath) -> Sequence[str]:
                    result = [
                        (
                            next(
                                (
                                    ".".join(name for _, name in key)
                                    for key, symbol in path.symmap.items()
                                    if symbol == clause.sym_ref
                                ),
                                None,
                            )
                        )
                        for clause in path.clauses
                        if type(clause) == PathConditionClauseAssumeNull
                    ]
                    result = [item for item in result if item is not None]
                    return set(result)

                origin_null_refs = get_null_refs(origin_path)
                mutant_null_refs = get_null_refs(mutant_path)
                if origin_null_refs != mutant_null_refs:
                    continue

                origin_path_result = (
                    JBSEPathResultReturn(
                        z3_traverse_unparse_symbol(
                            origin_path.result.value, origin_path.symmap
                        )
                    )
                    if type(origin_path.result) == JBSEPathResultReturn
                    else origin_path.result
                )
                mutant_path_result = (
                    JBSEPathResultReturn(
                        z3_traverse_unparse_symbol(
                            mutant_path.result.value, mutant_path.symmap
                        )
                    )
                    if type(mutant_path.result) == JBSEPathResultReturn
                    else mutant_path.result
                )

                if origin_path_result != mutant_path_result:
                    path_condition = [
                        *[
                            z3_traverse_unparse_symbol(c, origin_path.symmap)
                            for c in origin_path.z3_clauses
                        ],
                        *[
                            z3_traverse_unparse_symbol(c, mutant_path.symmap)
                            for c in mutant_path.z3_clauses
                        ],
                    ]

                    feasibility_condition = [
                        *[
                            z3_traverse_unparse_symbol(c, origin_path.symmap)
                            for c in origin_path.feasibility_assumptions
                        ],
                        *[
                            z3_traverse_unparse_symbol(c, mutant_path.symmap)
                            for c in mutant_path.feasibility_assumptions
                        ],
                    ]

                    if (
                        type(mutant_path_result)
                        == type(origin_path_result)
                        == JBSEPathResultReturn
                    ):
                        path_condition.append(
                            origin_path_result.value != mutant_path_result.value
                        )

                    s = z3.Optimize()
                    s.add(*path_condition)
                    for c in feasibility_condition:
                        s.add_soft(c)

                    if str(s.check()) == "sat":
                        inputs = get_inputs(
                            get_n_models(s, self.num_models),
                            origin_null_refs,
                            self.methods,
                            origin_path.symmap,
                        )

                        self.kill_conditions.append(
                            {
                                "origin_pathname": origin_path.name,
                                "origin_result_string": origin_path.result.to_string(
                                    origin_path.symmap
                                ),
                                "origin_result_description": origin_path.result.to_description(
                                    origin_path.symmap
                                ),
                                "mutant_pathname": mutant_path.name,
                                "mutant_result_string": mutant_path.result.to_string(
                                    mutant_path.symmap
                                ),
                                "mutant_result_description": mutant_path.result.to_description(
                                    mutant_path.symmap
                                ),
                                "path_condition": z3_to_java_without_symmap(
                                    z3.simplify(z3.And(*path_condition))
                                ),
                                "inputs": inputs,
                            }
                        )
                    elif str(s.check()) == "unknown":
                        self.unknown_conditions.append(
                            {
                                "origin_pathname": origin_path.name,
                                "origin_result": origin_path.result.to_description(
                                    origin_path.symmap
                                ),
                                "mutant_pathname": mutant_path.name,
                                "mutant_result": mutant_path.result.to_description(
                                    mutant_path.symmap
                                ),
                                "path_condition": [
                                    z3_to_java_without_symmap(cond)
                                    for cond in path_condition
                                ],
                            }
                        )


def get_inputs(
    models: Sequence[z3.ModelRef],
    null_refs: Sequence[str],
    methods: Sequence[Tuple[str, str, dict, JavaType]],
    symmap: dict[Sequence[Tuple[str, str]], JBSESymbol],
) -> Sequence[dict[str, Tuple[Union[list, str], JavaType]]]:
    result = []
    params = methods[0][2]

    string_variables = []
    array_variables = {}  # XXX: array of primitive types (including arrays and strings)

    def is_primitive_array(t: JavaType) -> bool:
        if type(t) != JavaTypeArray:
            return False

        if type(t.inner) == JavaTypeArray:
            return is_primitive_array(t.inner)

        if type(t.inner) != JavaTypeClass:
            return True

        return t.inner.binary_name == "java/lang/String"

    for param_name, param_type in params.items():
        def set_array_variables(name: str, type_desc: JavaType):
            if name in array_variables:
                return

            array_variables[name] = type_desc.inner

            if type(type_desc.inner) == JavaTypeArray:
                for key in symmap:
                    child_name = ".".join(name for _, name in key)
                    matched = re.match(rf"^{re.escape(name)}\[(\d+)\]", child_name)
                    if matched:
                        set_array_variables(
                            f"{name}[{matched.group(1)}]", type_desc.inner
                        )

            elif (
                type(type_desc.inner) == JavaTypeClass
                and type_desc.inner.binary_name == "java/lang/String"
            ):
                for key in symmap:
                    child_name = ".".join(name for _, name in key)
                    matched = re.match(rf"^{re.escape(name)}\[(\d+)\]", child_name)
                    if matched:
                        string_variables.append(f"{name}[{matched.group(1)}]")

        # array
        if is_primitive_array(param_type):
            set_array_variables(param_name, param_type)

        # string
        if type(param_type) == JavaTypeClass:
            if param_type.binary_name == "java/lang/String":
                string_variables.append(param_name)

            else:
                for key, symbol in symmap.items():
                    name = ".".join(name for _, name in key)

                    if (
                        name.startswith(param_name + ".")
                        and type(symbol) == JBSESymbolRef
                    ):
                        # array
                        if is_primitive_array(symbol.type):
                            set_array_variables(name, symbol.type)

                        # string
                        if (
                            type(symbol.type) == JavaTypeClass
                            and symbol.type.binary_name == "java/lang/String"
                        ):
                            string_variables.append(name)

    array_variables = list(array_variables.items())

    array_variables.sort(key=lambda x: -len(x[0]))
    string_variables.sort(key=lambda x: -len(x))

    for i, model in enumerate(models):
        cases = {}

        model_variables = dict(
            [(variable.name(), model.evaluate(variable())) for variable in model]
        )
        consumed_variables = []

        # string
        for string_variable in string_variables:
            string_conditions = {}

            for var, val in model_variables.items():
                matched = re.match(
                    rf"{re.escape(string_variable)}\.value\[(\d+)\]", var
                )
                if matched:
                    consumed_variables.append(var)
                    string_conditions[int(matched.group(1))] = int(val.params()[0])

            if f"{string_variable}.value.length" not in model_variables:
                length = max(list(string_conditions) + [0])

            else:
                val = model_variables[f"{string_variable}.value.length"]
                consumed_variables.append(f"{string_variable}.value.length")
                length = int(val.params()[0])

            string = ""
            for i in range(length):
                if i in string_conditions:
                    string += (
                        chr(string_conditions[i])
                        if string_conditions[i] != 0
                        else "\u0000"
                    )
                else:
                    string += "?"

            cases[string_variable] = (json.dumps(string), JavaTypeClass("java/lang/String"))

        # array
        for (array_variable, inner_type) in array_variables:
            # array of arrays
            if type(inner_type) == JavaTypeArray:
                array_conditions = {}

                for var, val in cases.items():
                    matched = re.match(rf"^{re.escape(array_variable)}\[(\d+)\]$", var)
                    if matched:
                        consumed_variables.append(var)
                        array_conditions[int(matched.group(1))] = val

                if f"{array_variable}.length" not in model_variables:
                    length = max(list(array_conditions) + [0])

                else:
                    val = model_variables[f"{array_variable}.length"]
                    consumed_variables.append(f"{array_variable}.length")
                    length = int(val.params()[0])

                array = []
                for i in range(length):
                    if i in array_conditions:
                        array.append(array_conditions[i])
                    else:
                        array.append(([], inner_type))

                cases[array_variable] = (array, JavaTypeArray(inner_type))

            # array of strings
            elif type(inner_type) == JavaTypeClass:
                array_conditions = {}

                for var, val in cases.items():
                    matched = re.match(rf"^{re.escape(array_variable)}\[(\d+)\]$", var)
                    if matched:
                        consumed_variables.append(var)
                        array_conditions[int(matched.group(1))] = val

                if f"{array_variable}.length" not in model_variables:
                    length = max(list(array_conditions) + [0])

                else:
                    val = model_variables[f"{array_variable}.length"]
                    consumed_variables.append(f"{array_variable}.length")
                    length = int(val.params()[0])

                array = []
                for i in range(length):
                    if i in array_conditions:
                        array.append(array_conditions[i])
                    else:
                        array.append(("", inner_type))

                cases[array_variable] = (array, JavaTypeArray(inner_type))

            # array of primitives
            else:
                array_conditions = {}

                for var, val in model_variables.items():
                    matched = re.match(rf"^{re.escape(array_variable)}\[(\d+)\]$", var)
                    if matched:
                        consumed_variables.append(var)
                        if inner_type == JavaTypeDouble():
                            num_literal = val.as_decimal(prec=17).replace("?", "")

                            if "." not in num_literal:
                                array_conditions[
                                    int(matched.group(1))
                                ] = f"{num_literal}.0d"
                            else:
                                array_conditions[
                                    int(matched.group(1))
                                ] = f"{num_literal}d"

                        else:
                            array_conditions[int(matched.group(1))] = int(
                                val.params()[0]
                            )

                if f"{array_variable}.length" not in model_variables:
                    length = max(list(array_conditions) + [0])

                else:
                    val = model_variables[f"{array_variable}.length"]
                    consumed_variables.append(f"{array_variable}.length")
                    length = int(val.params()[0])

                array = []
                for i in range(length):
                    if i in array_conditions:
                        v = array_conditions[i]

                        if inner_type == JavaTypeBoolean():
                            array.append(("false" if v == 0 else "true", inner_type))
                        if inner_type == JavaTypeByte():
                            array.append((f"(byte) {v if v < 128 else v - 256}", inner_type))
                        if inner_type == JavaTypeChar():
                            array.append((f"'{chr(v)}'" if v != 0 else "'\\u0000'", inner_type))
                        if inner_type == JavaTypeDouble():
                            array.append((v, inner_type))
                        if inner_type == JavaTypeInt():
                            array.append((str(v if v < 2 ** 31 else v - 2 ** 32), inner_type))
                        if inner_type == JavaTypeLong():
                            array.append((f"{v if v < 2 ** 63 else v - 2 ** 64}L", inner_type))

                    else:
                        if inner_type == JavaTypeBoolean():
                            array.append(("false", inner_type))
                        if inner_type == JavaTypeByte():
                            array.append(("(byte) 0", inner_type))
                        if inner_type == JavaTypeChar():
                            array.append(("'?'", inner_type))
                        if inner_type == JavaTypeDouble():
                            array.append(("0.0d", inner_type))
                        if inner_type == JavaTypeInt():
                            array.append(("0", inner_type))
                        if inner_type == JavaTypeLong():
                            array.append(("0L", inner_type))

                cases[array_variable] = (array, JavaTypeArray(inner_type))

        for var, val in model_variables.items():
            if var not in consumed_variables:
                var_type = next(
                    (
                        symbol.type
                        for key, symbol in symmap.items()
                        if ".".join([k[1] for k in key]) == var
                    ),
                    None,
                )

                if var_type is not None:
                    if var_type == JavaTypeDouble():
                        num_literal = val.as_decimal(prec=17).replace("?", "")

                        if "." not in num_literal:
                            cases[var] = (f"{num_literal}.0d", var_type)
                        else:
                            cases[var] = (f"{num_literal}d", var_type)

                    else:
                        v = int(val.params()[0])
                        if var_type == JavaTypeBoolean():
                            cases[var] = ("false" if v == 0 else "true", var_type)
                        if var_type == JavaTypeByte():
                            cases[var] = (f"(byte) {v if v < 128 else v - 256}", var_type)
                        if var_type == JavaTypeChar():
                            cases[var] = (f"'{chr(v)}'" if v != 0 else "'\\u0000'", var_type)
                        if var_type == JavaTypeInt():
                            cases[var] = (str(v if v < 2 ** 31 else v - 2 ** 32), var_type)
                        if var_type == JavaTypeLong():
                            cases[var] = (f"{v if v < 2 ** 63 else v - 2 ** 64}L", var_type)

        for var in consumed_variables:
            if cases.get(var) is not None:
                cases.pop(var)

        # reference variables which are null
        for null_ref in null_refs:
            var_type = next(
                (
                    symbol.type
                    for key, symbol in symmap.items()
                    if ".".join([k[1] for k in key]) == var
                ),
                None,
            )

            cases[null_ref] = ("null", var_type)

        result.append(cases)

    return result
