import os
import argparse
import re
from typing import Optional, Tuple, Sequence, Union

import pprint
import z3
from glob import glob
from src.java.type import (
    JavaType,
    JavaTypeArray,
    JavaTypeBoolean,
    JavaTypeByte,
    JavaTypeChar,
    JavaTypeClass,
    JavaTypeDouble,
    JavaTypeFloat,
    JavaTypeInt,
    JavaTypeLong,
    JavaTypeShort,
)

from src.jbse.path import JBSEPath, JBSEPathAux, JBSEPathResultReturn
from src.jbse.path_condition import (
    PathConditionClauseAssumeNull,
)
from src.jbse.symbol import JBSESymbol, JBSESymbolRef, JBSESymbolValue
from src.util.arg import parse_method
from src.util.math import get_n_models

from src.util.z3_to_java import (
    bv_to_java,
    z3_to_java,
    z3_to_java_without_symmap,
    z3_traverse_unparse_symbol,
)


curr_dir = os.getcwd()
NUM_MODELS = 4


def main(target: str, methods: Sequence[str], num_models: int, debug: bool = False):
    methods = [parse_method(method) for method in methods]

    with open(target, "r") as f:
        content = "".join(f.readlines())

    path = JBSEPath.parse(content, JBSEPathAux(methods))
    if debug:
        pprint.pprint(
            path,
            indent=4,
            compact=False,
        )

    s, r, models = path.solve(num_models)

    return path, s, r, models


def log(
    path: JBSEPath,
    s: z3.Solver,
    r: z3.CheckSatResult,
    models: Sequence[Tuple[z3.ModelRef, Sequence[int]]],
):
    print("============================================================")
    for key, value in path.symmap.items():
        print(repr(value)[:4], "====>", key)

    if r == z3.unsat:
        # XXX: probably this is already filtered out from JBSE results.
        print(f"The path {path.name} is unreachable.")
    elif r == z3.unknown:
        if models == []:
            print(
                "The Z3 did not solve any clauses!"
                "So we have no information for this path."
            )
        else:
            print(
                f"The path {path.name} is partially satisfiable with the following model{'' if len(models) == 1 else 's'}."
            )
            for i, (m, u) in enumerate(models):
                print(f"{i + 1}.", repr(m))
                print("    Unsatisfied clauses: ", [path.z3_clauses[i] for i in u])
    else:
        print(
            f"The path {path.name} is satisfiable with the following model{'' if len(models) == 1 else 's'}."
        )
        for i, (m, _) in enumerate(models):
            print(f"{i + 1}.", repr(m))


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
                            + origin_path.feasibility_assumptions
                        ],
                        *[
                            z3_traverse_unparse_symbol(c, mutant_path.symmap)
                            for c in mutant_path.z3_clauses
                            + mutant_path.feasibility_assumptions
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

                    s = z3.Solver()
                    s.add(*path_condition)

                    if str(s.check()) == "sat":
                        inputs = get_inputs(
                            get_n_models(s, self.num_models),
                            (origin_null_refs, mutant_null_refs),
                            self.methods,
                            origin_path.symmap,
                        )

                        self.kill_conditions.append(
                            {
                                "origin_pathname": origin_path.name,
                                "origin_result": origin_path.result.to_string(
                                    origin_path.symmap
                                ),
                                "mutant_pathname": mutant_path.name,
                                "mutant_result": mutant_path.result.to_string(
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
                                "origin_result": origin_path.result.to_string(
                                    origin_path.symmap
                                ),
                                "mutant_pathname": mutant_path.name,
                                "mutant_result": mutant_path.result.to_string(
                                    mutant_path.symmap
                                ),
                                "path_condition": [
                                    z3_to_java_without_symmap(cond)
                                    for cond in path_condition
                                ],
                            }
                        )


def print_parse_result(
    project: str, mutant: Optional[int], filename: str, num_models: int
):

    if mutant is None:
        target_path = os.path.join(project, "original", filename)
    else:
        target_path = os.path.join(
            project,
            "mutants",
            str(mutant),
            filename,
        )

    # run main
    path, s, r, models = main(
        target_path,
        methods,
        num_models,
    )

    path_condition = z3.simplify(z3.And(*path.z3_clauses))

    if args.verbose:
        print("Result of the path:")
        print(path.result)
        print("")

        print("Concatenation of all clauses:")
        print(path_condition)
        print("")

        # Simplification using ctx-solver-simplify tactic,
        # but it seems not that good at times...
        print("Simplification using ctx-solver-simplify:")
        print(z3.Tactic("ctx-solver-simplify")(path_condition))
        print("")

        print("Path condition in Java syntax:")
        print(path_condition, "--->")
        print("    " + z3_to_java(path_condition, path.symmap))
        print("")

        print("Models:")
        for i, (model, unsat_clauses) in enumerate(models):
            print("Model " + str(i) + ":")

            if len(unsat_clauses) != 0:
                print("   ", "Unsatisfied clauses:")
                for j, clause in enumerate(unsat_clauses):
                    print("   ", "   ", str(j) + ".", clause)

            print("   ", "Assignments:")

            stringified_conditions = []

            for variable in model:
                name = variable.name()
                variable = variable()
                stringified_conditions.append(
                    next(
                        (
                            ".".join([k[1] for k in key])
                            for key, value in path.symmap.items()
                            if value == path.symmgr.get_parse(name)
                        ),
                        None,
                    )
                    + " = "
                    + bv_to_java(model.evaluate(variable))
                )

            for clause in path.null_clauses:
                stringified_conditions.append(
                    next(
                        (
                            ".".join([k[1] for k in key])
                            for (key, value) in path.symmap.items()
                            if value == clause.sym_ref
                        ),
                        None,
                    )
                    + " == null",
                )

            print(
                ";\n".join("        " + x for x in stringified_conditions),
                end=";\n",
            )

        print("")

    else:
        stringified_condition = "&&".join(
            condition
            for condition in [
                z3_to_java(path_condition, path.symmap),
                *[
                    "("
                    + next(
                        (
                            ".".join([k[1] for k in key])
                            for (key, value) in path.symmap.items()
                            if value == clause.sym_ref
                        ),
                        None,
                    )
                    + " == null)"
                    for clause in path.clauses
                    if type(clause) == PathConditionClauseAssumeNull
                ],
            ]
            if condition != "true"
        )

        if stringified_condition == "":
            stringified_condition = "true"

        print(stringified_condition)


# FIXME: !!!!
def get_inputs(
    models: Sequence[z3.ModelRef],
    null_refs: Tuple[Sequence[str], Sequence[str]],
    methods: Sequence[Tuple[str, str, dict, JavaType]],
    symmap: dict[Sequence[Tuple[str, str]], JBSESymbol],
) -> Sequence[dict[str, str]]:
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

            array_variables[name] = type(type_desc.inner)

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
                        else "\\u0000"
                    )
                else:
                    string += "?"

            cases[string_variable] = string

        # array
        for (array_variable, inner_type) in array_variables:
            # array of arrays
            if inner_type == JavaTypeArray:
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
                        array.append([])

                cases[array_variable] = array

            # array of strings
            elif inner_type == JavaTypeClass:
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
                        array.append("")

                cases[array_variable] = array

            # array of primitives
            else:
                array_conditions = {}

                for var, val in model_variables.items():
                    matched = re.match(rf"^{re.escape(array_variable)}\[(\d+)\]$", var)
                    if matched:
                        consumed_variables.append(var)
                        if inner_type == JavaTypeDouble:
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

                        if inner_type == JavaTypeBoolean:
                            array.append("false" if v == 0 else "true")
                        if inner_type == JavaTypeByte:
                            array.append(f"(byte) {v if v < 128 else v - 256}")
                        if inner_type == JavaTypeChar:
                            array.append(f"'{chr(v)}'" if v != 0 else "'\\u0000'")
                        if inner_type == JavaTypeDouble:
                            array.append(v)
                        if inner_type == JavaTypeInt:
                            array.append(str(v if v < 2 ** 31 else v - 2 ** 32))
                        if inner_type == JavaTypeLong:
                            array.append(f"{v if v < 2 ** 63 else v - 2 ** 64}L")

                    else:
                        if inner_type == JavaTypeBoolean:
                            array.append("false")
                        if inner_type == JavaTypeByte:
                            array.append("(byte) 0")
                        if inner_type == JavaTypeChar:
                            array.append("'?'")
                        if inner_type == JavaTypeDouble:
                            array.append("0.0d")
                        if inner_type == JavaTypeInt:
                            array.append("0")
                        if inner_type == JavaTypeLong:
                            array.append("0L")

                cases[array_variable] = array

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
                    if var_type == JavaTypeDouble:
                        num_literal = val.as_decimal(prec=17).replace("?", "")

                        if "." not in num_literal:
                            cases[var] = f"{num_literal}.0d"
                        else:
                            cases[var] = f"{num_literal}d"

                    else:
                        v = int(val.params()[0])
                        if var_type == JavaTypeBoolean:
                            cases[var] = "false" if v == 0 else "true"
                        if var_type == JavaTypeByte:
                            cases[var] = f"(byte) {v if v < 128 else v - 256}"
                        if var_type == JavaTypeChar:
                            cases[var] = f"'{chr(v)}'" if v != 0 else "'\\u0000'"
                        if var_type == JavaTypeInt:
                            cases[var] = str(v if v < 2 ** 31 else v - 2 ** 32)
                        if var_type == JavaTypeLong:
                            cases[var] = f"{v if v < 2 ** 63 else v - 2 ** 64}L"

        for var in consumed_variables:
            if cases.get(var) is not None:
                cases.pop(var)

        result.append(cases)

    return result


if __name__ == "__main__":
    # Argument Parsing
    parser = argparse.ArgumentParser()
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose mode")
    parser.add_argument(
        "--nummodels", "-n", default=NUM_MODELS, help="# of models (e.g. 10)"
    )
    parser.add_argument("--action", "-a", choices=["parse", "kill"], default="kill")
    parser.add_argument(
        "--project",
        "-p",
        required=True,
        help="Project directory path (e.g. examples/1)",
    )
    parser.add_argument("--mutant", "-m", default=None, help="Mutant index (e.g. 1)")
    parser.add_argument(
        "--filename", "-f", help="Filename (e.g. path4.txt)", nargs="+", default=None
    )

    args = parser.parse_args()

    with open(os.path.join(args.project, "methods.txt"), "r") as methods_file:
        methods = [l.strip() for l in methods_file.readlines()]

    action = args.action

    try:
        num_models = int(args.nummodels)
    except:
        num_models = NUM_MODELS

    if action == "parse":
        paths_dir = (
            os.listdir(os.path.join(args.project, "mutants", str(args.mutant)))
            if args.mutant is not None
            else os.listdir(os.path.join(args.project, "original"))
        )

        for filename in args.filename or paths_dir:
            print(f"[Path: {filename}]")
            print_parse_result(args.project, args.mutant, filename, num_models)

    if action == "kill":
        origin, mutant = glob(f"{args.project}/original/*.txt"), glob(
            f"{args.project}/mutants/{args.mutant}/*.txt"
        )

        origin = ["".join(open(file).readlines()) for file in origin]
        mutant = ["".join(open(file).readlines()) for file in mutant]

        finder = KillConditionFinder(origin, mutant, methods, num_models)

        finder.find_kill()

        pprint.pprint(finder.kill_conditions)
        pprint.pprint(finder.unknown_conditions)
