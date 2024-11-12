from dataclasses import dataclass
import dis
import ast


@dataclass
class Fuzzer:
    function: ast.FunctionDef
    bytecode: dis.Bytecode
    preconditions: list[ast.Expr]

    def generate_test_cases(self) -> list[list]:
        pass