from dataclasses import dataclass
import dis
import ast


@dataclass
class Fuzzer:
    function: ast.FunctionDef
    bytecode: dis.Bytecode
    preconditions: list[ast.Expr]

    def generate_test_cases(self) -> list[list]:
        print(self.preconditions)
        print(ast.unparse(self.function))
        print(self.bytecode.dis())
        #for instruction in self.bytecode:
        #    print(instruction)