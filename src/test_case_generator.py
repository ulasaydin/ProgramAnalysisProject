from dataclasses import dataclass
import dis
import ast

from interpreter import Interpreter


@dataclass
class TestCaseGenerator:
    env: dict[str, dis.Bytecode]
    entry_point: str

    def generate_test_cases(self) -> list[list]:
        vm = Interpreter(env=self.env, entry_point=self.entry_point)
        #vm.run()
        # TODO: Implement concolic execution for test case generation with the interpreter