import dis
import math
from attr import dataclass


@dataclass
class Interpreter:
    env: dict[str, dis.Bytecode]
    entry_point: str
    heap: dict = {}
    stack: list = []
    pc: int = 0
    done: bool = False

    def run(self, max_steps=math.inf) -> bool:
        steps_so_far = 0
        instructions = list(self.env[self.entry_point])
        while steps_so_far < max_steps:
            instruction = instructions[self.pc]
            steps_so_far += 1
            self.step(instruction)
            if self.done:
                return True

    def step(self, instruction: dis.Instruction):
        getattr(self, f"step_{instruction.opname}")(instruction)

    def step_LOAD_GLOBAL(self, instruction: dis.Instruction):
        pass
