import dis
import math


class Frame:
    def __init__(self, function_name: str, locals_: list[any]):
        self.pc: int = 0
        self.stack: list[any] = []
        self.locals: list[any] = locals_
        self.function_name: str = function_name


class ProgramState:
    def __init__(self, entry_point: str, inputs: list[any]):
        self.heap: dict = {}
        self.frames: list[Frame] = [Frame(function_name=entry_point, locals_=inputs)]
        self.done: bool = False


class Python39Interpreter:
    def __init__(self, env: dict[str, dis.Bytecode], entry_point: str, inputs: list[any]):
        self.env: dict[str, dis.Bytecode] = env
        self.entry_point: str = entry_point
        self.state: ProgramState = ProgramState(entry_point, inputs)
        self.instructions: list[dis.Instruction] = list(self.bytecode)

    @property
    def pc(self) -> int:
        return self.state.frames[-1].pc

    @pc.setter
    def pc(self, value: int):
        self.state.frames[-1].pc = value

    @property
    def stack(self) -> list[any]:
        return self.state.frames[-1].stack

    @stack.setter
    def stack(self, value: list[any]):
        self.state.frames[-1].stack = value

    @property
    def locals(self) -> list[any]:
        return self.state.frames[-1].locals

    @property
    def bytecode(self) -> dis.Bytecode:
        return self.env[self.state.frames[-1].function_name]

    def run(self, max_steps=math.inf) -> any:
        steps_so_far = 0
        while steps_so_far < max_steps:
            instruction = self.instructions[self.pc]
            steps_so_far += 1
            self.step(instruction)
            if self.state.done:
                return self.state.frames[-1].stack[-1]

    def step(self, instruction: dis.Instruction):
        getattr(self, f"step_{instruction.opname}")(instruction)

    def step_LOAD_GLOBAL(self, instruction: dis.Instruction):
        self.stack.append(self.bytecode.codeobj.co_names[instruction.arg])
        self.pc += 1

    def step_LOAD_FAST(self, instruction: dis.Instruction):
        self.stack.append(self.bytecode.codeobj.co_varnames[instruction.arg])
        self.pc += 1

    def step_CALL_FUNCTION(self, instruction: dis.Instruction):
        self.pc += 1
        # pop arguments from top of stack
        inputs = self.stack[-instruction.arg:]
        self.stack = self.stack[:-instruction.arg]
        # pop function name from top of stack
        function_name = self.stack.pop()
        self.state.frames.append(Frame(function_name=function_name, locals_=inputs))
        self.instructions = list(self.bytecode)

