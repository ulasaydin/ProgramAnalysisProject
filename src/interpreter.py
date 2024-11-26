import dis
import math
import builtins
import os
import sys
from typing import Any

from attr import dataclass

sys.path.append(os.path.dirname(__file__))

from util import function_initial_locals_from_inputs

class Frame:
    def __init__(self, function_name: str, locals_: dict[str, Any]):
        self.pc: int = 0
        self.locals: dict[str, Any] = locals_
        self.function_name: str = function_name

    def __repr__(self):
        return f"Frame({self.function_name}, locals={self.locals}, pc={self.pc * 2})"

@dataclass
class HeapReference:
    address: int

class ProgramState:
    def __init__(self, entry_point: str, inputs_as_locals: dict[str, Any], heap: dict[int, Any]):
        self.heap: dict = {}
        self.stack: list[any] = []
        self.frames: list[Frame] = [
            Frame(function_name=entry_point, locals_=inputs_as_locals)
        ]
        self.done: bool = False

    @classmethod
    def generate_program_state_from_arguments_and_bytecode(cls, 
                                                           entry_point: str, 
                                                           entry_point_function_bytecode: dis.Bytecode, 
                                                           arguments: list[Any],
                                                           heap: dict[int, Any]):
        return cls(
            entry_point,
            function_initial_locals_from_inputs(entry_point_function_bytecode, arguments),
            heap
        )

    @property
    def top_frame(self) -> Frame:
        return self.frames[-1]

    def __str__(self):
        return f"ProgramState(frames={self.frames}, stack={self.stack}, heap={self.heap})"


class InterpreterError(Exception):
    pass

class Python39Interpreter:
    def __init__(self, env: dict[str, dis.Bytecode], entry_point: str, name=None, verbose=False):
        self.verbose: bool = verbose
        self.name: str = name if name else "Python39Interpreter"
        self.log("Creating Python39Interpreter")
        self.env: dict[str, dis.Bytecode] = env
        for function_name, bytecode in env.items():
            for instruction in list(bytecode):
                if not hasattr(self, f"step_{instruction.opname}"):
                    raise NotImplementedError(
                        f"Instruction {instruction.opname} not implemented"
                    )
            self.log(
                f"Given function {function_name} in the environment with bytecode:\n {bytecode.dis()}"
            )
        self.entry_point: str = entry_point
        self.chosen_branch: int = 0
        self.state: ProgramState = ProgramState(entry_point, {}, {})

    @property
    def instructions(self) -> list[dis.Instruction]:
        return list(self.bytecode)

    @property
    def pc(self) -> int:
        return self.state.top_frame.pc

    @pc.setter
    def pc(self, value: int):
        self.state.top_frame.pc = value

    @property
    def stack(self) -> list[Any]:
        return self.state.stack

    @stack.setter
    def stack(self, value: list[Any]):
        self.state.stack = value

    @property
    def locals(self) -> dict[str, Any]:
        return self.state.top_frame.locals

    @property
    def bytecode(self) -> dis.Bytecode:
        return self.env[self.state.top_frame.function_name]

    @property
    def heap(self) -> dict:
        return self.state.heap

    @property
    def done(self) -> bool:
        return self.state.done

    def run(self, inputs: list[Any], max_steps=math.inf) -> Any:
        inputs_ = function_initial_locals_from_inputs(self.env[self.entry_point], inputs)
        self.state = ProgramState(self.entry_point, inputs_)
        self.log(
            f"Starting execution of {self.state.top_frame.function_name} "
            f"for {max_steps} steps with locals {self.state.top_frame.locals}"
        )
        steps_so_far = 0
        while steps_so_far < max_steps:
            instruction = self.instructions[self.pc]
            steps_so_far += 1
            self.log(f"Executing instruction #{steps_so_far}: {instruction.opname} {instruction.argrepr}, "
                     f"PC: {self.pc * 2} [{self.state.top_frame.function_name}], "
                     f"Operand Stack: {self.stack}, "
                     #f"Heap: {self.state.heap}, "
                     f"Locals: {self.state.top_frame.locals}"
                     #f"Frames: {self.state.frames}"
                     )
            self.step(instruction)
            if self.done:
                return self.stack[-1]

    def step(self, instruction: dis.Instruction) -> Any:
        self.log(f"Executing instruction {instruction.opname} {instruction.argrepr}, "
                 f"PC: {self.pc * 2} [{self.state.top_frame.function_name}], "
                 f"Operand Stack: {self.stack}, "
                 #f"Heap: {self.state.heap}, "
                 f"Locals: {self.state.top_frame.locals}"
                 #f"Frames: {self.state.frames}\n"
                 )
        step_function_name = f"step_{instruction.opname}"
        if hasattr(self, step_function_name):
            return getattr(self, step_function_name)(instruction)
        else:
            raise NotImplementedError(
                f"Instruction {instruction.opname} not implemented"
            )

    def step_with_state(self, concrete_program_state: ProgramState) -> tuple[ProgramState, int]:
        self.state = concrete_program_state
        instruction = self.instructions[self.pc]
        self.chosen_branch = 0
        self.step(instruction)
        return self.state, self.chosen_branch

    def step_LOAD_GLOBAL(self, instruction: dis.Instruction):
        self.stack.append(self.bytecode.codeobj.co_names[instruction.arg])
        self.pc += 1

    def step_LOAD_FAST(self, instruction: dis.Instruction):
        self.stack.append(
            self.state.top_frame.locals[
                self.bytecode.codeobj.co_varnames[instruction.arg]
            ]
        )
        self.pc += 1

    def create_new_frame(self, function_name: str, locals_: dict[str, Any]):
        return Frame(function_name=function_name, locals_=locals_)

    def step_CALL_FUNCTION(self, instruction: dis.Instruction):
        self.pc += 1
        # pop arguments from top of stack
        inputs = self.stack[-instruction.arg :]
        self.stack = self.stack[: -instruction.arg]
        # pop function name from top of stack
        function_name = self.stack.pop()
        if function_name in self.env:
            inputs = function_initial_locals_from_inputs(self.env[function_name], inputs)
            self.state.frames.append(self.create_new_frame(function_name=function_name, locals_=inputs))
        elif function_name in dir(builtins):
            self.stack.append(self.handle_builtin_function_call(function_name, inputs))

    def handle_builtin_function_call(self, function_name: str, inputs: list[Any]):
        return getattr(builtins, function_name)(*inputs)

    def step_LOAD_CONST(self, instruction: dis.Instruction):
        self.stack.append(self.bytecode.codeobj.co_consts[instruction.arg])
        self.pc += 1

    def step_RETURN_VALUE(self, instruction: dis.Instruction):
        self.state.frames.pop()
        if len(self.state.frames) == 0:
            self.state.done = True

    def step_JUMP_IF_FALSE_OR_POP(self, instruction: dis.Instruction):
        if self.stack[-1]:
            self.stack.pop()
            self.pc += 1
            self.chosen_branch = 0
        else:
            self.pc = instruction.arg // 2
            self.chosen_branch = 1

    def step_COMPARE_OP(self, instruction: dis.Instruction):
        b = self.stack.pop()
        a = self.stack.pop()
        op = dis.cmp_op[instruction.arg]
        if op == "<":
            self.stack.append(a < b)
        elif op == "<=":
            self.stack.append(a <= b)
        elif op == "==":
            self.stack.append(a == b)
        elif op == "!=":
            self.stack.append(a != b)
        elif op == ">":
            self.stack.append(a > b)
        elif op == ">=":
            self.stack.append(a >= b)
        self.pc += 1

    def step_POP_JUMP_IF_TRUE(self, instruction: dis.Instruction):
        if self.stack.pop():
            self.pc = instruction.arg // 2
            self.chosen_branch = 0
        else:
            self.pc += 1
            self.chosen_branch = 1

    def step_POP_JUMP_IF_FALSE(self, instruction: dis.Instruction):
        if not self.stack.pop():
            self.pc = instruction.arg // 2
            self.chosen_branch = 0
        else:
            self.pc += 1
            self.chosen_branch = 1

    def step_JUMP_IF_TRUE_OR_POP(self, instruction: dis.Instruction):
        if self.stack[-1]:
            self.pc = instruction.arg // 2
            self.chosen_branch = 0
        else:
            self.stack.pop()
            self.pc += 1
            self.chosen_branch = 1

    def step_BINARY_FLOOR_DIVIDE(self, instruction: dis.Instruction):
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a // b)
        self.pc += 1

    def step_POP_TOP(self, instruction: dis.Instruction):
        self.stack.pop()
        self.pc += 1

    def step_STORE_FAST(self, instruction: dis.Instruction):
        self.state.top_frame.locals[
            self.bytecode.codeobj.co_varnames[instruction.arg]
        ] = self.stack.pop()
        self.pc += 1

    def step_BINARY_SUBTRACT(self, instruction: dis.Instruction):
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a - b)
        self.pc += 1

    def step_BINARY_ADD(self, instruction: dis.Instruction):
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a + b)
        self.pc += 1

    def step_BINARY_SUBSCR(self, instruction: dis.Instruction):
        i = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a[i])
        self.pc += 1

    def step_BINARY_MULTIPLY(self, instruction: dis.Instruction):
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a * b)
        self.pc += 1

    def step_JUMP_ABSOLUTE(self, instruction: dis.Instruction):
        self.pc = instruction.arg // 2

    def step_UNARY_NEGATIVE(self, instruction: dis.Instruction):
        self.stack.append(-self.stack.pop())
        self.pc += 1

    def step_RAISE_VARARGS(self, instruction: dis.Instruction):
        if instruction.arg == 1:
            raise InterpreterError(self.stack.pop())
        elif instruction.arg == 0:
            raise InterpreterError()
        elif instruction.arg == 2:
            tos = self.stack.pop()
            tos1 = self.stack.pop()
            raise InterpreterError(tos1) from tos

    def step_INPLACE_ADD(self, instruction: dis.Instruction):
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a + b)
        self.pc += 1

    def step_STORE_SUBSCR(self, instruction: dis.Instruction):
        tos = self.stack.pop()
        tos1 = self.stack.pop()
        tos2 = self.stack.pop()
        tos1[tos] = tos2
        self.pc += 1

    def log(self, message: str):
        if self.verbose:
            print(f"{self.name}: {message}")
