import math
import z3
from ast import Expression
import copy
import dis
from webbrowser import get
from src.interpreter import Frame, ProgramState, Python39Interpreter
from src.util import function_initial_locals_from_inputs


class SymbolicFrame(Frame):
    def __init__(self, function_name: str, locals_: dict[str, any]):
        super().__init__(function_name, locals_)
        self.latest_locals: dict[str, str] = { k : (k, 0) for k in locals_.keys() }


class SymbolicProgramState(ProgramState):
    def __init__(self, entry_point, inputs_as_locals):
        super().__init__(entry_point, inputs_as_locals)
        self.frames: list[SymbolicFrame] = [SymbolicFrame(function_name=entry_point, locals_=inputs_as_locals)]


class Expression:
    pass

class SymbolicInterpreter(Python39Interpreter):
    def __init__(self, env, entry_point):
        super().__init__(env, entry_point)

    def step_STORE_FAST(self, instruction) -> list[tuple[SymbolicProgramState, Expression]]:
        var_name = self.bytecode.codeobj.co_varnames[instruction.arg]
        base_name, latest_version =  self.state.top_frame.latest_locals[var_name]
        new_version = latest_version + 1
        new_var_name = f"{base_name}_{new_version}"
        
        self.state.top_frame.latest_locals[var_name] = (base_name, new_version)
        tos = self.stack.pop()
        self.state.top_frame.locals[new_var_name] = tos
        self.pc += 1
        super().step_STORE_FAST(instruction)
        
        return [(self.state, z3.Int(new_var_name) == tos)]

    def step_with_state(self, symbolic_program_state: SymbolicProgramState) -> list[tuple[SymbolicProgramState, Expression]]:
        self.state = symbolic_program_state
        instruction = self.instructions[self.pc]
        l = self.step(instruction)
        if l is None:
            return [(self.state, Expression(True))]
        else:
            return l

    def step_JUMP_IF_FALSE_OR_POP(self, instruction: dis.Instruction) -> list[tuple[SymbolicProgramState, Expression]]:
        condition = self.stack[-1]
        old_state = copy.deepcopy(self.state)
        branches = []
        
        self.stack.pop()
        self.pc += 1
        branches.append((self.state, condition))

        self.state = old_state
        self.pc = instruction.arg // 2
        branches.append((self.state, z3.Not(condition)))
        return branches

    def step_POP_JUMP_IF_TRUE(self, instruction: dis.Instruction) -> list[tuple[SymbolicProgramState, Expression]]:
        condition = self.stack.pop()
        old_state = copy.deepcopy(self.state)
        branches = []
        
        self.pc = instruction.arg // 2
        branches.append((self.state, condition))

        self.state = old_state
        self.pc += 1
        branches.append((self.state, z3.Not(condition)))
        return branches

    def step_POP_JUMP_IF_FALSE(self, instruction: dis.Instruction) -> list[tuple[SymbolicProgramState, Expression]]:
        condition = z3.Not(self.stack.pop())
        old_state = copy.deepcopy(self.state)
        branches = []

        self.pc = instruction.arg // 2
        branches.append((self.state, condition))

        self.state = old_state
        self.pc += 1
        branches.append((self.state, z3.Not(condition)))
        return branches