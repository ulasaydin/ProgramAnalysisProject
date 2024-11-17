import math
import z3
from ast import Expression
import copy
import dis
from webbrowser import get
from src.interpreter import ProgramState, Python39Interpreter
from src.util import function_initial_locals_from_inputs


class SymbolicProgramState(ProgramState):
    pass

class Expression:
    pass

class SymbolicInterpreter(Python39Interpreter):
    def __init__(self, env, entry_point):
        super().__init__(env, entry_point)

    def symbolic_step(self, symbolic_program_state: SymbolicProgramState) -> list[tuple[SymbolicProgramState, Expression]]:
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