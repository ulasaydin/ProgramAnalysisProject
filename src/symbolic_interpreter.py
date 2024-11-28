from typing import Any
import z3
from copy import deepcopy
import dis

from interpreter import Frame, ProgramState, Python39Interpreter
from model_wrapper import ModelWrapper
from symbolic_integer_array import HeapReference, SymbolicIntegerArray


class SymbolicProgramState(ProgramState):
    def __init__(self, entry_point: str, inputs_as_locals: dict[str, Any], heap: dict[int, SymbolicIntegerArray]):
        super().__init__(entry_point, inputs_as_locals, heap)

    def to_concrete_state(self, wrapper: ModelWrapper):
        #print("Making symbolic state concrete", self)
        concrete_state = deepcopy(self)
        for frame in concrete_state.frames:
            for var_name, var_value in frame.locals.items():
                #var_value = frame.locals[latest_var_name]
                if isinstance(var_value, HeapReference):
                    continue
                if z3.is_expr(var_value):
                    e = wrapper.model.evaluate(var_value)
                    if z3.is_int_value(e):
                        frame.locals[var_name] = e.as_long()
                    elif z3.is_true(e) or z3.is_false(e):
                        frame.locals[var_name] = z3.is_true(e)
                    else:
                        pass # TODO
                else:
                    frame.locals[var_name] = var_value
        for i, stack_value in enumerate(concrete_state.stack):
            if isinstance(stack_value, HeapReference):
                continue
            if z3.is_expr(stack_value):
                e = wrapper.model.evaluate(stack_value)
                if z3.is_int_value(e):
                    stack_value = e.as_long()
                elif z3.is_true(e) or z3.is_false(e):
                    stack_value = z3.is_true(e)
                else:
                    pass # TODO
            concrete_state.stack[i] = stack_value
        for k, v in concrete_state.heap.items():
            if isinstance(v, SymbolicIntegerArray):
                concrete_state.heap[k] = v.to_concrete(wrapper)
        return concrete_state


class SymbolicInterpreter(Python39Interpreter):
    def __init__(self, env, entry_point, name=None, verbose=False):
        super().__init__(env, entry_point, name, verbose)
        self.possible_branches = []
        self.constraints = []

    def handle_builtin_function_call(self, function_name, inputs):
        if function_name == 'len' and isinstance(inputs[0], HeapReference):
            container = self.heap[inputs[0].address]
            if isinstance(container, SymbolicIntegerArray):
                self.constraints.append(container.length() >= 0)
                return container.length()

    def step_BINARY_SUBSCR(self, instruction):
        i = self.stack.pop()
        a = self.heap[self.stack.pop().address]
        self.stack.append(a[i])
        self.pc += 1
        self.constraints.append(i >= 0)
        self.constraints.append(i < a.length())

    def step_STORE_SUBSCR(self, instruction):
        tos = self.stack.pop()
        tos1 = self.heap[self.stack.pop().address]
        tos2 = self.stack.pop()
        tos1[tos] = tos2
        self.pc += 1
        self.constraints.append(tos >= 0)
        self.constraints.append(tos < tos1.length())

    def step_STORE_FAST(self, instruction):
        tos = self.stack.pop()
        self.state.top_frame.locals[
            self.bytecode.codeobj.co_varnames[instruction.arg]
        ] = z3.simplify(tos) if z3.is_expr(tos) else tos
        self.pc += 1

    def step_with_state(self, symbolic_program_state: SymbolicProgramState) -> list[tuple[SymbolicProgramState, z3.ExprRef]]:
        self.state = symbolic_program_state
        instruction = self.instructions[self.pc]
        self.constraints = [z3.BoolVal(True)]
        self.possible_branches = []
        self.step(instruction)
        if self.possible_branches:
            return self.possible_branches
        return [(self.state, z3.And(self.constraints))]

    def step_JUMP_IF_FALSE_OR_POP(self, instruction: dis.Instruction):
        condition = self.stack[-1]
        old_state = deepcopy(self.state)
        self.possible_branches = []
        
        self.stack.pop()
        self.pc += 1
        self.possible_branches.append((self.state, condition))

        self.state = old_state
        self.pc = instruction.arg // 2
        self.possible_branches.append((self.state, z3.Not(condition)))

    def step_POP_JUMP_IF_TRUE(self, instruction: dis.Instruction):
        condition = self.stack.pop()
        old_state = deepcopy(self.state)
        self.possible_branches = []
        
        self.pc = instruction.arg // 2
        self.possible_branches.append((self.state, condition))

        self.state = old_state
        self.pc += 1
        self.possible_branches.append((self.state, z3.Not(condition)))

    def step_POP_JUMP_IF_FALSE(self, instruction: dis.Instruction):
        condition = z3.Not(self.stack.pop())
        old_state = deepcopy(self.state)
        self.possible_branches = []

        self.pc = instruction.arg // 2
        self.possible_branches.append((self.state, condition))

        self.state = old_state
        self.pc += 1
        self.possible_branches.append((self.state, z3.Not(condition)))

    def step_JUMP_IF_TRUE_OR_POP(self, instruction: dis.Instruction):
        condition = self.stack[-1]
        old_state = deepcopy(self.state)
        self.possible_branches = []

        self.pc = instruction.arg // 2
        self.possible_branches.append((self.state, condition))
        
        self.state = old_state
        self.pc += 1
        self.possible_branches.append((self.state, z3.Not(condition)))

    def step_LOAD_CONST(self, instruction: dis.Instruction):
        const = self.bytecode.codeobj.co_consts[instruction.arg]
        if type(const) == int:
            self.stack.append(z3.IntVal(const))
        elif type(const) == bool:
            self.stack.append(z3.BoolVal(const))
        elif const is None:
            self.stack.append(const)
        elif type(const) == str:
            self.stack.append(const)
        else:
            raise NotImplementedError(f"Unsupported constant type {type(const)}")
        self.pc += 1

    def step_BINARY_FLOOR_DIVIDE(self, instruction: dis.Instruction):
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a / b)
        self.pc += 1