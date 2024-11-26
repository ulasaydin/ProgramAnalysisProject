from typing import Any

import z3
from copy import deepcopy
import dis

from interpreter import Frame, ProgramState, Python39Interpreter
from symbolic_integer_array import SymbolicIntegerArray


class SymbolicFrame(Frame):
    def __init__(self, function_name: str, locals_: dict[str, any]):
        super().__init__(function_name, locals_)
        #self.locals_latest_version: dict[str, tuple[str, int]] = { k : (k, 0) for k in locals_.keys() }


class SymbolicProgramState(ProgramState):
    def __init__(self, entry_point: str, inputs_as_locals: dict[str, Any], heap: dict[str, Any]):
        super().__init__(entry_point, inputs_as_locals, heap)
        self.frames: list[SymbolicFrame] = [SymbolicFrame(function_name=entry_point, locals_=inputs_as_locals)]

    @classmethod
    def generate_symbolic_state_from_arguments_and_bytecode(cls, 
                                                            entry_point: str, 
                                                            entry_point_function_bytecode: dis.Bytecode, 
                                                            symbolic_arguments: list[Any],
                                                            heap: dict[str, Any]):
        return cls.generate_program_state_from_arguments_and_bytecode(
            entry_point,
            entry_point_function_bytecode,
            symbolic_arguments,
            heap
        )

    @property
    def top_frame(self) -> SymbolicFrame:
        return self.frames[-1]

    def to_concrete_state(self, model: z3.ModelRef):
        #print("Making symbolic state concrete", self)
        concrete_state = deepcopy(self)
        for frame in concrete_state.frames:
            for var_name, var_value in frame.locals.items():
                #var_value = frame.locals[latest_var_name]
                if isinstance(var_value, SymbolicIntegerArray):
                    frame.locals[var_name] = var_value.to_concrete(model)
                    continue
                if z3.is_expr(var_value):
                    e = model.evaluate(var_value)
                    if z3.is_const(e):
                        if z3.is_int_value(e):
                            frame.locals[var_name] = e.as_long()
                        if z3.is_bool(e):
                            frame.locals[var_name] = z3.is_true(e)
                else:
                    frame.locals[var_name] = var_value
                """
                if isinstance(var_value, z3.IntNumRef):
                    frame.locals[var_name] = var_value.as_long()
                    continue
                if model[var_value] is None:
                    frame.locals[var_name] = inputs[var_value]
                    continue
                if isinstance(var_value, z3.ExprRef):
                    if isinstance(var_value, z3.ArithRef):
                        frame.locals[var_name] = model[var_value].as_long()
                    elif isinstance(var_value, z3.BoolRef):
                        frame.locals[var_name] = z3.is_true(model[var_value])
                    else:
                        raise NotImplementedError(f"Unsupported z3 type {type(var_value)}") 
                else:
                    frame.locals[var_name] = var_value
                """
        for i, stack_value in enumerate(concrete_state.stack):
            if isinstance(stack_value, SymbolicIntegerArray):
                stack_value = stack_value.to_concrete(model)
                continue
            if z3.is_expr(stack_value):
                e = model.evaluate(stack_value)
                if z3.is_const(e):
                    if z3.is_int_value(e):
                        stack_value = e.as_long()
                    if z3.is_bool(e):
                        stack_value = z3.is_true(e)
            """
            if isinstance(stack_value, z3.ExprRef):
                if isinstance(stack_value, z3.ArithRef):
                    stack_value = model[stack_value].as_long()
                elif isinstance(stack_value, z3.BoolRef):
                    stack_value = z3.is_true(model[stack_value])
                else:
                    raise NotImplementedError(f"Unsupported z3 type {type(stack_value)}")
            """
            concrete_state.stack[i] = stack_value
        return concrete_state


class SymbolicInterpreter(Python39Interpreter):
    def __init__(self, env, entry_point, name=None, verbose=False):
        super().__init__(env, entry_point, name, verbose)
        self.possible_branches = []
        self.constraints = []

    def handle_builtin_function_call(self, function_name, inputs):
        if function_name == 'len' and isinstance(inputs[0], SymbolicIntegerArray):
            self.constraints.append(inputs[0].length() >= 0)
            return inputs[0].length()

    def create_new_frame(self, function_name: str, locals_: dict[str, Any]):
        return SymbolicFrame(function_name, locals_)

    def step_STORE_FAST(self, instruction):
        tos = self.stack.pop()
        self.state.top_frame.locals[
            self.bytecode.codeobj.co_varnames[instruction.arg]
        ] = z3.simplify(tos) if z3.is_expr(tos) else tos
        self.pc += 1

    """
    def step_STORE_FAST(self, instruction: dis.Instruction):
        var_name = self.bytecode.codeobj.co_varnames[instruction.arg]
        if var_name not in self.state.top_frame.locals_latest_version:
            self.state.top_frame.locals_latest_version[var_name] = var_name, 0
        _, latest_version =  self.state.top_frame.locals_latest_version[var_name]
        new_version = latest_version + 1
        new_var_name = f"{var_name}_{new_version}"
        self.state.top_frame.locals_latest_version[var_name] = new_var_name, new_version
        tos = self.stack.pop()
        self.state.top_frame.locals[new_var_name] = z3.simplify(tos) if not isinstance(tos, SymbolicIntegerArray) else tos
        self.pc += 1
        if isinstance(tos, z3.ArithRef):
            new_var = z3.Int(new_var_name)
        elif isinstance(tos, z3.BoolRef):
            new_var = z3.Bool(new_var_name)
        else:
            raise NotImplementedError(f"Unsupported z3 type {type(tos)}")
        self.possible_branches = [(self.state, new_var == tos)]

    def step_LOAD_FAST(self, instruction: dis.Instruction):
        var_name = self.bytecode.codeobj.co_varnames[instruction.arg]
        latest_var_name, _ =  self.state.top_frame.locals_latest_version[var_name]
        self.stack.append(self.state.top_frame.locals[latest_var_name])
        self.pc += 1
    """

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