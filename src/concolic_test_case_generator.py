import ast
from copy import deepcopy
from dataclasses import dataclass
import enum
from typing import Any, List, Dict
import uuid
import dis
import z3

from src import symbolic_interpreter
from src.interpreter import ProgramState, Python39Interpreter
from util import extract_parameter_types, function_initial_locals_from_inputs, generate_random_value
from symbolic_interpreter import SymbolicInterpreter, SymbolicProgramState

def types_to_symbolic_inputs(random_inputs: list[str]):
    symbolic_inputs = []
    for input in random_inputs:
        unique_name = str(uuid.uuid4())
        if isinstance(input, int):
            symbolic_inputs.append(z3.Int(unique_name))
        elif isinstance(input, bool):
            symbolic_inputs.append(z3.Bool(unique_name))
        elif isinstance(input, float):
            symbolic_inputs.append(z3.Real(unique_name))
    return symbolic_inputs


@dataclass
class ConcolicTestCaseGenerator:
    env: dict[str, tuple[ast.FunctionDef, dis.Bytecode]]
    entry_point: str

    def __init__(self):
        interpreter_env = { function_name : function_bytecode for function_name, (_, function_bytecode) in self.env.items() }
        self.concrete_interpreter = Python39Interpreter(interpreter_env, self.entry_point)
        self.symbolic_interpreter = SymbolicInterpreter(interpreter_env, self.entry_point)
        self.test_cases = []

    def generate_test_cases(self, max_depth = 50) -> list[list[any]]:
        entry_point_function_ast, entry_point_function_bytecode = self.env[self.entry_point]
        parameter_types = extract_parameter_types(entry_point_function_ast)
        random_inputs = [generate_random_value(param_type) for param_type in parameter_types]
        self.symbolic_arguments = types_to_symbolic_inputs(parameter_types)
        initial_concrete_state = ProgramState(
            self.entry_point, 
            function_initial_locals_from_inputs(self.entry_point_function_bytecode, random_inputs))
        initial_symbolic_state = SymbolicProgramState(
            self.entry_point, 
            function_initial_locals_from_inputs(self.entry_point_function_bytecode, self.symbolic_arguments))
        self.max_depth = max_depth
        self.rec(initial_symbolic_state, initial_concrete_state, [])
        return self.test_cases

    def model_to_testcase(self, model: z3.ModelRef):
        test_case = []
        for argument in self.symbolic_arguments:
            test_case.append(model[argument])
        return test_case        

    def rec(self, symbolic_state: SymbolicProgramState, concrete_state: ProgramState, path_constraints, depth):
        if depth > self.max_depth:
            return
        
        chosen_branch, new_concrete_state = self.concrete_interpreter.step_with_state(concrete_state)
        branches = self.symbolic_interpreter.step_with_state(symbolic_state)
                    
        if new_concrete_state.done:
            return

        for i, branch in enumerate(branches):
            new_symbolic_state, path_constraint = branch
            if i != chosen_branch:

                new_testcase_conditions = path_constraints + path_constraint
                solver = z3.Solver()
                solver.add(new_testcase_conditions)
                if solver.check() == z3.sat:
                    model = solver.model()
                    self.test_cases.append(self.model_to_testcase(model))
                else:
                    continue

                #update concrete state with new_testcase
                modified_concrete_state = deepcopy.copy(concrete_state)
                for frame in modified_concrete_state.frames:
#                    for var_name in model.decls(): #maybe https://z3prover.github.io/api/html/z3.z3.html#ModelRef
#                        frame.locals[var_name] = model[var_name]
                    for var_name, _ in frame.locals.items():
                        frame.locals[var_name] = model[var_name]
                
                self.rec(new_symbolic_state, modified_concrete_state, path_constraints+[path_constraint], depth + 1)
            else:
                # keep with concrete execution
                if len(branches)>1:
                    self.rec(new_symbolic_state, new_concrete_state, path_constraints+[path_constraint], depth + 1)
                else:
                    # normal execution without any branching
                    self.rec(new_symbolic_state, new_concrete_state, path_constraints+[path_constraint], depth )
