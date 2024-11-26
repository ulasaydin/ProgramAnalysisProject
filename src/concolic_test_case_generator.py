import ast
from dataclasses import dataclass
from math import e
from typing import Any, Union
from uuid import uuid4
import graphviz
import dis
import z3
import sys
import os

sys.path.append(os.path.dirname(__file__))

from interpreter import InterpreterError
from interpreter import ProgramState, Python39Interpreter
from util import extend_model_with_inputs, extract_parameter_names, extract_parameter_types, extract_arguments_and_annotations, generate_random_value, types_to_symbolic_inputs
from symbolic_interpreter import SymbolicInterpreter, SymbolicProgramState
from symbolic_integer_array import SymbolicIntegerArray


@dataclass
class ConcolicTestCaseGenerator:
    def __init__(self, env: dict[str, tuple[ast.FunctionDef, dis.Bytecode]], entry_point: str):
        self.env: dict[str, tuple[ast.FunctionDef, dis.Bytecode]] = env
        self.entry_point: str = entry_point
        interpreter_env = { function_name : function_bytecode for function_name, (_, function_bytecode) in self.env.items() }
        self.concrete_interpreter = Python39Interpreter(interpreter_env, self.entry_point, verbose=False, name="concrete")
        self.symbolic_interpreter = SymbolicInterpreter(interpreter_env, self.entry_point, verbose=False, name="symbolic")
        self.test_cases: list[list[Any]] = []
        self.requested_test_case_count: int = 0
        self.symbolic_arguments: list[Union[z3.ExprRef, SymbolicIntegerArray]] = []
        self.dot: graphviz.Digraph = None

    def generate_test_cases(self, test_case_count, initial_inputs = None) -> list[list[any]]:
        entry_point_function_ast, entry_point_function_bytecode = self.env[self.entry_point]
        parameter_types = extract_parameter_types(entry_point_function_ast)
        random_inputs = initial_inputs if initial_inputs else [generate_random_value(param_type) for param_type in parameter_types]
        print(f"Starting concolic execution with initial random inputs: {random_inputs}")
        self.symbolic_arguments = types_to_symbolic_inputs(extract_arguments_and_annotations(entry_point_function_ast))
        initial_concrete_state = ProgramState.generate_program_state_from_arguments_and_bytecode(
            self.entry_point,
            entry_point_function_bytecode,
            random_inputs,
            {}
        )
        initial_symbolic_state = SymbolicProgramState.generate_symbolic_state_from_arguments_and_bytecode(
            self.entry_point,
            entry_point_function_bytecode,
            self.symbolic_arguments,
            {}
        )
        root_name = str(uuid4())
        self.dot = graphviz.Digraph("concolic-tree")
        self.dot.node(root_name, label=f"Constraints: {[]}, Inputs: {random_inputs}")
        self.requested_test_case_count = test_case_count
        self.test_cases = []
        self.find_all_paths(root_name, random_inputs, initial_symbolic_state, initial_concrete_state, [], max_branching_depth=10)
        return self.test_cases

    def evaluate_arguments_in_model(self, model: z3.ModelRef) -> list[tuple[str, Any]]:
        new_inputs = []
        for argument in self.symbolic_arguments:
            if isinstance(argument, SymbolicIntegerArray):
                new_inputs.append(argument.to_concrete(model))
                continue
            concrete_value = model.evaluate(argument)
            if z3.is_int_value(concrete_value):
                new_inputs.append(concrete_value.as_long())
            elif z3.is_bool(concrete_value):
                new_inputs.append(z3.is_true(concrete_value))
            else:
                raise NotImplementedError(f"Unsupported z3 type {type(concrete_value)}")
        return new_inputs

    def find_all_paths(self, parent_node: str, inputs: list[Any], symbolic_state: SymbolicProgramState, concrete_state: ProgramState, path_constraints, max_branching_depth: int):
        if max_branching_depth == 0:
            return
        
        if len(self.test_cases) == self.requested_test_case_count:
            return

        if concrete_state.done:
            # we have reached the end of the program without raising an exception
            self.test_cases.append(inputs)
            return
        try:
            new_concrete_state, chosen_branch = self.concrete_interpreter.step_with_state(concrete_state)
        except InterpreterError:
            return
        possible_branches = self.symbolic_interpreter.step_with_state(symbolic_state)

        for i, branch in enumerate(possible_branches):
            new_symbolic_state, path_constraint = branch
            if i != chosen_branch:
                # we need to find a concrete state because we are not following the concrete execution
                new_path_constraints = path_constraints + [path_constraint]
                solver = z3.Solver()
                solver.add(new_path_constraints)
                result = solver.check()
                if result == z3.sat:
                    model = solver.model()
                elif result == z3.unsat:
                    continue
                elif result == z3.unknown:
                    continue
                else:
                    raise RuntimeError("Unexpected z3 result")
                print(f"Branching {new_symbolic_state}")
                old_inputs_dict = dict(zip(self.symbolic_arguments, inputs))
                extended_model_with_old_inputs = extend_model_with_inputs(solver, model, old_inputs_dict)
                new_inputs = self.evaluate_arguments_in_model(extended_model_with_old_inputs)
                extended_model_with_new_inputs = extend_model_with_inputs(solver, model, dict(zip(self.symbolic_arguments, new_inputs)))
                modified_concrete_state = new_symbolic_state.to_concrete_state(extended_model_with_new_inputs)
                new_parent_node = str(uuid4())
                self.dot.node(new_parent_node, label=f"Constraint: {path_constraint}, New inputs: {new_inputs}") # Symbolic State: {new_symbolic_state},
                self.dot.edge(parent_node, new_parent_node, label=f"Branch {path_constraint}")
                self.find_all_paths(new_parent_node, new_inputs, new_symbolic_state, modified_concrete_state, new_path_constraints, max_branching_depth - 1)
            else:
                # we can keep following the concrete execution because we have the concrete state from
                new_path_constraints = path_constraints + [path_constraint]
                if len(possible_branches) > 1:
                    # we decrease depth only if there are multiple branches
                    new_parent_node = str(uuid4())
                    self.dot.node(new_parent_node,
                                  label=f"Constraint: {path_constraint}") # Symbolic State: {new_symbolic_state},
                    self.dot.edge(parent_node, new_parent_node, label=f"chosen branch")
                    self.find_all_paths(new_parent_node, inputs, new_symbolic_state, new_concrete_state, new_path_constraints, max_branching_depth - 1)
                else:
                    # we do not decrease depth if there is only one branch
                    # because we want to explore all paths with at most max_depth branching points
                    self.find_all_paths(parent_node, inputs, new_symbolic_state, new_concrete_state, new_path_constraints, max_branching_depth)