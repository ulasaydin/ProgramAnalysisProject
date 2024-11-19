import ast
from dataclasses import dataclass
from tabnanny import verbose
from typing import Any
from uuid import uuid4

import graphviz
import dis
import z3
import sys
import os

sys.path.append(os.path.dirname(__file__))

from interpreter import InterpreterError
from interpreter import ProgramState, Python39Interpreter
from util import extract_parameter_names
from util import extract_parameter_types, function_initial_locals_from_inputs, generate_random_value
from symbolic_interpreter import SymbolicInterpreter, SymbolicProgramState


@dataclass
class ConcolicTestCaseGenerator:
    def __init__(self, env: dict[str, tuple[ast.FunctionDef, dis.Bytecode]], entry_point: str):
        self.env: dict[str, tuple[ast.FunctionDef, dis.Bytecode]] = env
        self.entry_point: str = entry_point
        interpreter_env = { function_name : function_bytecode for function_name, (_, function_bytecode) in self.env.items() }
        self.concrete_interpreter = Python39Interpreter(interpreter_env, self.entry_point)
        self.symbolic_interpreter = SymbolicInterpreter(interpreter_env, self.entry_point)
        self.test_cases: list[list[Any]] = []
        self.symbolic_arguments: list[z3.ExprRef] = []
        self.dot = graphviz.Digraph("concolic-tree")

    def generate_test_cases(self, initial_inputs = None, max_branching_points = 50) -> list[list[any]]:
        entry_point_function_ast, entry_point_function_bytecode = self.env[self.entry_point]
        parameter_types = extract_parameter_types(entry_point_function_ast)
        parameter_names = extract_parameter_names(entry_point_function_ast)
        random_inputs = initial_inputs if initial_inputs else [generate_random_value(param_type) for param_type in parameter_types]
        self.symbolic_arguments = self.types_to_symbolic_inputs(parameter_names, parameter_types)
        initial_concrete_state = ProgramState(
            self.entry_point,
            function_initial_locals_from_inputs(entry_point_function_bytecode, random_inputs))
        initial_symbolic_state = SymbolicProgramState(
            self.entry_point,
            function_initial_locals_from_inputs(entry_point_function_bytecode,
                                                self.symbolic_arguments)
        )
        root_name = str(uuid4())
        self.dot.node(root_name, label=f"Constraints: {[]}, Inputs: {random_inputs}")
        self.find_all_paths_with_max_branching_points(root_name, random_inputs, initial_symbolic_state, initial_concrete_state, [], max_branching_points)
        return self.test_cases

    def types_to_symbolic_inputs(self, names: list[str], types: list[str]):
        symbolic_inputs = []
        for name, typ in zip(names, types):
            if typ == "int":
                symbolic_inputs.append(z3.Int(name))
            elif typ == "bool":
                symbolic_inputs.append(z3.Bool(name))
            else:
                raise NotImplementedError(f"Unsupported type {typ}")
        return symbolic_inputs

    def evaluate_arguments_in_model(self, model: z3.ModelRef) -> list[Any]:
        new_inputs = []
        for argument in self.symbolic_arguments:
            concrete_value = model[argument]
            if isinstance(concrete_value, z3.IntNumRef):
                new_inputs.append(concrete_value.as_long())
            elif isinstance(concrete_value, z3.BoolRef):
                new_inputs.append(z3.is_true(concrete_value))
            else:
                raise NotImplementedError(f"Unsupported z3 type {type(concrete_value)}")
        return new_inputs

    def find_all_paths_with_max_branching_points(self, parent_node: str, inputs: list[Any], symbolic_state: SymbolicProgramState, concrete_state: ProgramState, path_constraints, max_branching_points: int):
        if max_branching_points < 0:
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
                modified_concrete_state = new_symbolic_state.to_concrete_state(model)
                new_inputs = self.evaluate_arguments_in_model(model)
                new_parent_node = str(uuid4())
                self.dot.node(new_parent_node, label=f"Concrete State: {modified_concrete_state}, Symbolic State: {new_symbolic_state}, Constraint: {path_constraint}, New inputs: {new_inputs}")
                self.dot.edge(parent_node, new_parent_node, label=f"Branch {path_constraint}")
                self.find_all_paths_with_max_branching_points(new_parent_node, new_inputs, new_symbolic_state, modified_concrete_state, new_path_constraints, max_branching_points - 1)
            else:
                # we can keep following the concrete execution because we have the concrete state from
                new_parent_node = str(uuid4())
                self.dot.node(new_parent_node, label=f"Concrete State: {new_concrete_state}, Symbolic State: {new_symbolic_state}, Constraint: {path_constraint}")
                self.dot.edge(parent_node, new_parent_node, label=f"chosen branch")
                new_path_constraints = path_constraints + [path_constraint]
                if len(possible_branches) > 1:
                    # we decrease depth only if there are multiple branches
                    self.find_all_paths_with_max_branching_points(new_parent_node, inputs, new_symbolic_state, new_concrete_state, new_path_constraints, max_branching_points - 1)
                else:
                    # we do not decrease depth if there is only one branch
                    # because we want to explore all paths with at most max_depth branching points
                    self.find_all_paths_with_max_branching_points(new_parent_node, inputs, new_symbolic_state, new_concrete_state, new_path_constraints, max_branching_points)