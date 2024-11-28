import ast
from dataclasses import dataclass
from math import e
import random
from typing import Any, Union
from uuid import uuid4
import graphviz
import dis
import z3
import sys
import os

from model_wrapper import ModelWrapper
from interpreter import InterpreterError
from interpreter import ProgramState, Python39Interpreter
from util import extend_model_with_heap, extend_model_with_inputs, extract_arguments_and_annotations, generate_random_value, test_case_from_inputs_and_heap, types_to_concrete_inputs_and_heap, types_to_symbolic_inputs_and_heap
from symbolic_interpreter import SymbolicInterpreter, SymbolicProgramState
from symbolic_integer_array import HeapReference, SymbolicIntegerArray


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
        self.symbolic_heap: dict[int, SymbolicIntegerArray] = {}
        self.dot: graphviz.Digraph = None

    def generate_test_cases(self, test_case_count) -> list[list[any]]:
        entry_point_function_ast, entry_point_function_bytecode = self.env[self.entry_point]
        arguments = extract_arguments_and_annotations(entry_point_function_ast)
        concrete_inputs, concrete_heap = types_to_concrete_inputs_and_heap(arguments)
        self.symbolic_arguments, self.symbolic_heap = types_to_symbolic_inputs_and_heap(arguments)
        initial_concrete_state = ProgramState.generate_program_state_from_arguments_and_bytecode(
            self.entry_point,
            entry_point_function_bytecode,
            concrete_inputs,
            concrete_heap
        )
        initial_symbolic_state = SymbolicProgramState.generate_symbolic_state_from_arguments_and_bytecode(
            self.entry_point,
            entry_point_function_bytecode,
            self.symbolic_arguments,
            self.symbolic_heap
        )
        root_name = str(uuid4())
        self.dot = graphviz.Digraph("concolic-tree")
        self.dot.node(root_name, label=f"Constraints: {[]}, Inputs: {concrete_inputs}, Heap: {concrete_heap}")
        self.requested_test_case_count = test_case_count
        self.test_cases = []
        print(f"Starting concolic execution with initial random inputs: {concrete_inputs} and heap: {concrete_heap}")
        self.find_all_paths(root_name, concrete_inputs, concrete_heap, initial_symbolic_state, initial_concrete_state, [], max_branching_depth=20)
        return self.test_cases

    def evaluate_arguments_in_model(self, model: ModelWrapper) -> list[tuple[str, Any]]:
        new_inputs = []
        for argument in self.symbolic_arguments:
            if isinstance(argument, HeapReference):
                new_inputs.append(argument)
                continue
            concrete_value = model.evaluate(argument)
            if z3.is_int_value(concrete_value):
                new_inputs.append(concrete_value.as_long())
            elif z3.is_true(concrete_value) or z3.is_false(concrete_value):
                new_inputs.append(z3.is_true(concrete_value))
            else:
                if z3.is_int(concrete_value):
                    random_value = generate_random_value('int')
                    new_inputs.append(random_value)
                    model.add(argument == random_value)
                elif z3.is_bool(concrete_value):
                    random_value = generate_random_value('bool')
                    new_inputs.append(random_value)
                    model.add(argument == random_value)
        return new_inputs
    
    def evaluate_heap_in_model(self, model: ModelWrapper, heap: dict[int, SymbolicIntegerArray]) -> dict[int, list[int]]:
        new_heap = {}
        for heap_ref in self.symbolic_heap.keys():
            heap_val = heap[heap_ref]
            new_heap[heap_ref] = heap_val.to_initial_state(model)
        return new_heap

    def find_all_paths(self, parent_node: str, inputs: list[Any], heap: dict[int, list[int]], symbolic_state: SymbolicProgramState, concrete_state: ProgramState, path_constraints, max_branching_depth: int):
        if max_branching_depth == 0:
            return
        
        if len(self.test_cases) == self.requested_test_case_count:
            return

        if concrete_state.done:
            #print("Found test case", inputs, heap)
            # we have reached the end of the program without raising an exception
            self.test_cases.append(test_case_from_inputs_and_heap(inputs, heap))
            return
        try:
            new_concrete_state, chosen_branch = self.concrete_interpreter.step_with_state(concrete_state)
        except InterpreterError:
            return
        possible_branches = self.symbolic_interpreter.step_with_state(symbolic_state)

        for i, branch in enumerate(possible_branches):
            new_symbolic_state, path_constraint = branch
            path_constraint_str = str(path_constraint)[:1000] #.replace('\n', '').replace('\'', '').replace('\"', '')
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
                #print(f"Branching {new_symbolic_state}")
                
                # merge the unused inputs with the model
                #old_inputs_dict = dict(zip(self.symbolic_arguments, inputs))
                #extended_model_with_all_inputs = extend_model_with_inputs(solver, model, old_inputs_dict)
                #new_initial_inputs = self.evaluate_arguments_in_model(extended_model_with_all_inputs)

                # merge the unused heap locations with the model
                #symbolic_to_concrete_heap = {symbolic_heap_ref.address: concrete_heap_ref.address for symbolic_heap_ref, concrete_heap_ref in old_inputs_dict.items() if isinstance(symbolic_heap_ref, HeapReference)}
                #extended_model_with_unused_heap = extend_model_with_heap(solver, extended_model_with_all_inputs, symbolic_to_concrete_heap, new_symbolic_state.heap, heap)
                #new_initial_heap = self.evaluate_heap_in_model(extended_model_with_unused_heap, new_symbolic_state.heap)

                # make the symbolic state concrete using the extended model
                m = ModelWrapper(model, solver)
                new_initial_inputs = self.evaluate_arguments_in_model(m)
                new_initial_heap = self.evaluate_heap_in_model(m, new_symbolic_state.heap)
                modified_concrete_state = new_symbolic_state.to_concrete_state(m)

                new_parent_node = str(uuid4())
                str
                self.dot.node(new_parent_node, label=f"Constraint: {path_constraint_str}, New inputs: {str(test_case_from_inputs_and_heap(new_initial_inputs, new_initial_heap))[:1000]}, Function Name: {modified_concrete_state.top_frame.function_name}, PC: {modified_concrete_state.top_frame.pc * 2}") # Symbolic State: {new_symbolic_state},
                self.dot.edge(parent_node, new_parent_node, label=f"Branch {path_constraint_str}")
                self.find_all_paths(new_parent_node, new_initial_inputs, new_initial_heap, new_symbolic_state, modified_concrete_state, new_path_constraints, max_branching_depth - 1)
            else:
                # we can keep following the concrete execution because we have the concrete state from
                new_path_constraints = path_constraints + [path_constraint]
                if len(possible_branches) > 1:
                    # we decrease depth only if there are multiple branches
                    new_parent_node = str(uuid4())
                    self.dot.node(new_parent_node,
                                  label=f"Constraint: {path_constraint_str}, Function Name: {new_concrete_state.top_frame.function_name}, PC: {new_concrete_state.top_frame.pc * 2}") # Symbolic State: {new_symbolic_state},
                    self.dot.edge(parent_node, new_parent_node, label=f"chosen branch")
                    self.find_all_paths(new_parent_node, inputs, heap, new_symbolic_state, new_concrete_state, new_path_constraints, max_branching_depth - 1)
                else:
                    # we do not decrease depth if there is only one branch
                    # because we want to explore all paths with at most max_depth branching points
                    self.find_all_paths(parent_node, inputs, heap, new_symbolic_state, new_concrete_state, new_path_constraints, max_branching_depth)