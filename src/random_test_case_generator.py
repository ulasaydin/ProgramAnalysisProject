import random
import ast
from typing import Any, List, Dict
from dataclasses import dataclass

@dataclass
class RandomTestCaseGenerator:
    env: Dict[str, ast.FunctionDef]
    entry_point: str
    verbose: bool = True

    def generate_random_test_cases(self) -> List[List[Any]]:
        """
        Generate 10 valid random test cases based on preconditions.

        Returns:
            List[List[Any]]: A list of 10 valid test cases for the specified function.
        """
        test_cases = []
        function_ast = self.env.get(self.entry_point)

        if function_ast:
            parameter_types = self.extract_parameter_types(function_ast)
            valid_case_count = 0

            # Generate random test cases until we have 10 valid ones
            while valid_case_count < 10:
                test_case = [self.generate_random_value(param_type) for param_type in parameter_types]

                if self.verbose:
                    print(f"Generated test case: {test_case}")

                if self.is_valid_test_case(test_case):
                    test_cases.append(test_case)
                    valid_case_count += 1
                    if self.verbose:
                        print(f"Valid test case #{valid_case_count}: {test_case}")
                else:
                    if self.verbose:
                        print(f"Invalid test case discarded: {test_case}")

        if self.verbose:
            print("Finished generating 10 valid test cases.")
        return test_cases

    def extract_parameter_types(self, function_ast: ast.FunctionDef) -> List[str]:
        parameter_types = []
        for arg in function_ast.args.args:
            if isinstance(arg.annotation, ast.Name):
                parameter_types.append(arg.annotation.id)
            elif isinstance(arg.annotation, ast.Subscript):
                if isinstance(arg.annotation.value, ast.Name) and arg.annotation.value.id == "list":
                    element_type = arg.annotation.slice.id if isinstance(arg.annotation.slice, ast.Name) else "Any"
                    parameter_types.append(f"list[{element_type}]")
            else:
                parameter_types.append("Any")
        if self.verbose:
            print(f"Extracted parameter types for {self.entry_point}: {parameter_types}")
        return parameter_types

    def generate_random_value(self, param_type: str) -> Any:
        value = None
        if param_type == "int":
            value = random.randint(-100, 100)
        elif param_type == "float":
            value = random.uniform(-100.0, 100.0)
        elif param_type == "str":
            value = ''.join(random.choices("abcdefghijklmnopqrstuvwxyz", k=random.randint(1, 10)))
        elif param_type == "bool":
            value = random.choice([True, False])
        elif param_type.startswith("list"):
            inner_type = param_type[5:-1]
            value = [self.generate_random_value(inner_type) for _ in range(random.randint(1, 10))]
        if self.verbose:
            print(f"Generated random value for type {param_type}: {value}")
        return value

    def is_valid_test_case(self, test_case: List[Any]) -> bool:
        """
        Calls check_preconditions with the test case to verify validity.

        Args:
            test_case (List[Any]): The generated input parameters for the function.

        Returns:
            bool: True if the test case satisfies the preconditions, False otherwise.
        """
        try:
            local_context = {}
            
            # Load all functions from `self.env` into `local_context`
            for name, func_ast in self.env.items():
                print(f"Loading function {name} into local context")
                function_code = ast.unparse(func_ast)
                exec(function_code, local_context)
            
            # Check if `check_preconditions` exists in `self.env`
            if "check_preconditions" in local_context:
                if self.verbose:
                    print(f"Checking preconditions with: {test_case}")

                # Call `check_preconditions` to validate input
                eval(f"check_preconditions(*{test_case})", local_context)
                return True
            else:
                return True  # If `check_preconditions` is not defined, accept the test case

        except Exception as e:
            if self.verbose:
                print(f"Error encountered for test case {test_case}: {e}")
            return False