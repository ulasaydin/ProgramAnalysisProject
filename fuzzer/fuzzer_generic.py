import random
import sys
import os
import copy

sys.path.append(os.path.join(os.path.dirname(__file__), "../converted"))

def fuzzer_generic(target_function, num_cases=10, input_gen_func=None, 
                   expected_value_func=None, expected_iterations_func=None, loop_line_offset=None, check_in_place=False):
    """
    A generalized fuzzer to test functions with specific preconditions and loop-based behavior.

    Args:
        target_function: The function to be tested.
        num_cases: Number of test cases to generate.
        input_gen_func: A callable to generate unique test inputs.
        expected_value_func: A callable to compute the expected returned value based on input.
        expected_iterations_func: A callable to compute the expected iteration count based on input.
        loop_line_offset: Line number offset where the loop starts within the function.
        check_in_place: Boolean indicating if the function modifies its input in-place.
    Returns:
        None; prints test case results.
        TODO: Add support for functions that modify input in-place.
        TODO: Edit returns to return results in a Daikon needed format.
    """
    results = []
    generated_values = set()  # To keep track of unique input values

    def trace_loop_count(frame, event, arg):
        """Tracing function to count loop iterations."""
        nonlocal iteration_count
        # Check if we're in the target function's loop line
        if frame.f_code.co_name == target_function.__name__ and frame.f_lineno == loop_line:
            if event == 'line':
                iteration_count += 1
        return trace_loop_count

    while len(results) < num_cases:
        # Generate a unique input value
        input_value = input_gen_func()
        input_value_beginning = copy.deepcopy(input_value) if check_in_place else input_value
        input_value_hashable = tuple(input_value[0]) if check_in_place and isinstance(input_value[0], list) else tuple(input_value) if isinstance(input_value, list) else input_value

        # if check_in_place:
        #     input_value_beginning = copy.deepcopy(input_value)
        #     input_value_hashable = tuple(input_value[0]) if isinstance(input_value[0], list) else input_value
        # else:
        #     input_value_hashable = tuple(input_value) if isinstance(input_value, list) else input_value
            
        if input_value_hashable in generated_values:
            continue
        generated_values.add(input_value_hashable)
        
        # Calculate the expected returned value using the provided function
        expected_returned_value = expected_value_func(input_value)
        iterations_expected = expected_iterations_func(input_value)

        # Tracking loop iteration count
        iteration_count = 0
        loop_line = target_function.__code__.co_firstlineno + loop_line_offset  # Set the correct loop line

        # Set the trace and call the target function
        sys.settrace(trace_loop_count)
        if check_in_place:
            target_function(*input_value)
            returned_value = input_value[0]
        else:
            returned_value = target_function(input_value)
        sys.settrace(None)  # Stop tracing

        # Check if the function output meets the expected result
        passes_returned_value = returned_value == expected_returned_value
        passes_iterations = iteration_count == iterations_expected
        # if check_in_place:
        #     iterations_expected = len(input_value[0]) if isinstance(input_value[0], list) else input_value
        #     passes_iterations = iteration_count == (len(input_value[0]) if isinstance(input_value[0], list) else input_value)
        # else:
        #     iterations_expected = len(input_value) if isinstance(input_value, list) else input_value,
        #     iterations_expected = iterations_expected[0] if isinstance(iterations_expected, tuple) else iterations_expected
        #     passes_iterations = iteration_count == (len(input_value) if isinstance(input_value, list) else input_value)

        
        # Record the test case results
        results.append({
            "input_value": input_value_beginning if check_in_place else input_value,
            "expected_returned_value": expected_returned_value,
            "returned_value": returned_value,
            "iterations_expected": iterations_expected,
            "iterations_actual": iteration_count,
            "pass_returned_value": passes_returned_value,
            "pass_iterations": passes_iterations,
            "overall_pass": passes_returned_value and passes_iterations
        })

    # Print results for each test case
    for idx, result in enumerate(results, 1):
        print(f"Test Case {idx}:")
        print(f"  Input Value = {result['input_value']}")
        print(f"  Expected Returned Value = {result['expected_returned_value']}, Returned Value = {result['returned_value']}")
        print(f"  Expected Iterations = {result['iterations_expected']}, Actual Iterations = {result['iterations_actual']}")
        print(f"  Returned Value Pass: {result['pass_returned_value']}")
        print(f"  Iterations Pass: {result['pass_iterations']}")
        print(f"  Overall Test Pass: {result['overall_pass']}\n")

# Usage with sum_one_to_n function
from sum_one_to_n import sum_one_to_n  # Import the sum_one_to_n function
from min_array import min_list  # Import the min_list function
from max_array import max_list  # Import the max_list function
from sum_array import sum_list  # Import the sum_list function
from arrays_fill_a import fill_a  # Import the fill_a function
from arrays_fill_b import fill_b  # Import the fill_b function

# Define input generator, expected value function, and loop line offset for sum_one_to_n
input_gen_sum = lambda: random.randint(0, 100)
expected_value_sum = lambda n: n * (n + 1) // 2
loop_line_offset_sum = 8  # Adjust to the line where `while` is located in sum_one_to_n
expected_iterations_sum = lambda n: n

fuzzer_generic(sum_one_to_n, input_gen_func=input_gen_sum, expected_value_func=expected_value_sum, expected_iterations_func=expected_iterations_sum, loop_line_offset=loop_line_offset_sum)

# Define input generator, expected value function, and loop line offset for min_list
input_gen_min_list = lambda: [random.randint(-100, 100) for _ in range(random.randint(1, 10))]
expected_value_min_list = lambda xs: min(xs)
loop_line_offset_min_list = 11  # Adjust to the line where `while` is located in min_list
expected_iterations_min_list = lambda xs: len(xs)

fuzzer_generic(min_list, input_gen_func=input_gen_min_list, expected_value_func=expected_value_min_list, expected_iterations_func=expected_iterations_min_list,loop_line_offset=loop_line_offset_min_list)

# Define input generator, expected value function, and loop line offset for max_list
input_gen_max_list = lambda: [random.randint(-100, 100) for _ in range(random.randint(1, 10))]
expected_value_max_list = lambda xs: max(xs)
loop_line_offset_max_list = 11  # Adjust to the line where `while` is located in max_list
expected_iterations_max_list = lambda xs: len(xs)

fuzzer_generic(max_list, input_gen_func=input_gen_max_list, expected_value_func=expected_value_max_list, expected_iterations_func=expected_iterations_max_list,loop_line_offset=loop_line_offset_max_list)

# Define input generator, expected value function, and loop line offset for sum_list
input_gen_sum_list = lambda: [random.randint(-100, 100) for _ in range(random.randint(1, 10))]
expected_value_sum_list = lambda xs: sum(xs)
loop_line_offset_sum_list = 14  # Adjust to the line where `while` is located in sum_list
expected_iterations_sum_list = lambda xs: len(xs)

fuzzer_generic(sum_list, input_gen_func=input_gen_sum_list, expected_value_func=expected_value_sum_list, expected_iterations_func=expected_iterations_sum_list, loop_line_offset=loop_line_offset_sum_list)

input_gen_fill_a = lambda: ([random.randint(-100, 100) for _ in range(random.randint(1, 10))], random.randint(-100, 100))
# input_gen_fill_a = lambda: ([0] * random.randint(1, 10), random.randint(-100, 100))
expected_value_fill_a = lambda input: [input[1]] * len(input[0])
loop_line_offset_fill_a = 10  # Adjust to the line where `while` is located in fill_a
expected_iterations_fill_a = lambda input: len(input[0])

fuzzer_generic(fill_a, input_gen_func=input_gen_fill_a, expected_value_func=expected_value_fill_a, expected_iterations_func=expected_iterations_fill_a, loop_line_offset=loop_line_offset_fill_a, check_in_place=True)

input_gen_fill_b = lambda: (
    array := [random.randint(-100, 100) for _ in range(random.randint(5, 15))],  
    random.randint(0, len(array) - 1), 
    random.randint(0, len(array) - 1),  
    random.randint(-100, 100) 
)
expected_value_fill_b = lambda input: [input[3] if input[1] <= i < input[2] else x for i, x in enumerate(input[0])]
loop_line_offset_fill_b = 14  
expected_iterations_fill_b = lambda input: max(0, input[2] - input[1])  

fuzzer_generic(fill_b, input_gen_func=input_gen_fill_b, expected_value_func=expected_value_fill_b, expected_iterations_func=expected_iterations_fill_b, loop_line_offset=loop_line_offset_fill_b, check_in_place=True)