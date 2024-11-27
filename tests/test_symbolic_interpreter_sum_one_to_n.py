import pytest
import z3

from src.interpreter import ProgramState
from src.symbolic_interpreter import SymbolicInterpreter, SymbolicProgramState
from tests.common import get_function_bytecode


def check_preconditions(n: int) -> None:
    if n < 0:
        raise RuntimeError('Precondition failed: n >= 0')

def sum_one_to_n(n: int) -> int:
    check_preconditions(n)
    i = 0
    sum = 0
    while i < n:
        i += 1
        sum += i
    return sum

env = {
    check_preconditions.__name__: get_function_bytecode(check_preconditions),
    sum_one_to_n.__name__: get_function_bytecode(sum_one_to_n)
}

interpreter = SymbolicInterpreter(
    env,
    sum_one_to_n.__name__
)

def test_sum_one_to_n():
    concrete_state = ProgramState.generate_program_state_from_arguments_and_bytecode(
        entry_point=sum_one_to_n.__name__,
        entry_point_function_bytecode=env[sum_one_to_n.__name__],
        arguments=[-1]
    )

    symbolic_state = SymbolicProgramState.generate_symbolic_state_from_arguments_and_bytecode(
        entry_point=sum_one_to_n.__name__,
        entry_point_function_bytecode=env[sum_one_to_n.__name__],
        symbolic_arguments=[z3.Int('n')]
    )

def test_sum_one_to_n_negative():
    pass