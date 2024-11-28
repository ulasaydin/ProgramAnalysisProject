from dataclasses import dataclass
import random
from typing import Union
import z3

from model_wrapper import ModelWrapper

class SymbolicIntegerArray:
    def __init__(self, name: str):
        self.__name: str = name
        self.__length: z3.ArithRef = z3.Int(f"{name}_length")
        self.__initial_array: z3.ArrayRef = z3.Array(f"{name}_array", z3.IntSort(), z3.IntSort())
        self.__array: z3.ArrayRef = self.__initial_array

    def __getitem__(self, i: Union[int, z3.IntNumRef]):
        return z3.Select(self.__array, z3.simplify(i) if z3.is_expr(i) else i)

    def __setitem__(self, i: Union[int, z3.ArithRef], v):
        i = z3.simplify(i) if z3.is_expr(i) else i
        v = z3.simplify(v) if z3.is_expr(v) else v
        self.__array = z3.Store(self.__array, i, v)

    def length(self):
        return self.__length

    def __repr__(self):
        return f"SymbolicIntegerArray({self.__name}, {self.__length}, {self.__array})"

    def to_concrete(self, model: ModelWrapper):
        l = model.evaluate(self.__length)
        if z3.is_int_value(l):
            l = l.as_long()
        else:
            l = random.randint(0, 10)
            model.add(self.__length == l)

        res = [random.randint(-100, 100) for i in range(l)]
        for i in range(l):
            e = model.evaluate(z3.Select(self.__array, i))
            if z3.is_int_value(e):
                res[i] = e.as_long()
            else:
                model.add(z3.Select(self.__array, i) == res[i])
                continue
        return res
    
    def to_initial_state(self, model: ModelWrapper):
        l = model.evaluate(self.__length)
        if z3.is_int_value(l):
            l = l.as_long()
        else:
            l = random.randint(0, 10)
            model.add(self.__length == l)
        res = [random.randint(-100, 100) for i in range(l)]
        for i in range(l):
            e = model.evaluate(z3.Select(self.__initial_array, i))
            if z3.is_int_value(e):
                res[i] = e.as_long()
            else:
                model.add(z3.Select(self.__initial_array, i) == res[i])
                continue
        return res
    
@dataclass
class HeapReference:
    address: int

    def __hash__(self):
        return hash(self.address)