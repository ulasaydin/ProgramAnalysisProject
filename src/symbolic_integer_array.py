from dataclasses import dataclass
import random
from typing import Union
import z3

class SymbolicIntegerArray:
    def __init__(self, name: str):
        self.__name: str = name
        self.__length: z3.ArithRef = z3.Int(f"{name}_length")
        self.__array: dict[z3.ArithRef, z3.ArithRef] = {}
        self.variables: dict[z3.ArithRef, z3.ArithRef] = {}

    def __getitem__(self, i: Union[int, z3.IntNumRef]):
        i = z3.simplify(i) if z3.is_expr(i) else i
        if i not in self.__array:
            v = z3.Int(f"{self.__name}_{i}")
            self.variables[i] = v
            self.__array[i] = v
        return self.__array[i]

    def __setitem__(self, i: Union[int, z3.ArithRef], v):
        i = z3.simplify(i) if z3.is_expr(i) else i
        self.__array[i] = z3.simplify(v) if z3.is_expr(v) else v

    def length(self):
        return self.__length

    def __repr__(self):
        return f"SymbolicIntegerArray({self.__name}, {self.__length}, {self.__array}, {self.variables})"

    def to_concrete(self, model: z3.ModelRef):
        l = model.evaluate(self.__length)
        if z3.is_int_value(l):
            l = l.as_long()
        else:
            l = random.randint(0, 10)
        # we do not support support append so array is static and initial length is exactly the same as l
        res = [random.randint(-100, 100) for i in range(l)]
        for i, v in self.__array.items():
            if z3.is_expr(i):
                i = model.evaluate(i)
                if z3.is_int_value(i):
                    i = i.as_long()
                else:
                    continue
            e = model.evaluate(v)
            if z3.is_int_value(e):
                res[i] = e.as_long()
            else:
                continue
        return res
    
    def to_initial_state(self, model: z3.ModelRef):
        #print(model)
        l = model.evaluate(self.__length)
        if z3.is_int_value(l):
            l = l.as_long()
        else:
            l = random.randint(0, 10)
        # we do not support support append so array is static and initial length is exactly the same as l
        res = [random.randint(-100, 100) for i in range(l)]
        for i, v in self.variables.items():
            #print(i, v)
            if z3.is_expr(i):
                i = model.evaluate(i)
                if z3.is_int_value(i):
                    i = i.as_long()
                else:
                    continue
            e = model.evaluate(v)
            if z3.is_int_value(e):
                res[i] = e.as_long()
            else:
                continue
        return res
    
@dataclass
class HeapReference:
    address: int

    def __hash__(self):
        return hash(self.address)