import z3

class SymbolicIntegerArray:
    def __init__(self, name: str):
        self.__name: str = name
        self.__length: z3.ArithRef = z3.Int(f"{name}_length")
        self.__array: dict[int, z3.ArithRef] = {}
        self.__variables: dict[int, z3.ArithRef] = {}

    def __getitem__(self, i: int):
        i = z3.simplify(i) if z3.is_expr(i) else i
        if i not in self.__array:
            v = z3.Int(f"{self.__name}_{i}")
            self.__variables[i] = v
            self.__array[i] = v
        return self.__array[i]

    def __setitem__(self, i, v):
        i = z3.simplify(i) if z3.is_expr(i) else i
        self.__array[i] = z3.simplify(v) if z3.is_expr(v) else v

    def length(self):
        return self.__length

    def __repr__(self):
        return f"SymbolicIntegerArray({self.__name}, {self.__length}, {self.__array})"

    def to_concrete(self, model: z3.ModelRef):
        l = model.evaluate(self.__length)
        if z3.is_int_value(l):
            l = l.as_long()
        else:
            l = 0
        # we do not support support append so array is static and initial length is exactly the same as l
        res = []
        for i in range(l):
            if i in self.__array:
                print(f"evaluating {self.__array[i]}")
                res.append(model.evaluate(self.__array[i]).as_long())
            else:
                res.append(0)
        return res