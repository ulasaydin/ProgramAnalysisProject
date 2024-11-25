import z3


class SymbolicIntegerArray:
    def __init__(self, name: str):
        self.name: str = name
        self.length: z3.ArithRef = z3.IntVal(0)
        self.array: z3.ArrayRef = z3.Array(name, z3.IntSort(), z3.IntSort())

    def __getitem__(self, i):
        return z3.Select(self.array, i)

    def __setitem__(self, i, v):
        self.array = z3.Store(self.array, i, v)
        self.length = z3.If(i > self.length, i, self.length)