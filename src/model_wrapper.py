from dataclasses import dataclass
import z3


@dataclass
class ModelWrapper:
    model: z3.ModelRef
    solver: z3.Solver

    def add(self, e):
        self.solver.add(e)
        self.solver.check()
        self.model = self.solver.model()
    
    def evaluate(self, e):
        return self.model.evaluate(e)