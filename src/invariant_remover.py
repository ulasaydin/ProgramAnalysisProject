from ast import NodeTransformer, fix_missing_locations

class InvariantRemover(NodeTransformer):
    def __init__(self, entry_point_function: str, invalid_invariant_line_number: int):
        self.entry_point_function = entry_point_function
        self.invalid_invariant_line_number = invalid_invariant_line_number
    
    def visit_While(self, node):
        print("Visiting While")
        new_body = []
        for stmt in node.body:
            if stmt.lineno != self.invalid_invariant_line_number:
                new_body.append(stmt)
            else:
                print(f"Removing invariant at line {self.invalid_invariant_line_number}")
        node.body = new_body
        return node

    def visit_FunctionDef(self, node):
        if node.name == self.entry_point_function:
            return self.generic_visit(node)
        else:
            return node
        
    def visit_Module(self, node):
        new_node = self.generic_visit(node)
        return fix_missing_locations(new_node)