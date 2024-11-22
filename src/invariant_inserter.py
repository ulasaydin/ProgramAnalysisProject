import ast

class InvariantInserter(ast.NodeTransformer):
    def __init__(self, invariants):
        self.invariants = invariants

    def insert_invariants_in_loop(self, loop_node):
        """Helper function to insert invariants below the existing ones in the loop body."""
        new_body = []
        existing_invariants = []

        # Separate existing invariants from the loop body
        for statement in loop_node.body:
            if isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Call) and getattr(statement.value.func, 'id', '') == "Invariant":
                existing_invariants.append(statement)
            else:
                new_body.append(statement)

        # Add original loop body after existing invariants
        updated_body = existing_invariants + new_body

        # Insert each new invariant after the existing ones
        for invariant in self.invariants:
            if invariant.startswith("Invariant(") and invariant.endswith(")"):
                invariant_content = invariant[len("Invariant("):-1] 
                try:
                 
                    parsed_invariant = ast.parse(f"Invariant({invariant_content})").body[0].value
                    updated_body.insert(len(existing_invariants), ast.Expr(value=parsed_invariant))
                except SyntaxError as e:
                    print(f"Skipping invalid invariant due to syntax error: {invariant}")
                    print(e)

        loop_node.body = updated_body
        return loop_node

    def visit_FunctionDef(self, node):
        # Modify each loop in the function body to include invariants
        for i, child in enumerate(node.body):
            if isinstance(child, (ast.For, ast.While)):
                node.body[i] = self.insert_invariants_in_loop(child)
        return node

def insert_invariants_in_ast(program_file_path, invariants, output_program_path):
    with open(program_file_path, "r") as file:
        program_ast = ast.parse(file.read())

    inserter = InvariantInserter(invariants)
    modified_ast = inserter.visit(program_ast)

    with open(output_program_path, "w") as file:
        file.write(ast.unparse(modified_ast))
