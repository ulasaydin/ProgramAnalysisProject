import ast

class InvariantInserter(ast.NodeTransformer):
    def __init__(self, invariants):
        self.invariants = invariants

    def insert_invariants_in_loop(self, loop_node):
        """Helper function to insert invariants at the start of a loop body."""
        new_body = []
        # Insert each invariant as an expression at the beginning of the loop's body
        for invariant in self.invariants:
            if invariant.startswith("Invariant(") and invariant.endswith(")"):
                invariant_content = invariant[len("Invariant("):-1]  # Extract content inside Invariant(...)
                try:
                    # Parse it as a function call to Invariant with the content as the argument
                    parsed_invariant = ast.parse(f"Invariant({invariant_content})").body[0].value
                    new_body.append(ast.Expr(value=parsed_invariant))
                except SyntaxError as e:
                    print(f"Skipping invalid invariant due to syntax error: {invariant}")
                    print(e)

        # Add the original loop body after the invariants
        new_body.extend(loop_node.body)
        loop_node.body = new_body
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
