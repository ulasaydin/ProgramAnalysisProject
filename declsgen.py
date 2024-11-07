import ast
import os
import sys


class DeclGenerator(ast.NodeVisitor):
    def __init__(self):
        self.decls_content = ""
        self.decls_content += "decl-version 2.0\n"
        self.enter_vars = []
        self.exit_vars = []

    def visit_FunctionDef(self, node):
        # Define function entry point
        self.decls_content += f"ppt {node.name}:::ENTER\n"

        # Process function arguments
        for arg in node.args.args:
            arg_type = "unknown"  # Default if no type hint is provided
            if arg.annotation:
                arg_type = self.get_type_from_annotation(arg.annotation)
            self.add_variable_entry(arg.arg, "variable", arg_type, "ENTER")

        for enter_var in self.enter_vars:
            self.decls_content += enter_var

        # Add newline
        self.decls_content += "\n"

        # Define the function exit point
        self.decls_content += f"ppt {node.name}:::EXIT\n"

        # Traverse body to find local variables and the return statement
        local_vars = set()
        return_type = "unknown"

        for stmt in ast.walk(node):
            if isinstance(stmt, ast.Assign):  # Assignments (local variables)
                for target in stmt.targets:
                    if isinstance(target, ast.Name):
                        var_type = self.get_type_from_value(stmt.value)
                        self.add_variable_entry(target.id, "variable", var_type, "EXIT")
                        local_vars.add(target.id)
            elif isinstance(stmt, ast.Return):  # Return statement
                return_type = self.get_type_from_value(stmt.value)
                self.add_variable_entry("return", "return", return_type, "EXIT")

        for enter_var in self.enter_vars:
            self.decls_content += enter_var
        for exit_var in self.exit_vars:
            self.decls_content += exit_var

    def get_type_from_annotation(self, annotation):
        """Converts annotation node to a type name."""
        if isinstance(annotation, ast.Name):
            return annotation.id  # e.g., "int", "str"
        elif isinstance(annotation, ast.Subscript):
            base_type = annotation.value.id
            if isinstance(annotation.slice, ast.Index) and isinstance(
                annotation.slice.value, ast.Name
            ):
                sub_type = annotation.slice.value.id
                return f"{base_type}[{sub_type}]"
        return "unknown"

    def get_type_from_value(self, value):
        """Infers the type from an assignment's value."""
        if isinstance(value, ast.Constant):
            return type(value.value).__name__  # `int`, `str`, etc.
        elif isinstance(value, ast.List):
            return "list"
        elif isinstance(value, ast.Dict):
            return "dict"
        elif isinstance(value, ast.NameConstant):
            return type(value.value).__name__ if value.value is not None else "NoneType"
        elif isinstance(value, ast.BinOp) and isinstance(
            value.op, (ast.Add, ast.Sub, ast.Mult, ast.Div)
        ):
            # Assume arithmetic operations result in int or float
            return (
                "int"
                if all(
                    isinstance(operand, ast.Constant) and isinstance(operand.value, int)
                    for operand in [value.left, value.right]
                )
                else "float"
            )
        return "unknown"

    def add_variable_entry(self, name, kind, dec_type, ppt):
        var_props = ""
        """Adds a variable entry to the decls content."""
        var_props += f"  variable {name}\n"
        var_props += f"    var-kind {kind}\n"
        var_props += f"    dec-type {dec_type}\n"
        var_props += f"    rep-type {dec_type}\n"
        var_props += "    comparability 5\n"  # Using a default comparability value
        if ppt == "ENTER":
            self.enter_vars.append(var_props)
        elif ppt == "EXIT":
            self.exit_vars.append(var_props)

    def generate_decls(self, filename):
        """Parse a Python file and generate decls content."""
        with open(filename, "r") as file:
            lines = file.readlines()
            filtered_lines = [
                line
                for line in lines
                if not any(
                    line.strip().startswith(keyword)
                    for keyword in ["Requires", "Ensures", "Invariant", "Assert"]
                )
            ]
            tree = ast.parse("".join(filtered_lines))
            self.visit(tree)
        return self.decls_content


# Usage
generator = DeclGenerator()

if len(sys.argv) != 2:
    print("Usage: python declsgen.py <filename.py>")
    sys.exit(1)

filename = sys.argv[1]
decls_content = generator.generate_decls(filename)

with open(f"{os.path.splitext(filename)[0]}.decls", "w") as decls_file:
    decls_file.write(decls_content)

print(f"`{os.path.splitext(filename)[0]}.decls` file generated successfully.")
