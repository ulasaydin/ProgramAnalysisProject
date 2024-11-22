import re

def parse_all_daikon_invariants(daikon_output):

    invariants = []

    # Regex patterns for Daikon invariants
    orig_pattern = r"(\w+)\s*(==|!=|<=|>=|>|<)\s*orig\((\w+)\)"
    size_pattern = r"size\((\w+)\[\]\)"
    general_comparison_pattern = r"(\w+)\s*(==|!=|<=|>=|>|<)\s*(\w+|\d+)"
    subtraction_pattern = r"(\w+)\s*-\s*(\w+)\s*-\s*(\w+)\s*(==|!=|<=|>=|>|<)\s*([\w\d-]+)"
    has_only_one_value_pattern = r"(\w+)\s+has\s+only\s+one\s+value"

 
    def replace_size_and_null(line):
        line = re.sub(size_pattern, r"len(\1)", line)  
        line = line.replace("null", "None") 
        return line

    def is_valid_invariant(left, operator, right):
        if left.isdigit() and right.isdigit():
            return False  
        if left == right and operator in ["==", "<=", ">="]:
            return False  
        return True

    # Process the Daikon output line by line
    lines = [line.strip() for line in daikon_output.splitlines() if line.strip()]
    for line in lines:
        # Replace size(a[]) with len(a) and null with None
        line = replace_size_and_null(line)

        # Parse orig(x) patterns
        if re.search(orig_pattern, line):
            match = re.findall(orig_pattern, line)
            for var, operator, orig_var in match:
                invariants.append(f"Invariant({var} {operator} Old({orig_var}))")

        # Parse "has only one value"
        elif re.search(has_only_one_value_pattern, line):
            match = re.findall(has_only_one_value_pattern, line)
            for var in match:
                invariants.append(
                    f"Invariant(Forall(int i, Implies(0 <= i and i < len({var}), {var}[i] == {var}[0])))"
                )

        # Parse subtraction relationships
        elif re.search(subtraction_pattern, line):
            match = re.findall(subtraction_pattern, line)
            for var1, var2, var3, operator, value in match:
                invariants.append(f"Invariant({var1} - {var2} - {var3} {operator} {value})")

        # Parse general comparisons
        elif re.search(general_comparison_pattern, line):
            match = re.findall(general_comparison_pattern, line)
            for left, operator, right in match:
                if is_valid_invariant(left, operator, right):
                   
                    left = left.replace("len", "len(a)") if left == "len" else left
                    right = right.replace("len", "len(a)") if right == "len" else right
                    invariants.append(f"Invariant({left} {operator} {right})")

    # Remove duplicates
    unique_invariants = sorted(set(invariants))

    return unique_invariants
