import re

# Patterns for different invariant types without "orig"
scalar_pattern = r"(\w+)\s*==\s*post\(\1\)"  # a == post(a)
non_zero_pattern = r"(\w+)\s*!=\s*0"  # x != 0
mod_pattern = r"(\w+)\s*!=\s*(\w+)\s*\(mod\s*(\d+)\)"  # x != r (mod m)
equality_pattern = r"(\w+\[\])\s*==\s*(\w+\[\])"  # a[] == b[]
greater_than_pattern = r"(\w+)\s*>\s*(\w+)"  # a > b
less_than_pattern = r"(\w+)\s*<\s*(\w+)"  # a < b
logical_pattern = r"(\w+)\s*(==|!=|>=|<=|>|<)\s*(\w+)"  # x == y or x != y or x > y 
one_of_pattern = r"(\w+)\s*one\s*of\s*\{([0-9, ]+)\}"  # n one of {5, 10}
sum_pattern = r"(\w+)\s*-\s*(\w+)\s*-\s*(\w+)\s*([=!><]+)\s*(\d+)"  # sum - i - j == 0
single_value_pattern = r"(\w+)\s+has\s+only\s+one\s+value"  # Pattern for single unique value

def parse_daikon_output(daikon_output_content):
    invariants = []

    daikon_output_content = re.sub(r"size\((\w+)\[\]\)", r"len(\1)", daikon_output_content)

    # Scalar invariants without "orig"
    for match in re.finditer(scalar_pattern, daikon_output_content):
        invariants.append(f"Invariant({match.group(1)} == Result())")

    # Non-zero invariants
    for match in re.finditer(non_zero_pattern, daikon_output_content):
        invariants.append(f"Invariant({match.group(1)} != 0)")

    # Modulus invariants
    for match in re.finditer(mod_pattern, daikon_output_content):
        invariants.append(f"Invariant({match.group(1)} != {match.group(2)} % {match.group(3)})")

    # Equality of arrays
    for match in re.finditer(equality_pattern, daikon_output_content):
        invariants.append(f"Invariant({match.group(1)} == {match.group(2)})")

    # Greater-than comparisons
    for match in re.finditer(greater_than_pattern, daikon_output_content):
        if "orig" not in match.group(0):  # Exclude invariants with "orig"
            invariants.append(f"Invariant({match.group(1)} > {match.group(2)})")

    # Less-than comparisons
    for match in re.finditer(less_than_pattern, daikon_output_content):
        if "orig" not in match.group(0):  # Exclude invariants with "orig"
            invariants.append(f"Invariant({match.group(1)} < {match.group(2)})")

    # Logical expressions without "orig"
    for match in re.finditer(logical_pattern, daikon_output_content):
        if "orig" not in match.group(0):  # Exclude invariants with "orig"
            invariants.append(f"Invariant({match.group(1)} {match.group(2)} {match.group(3)})")

    # "One of" invariants (e.g., n one of {5, 10})
    for match in re.finditer(one_of_pattern, daikon_output_content):
        values = match.group(2).split(', ')
        invariants.append(f"Invariant({match.group(1)} one of {{{', '.join(values)}}})")

    # Sum and difference invariants without "orig"
    for match in re.finditer(sum_pattern, daikon_output_content):
        if "orig" not in match.group(0):  # Exclude invariants with "orig"
            invariants.append(f"Invariant({match.group(1)} - {match.group(2)} - {match.group(3)} {match.group(4)} {match.group(5)})")

    # Check for "has only one value" pattern
    for match in re.finditer(single_value_pattern, daikon_output_content):
        variable = match.group(1)
        invariants.append(f"Invariant(Forall(int i, Implies(0 <= i and i < len({variable}), {variable}[i] == {variable}[0])))")

    # Remove duplicates
    unique_invariants = list(set(invariants))

    # Filter out any invariants containing "orig"
    filtered_invariants = [inv for inv in unique_invariants if "orig" not in inv]
    
    return filtered_invariants
