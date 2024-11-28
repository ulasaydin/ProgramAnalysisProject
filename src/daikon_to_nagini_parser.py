import re

def parse_daikon_output(daikon_output):
    invariants = []

    def process_line(line):
   
        line = re.sub(r"(Old\(\w+\))\s*\*\*\s*(\d+)", r"\1 * \1", line)  
        line = re.sub(r"(\w+)\s*\*\*\s*(\d+)", r"\1 * \1", line) 

        # Handle cases like `a[] == orig(a[])` and convert it to Forall...
        if re.search(r"\w+\[\] == orig\(\w+\[\]\)", line):
            match = re.match(r"(\w+)\[\] == orig\((\w+)\[\]\)", line)
            if match:
                array_name = match.group(1)
                return f"Forall(int, lambda i: Implies(0 <= i and i < len({array_name}), {array_name}[i] == Old({array_name}[i])))"

        # Handle cases like `a == orig(a)` and convert it to Old(a)
        if re.search(r"\w+ == orig\(\w+\)", line):
            match = re.match(r"(\w+) == orig\((\w+)\)", line)
            if match:
                return f"Invariant({match.group(1)} == Old({match.group(1)}))"

        # Handle "one of {}" and convert it to or conditions
        if "one of {" in line:
            match = re.search(r"(\w+)\s+one\s+of\s+\{(.+?)\}", line)
            if match:
                variable = match.group(1)
                values = match.group(2).split(",")
                values = [value.strip() for value in values]
                conditions = " or ".join(f"{variable} == {value}" for value in values)
                return f"Invariant({conditions})"

        # Handle "has only one value"
        if "has only one value" in line:
            if not line.startswith("Invariant("):
                return f"Invariant({line.strip()})"

        # Replace `orig()` with `Old()`
        line = line.replace("orig(", "Old(").replace(")", ")")
        # Replace `size()` with `len()`
        line = line.replace("size(", "len(").replace("[])", ")")
        # Convert `null` to `None`
        line = line.replace("null", "None")

        
        if any(op in line for op in ["==", "!=", ">=", "<=", ">", "<", "%", "-", "+", "**"]):
            if not line.startswith("Invariant("):
                return f"Invariant({line.strip()})"

        # Default case: return as-is
        return line.strip()

    # Process the Daikon output line by line
    lines = [line.strip() for line in daikon_output.splitlines() if line.strip()]

    for line in lines:
        # Skip metadata or irrelevant lines
        if any(
            line.startswith(prefix)
            for prefix in [
                "Daikon version", "Reading declaration files", "Exiting Daikon", "=",
                "iter_inv_0()", "loop_inv_0()", "End of report", "No return from procedure"
            ]
        ):
            continue

        # Process each valid line
        processed_line = process_line(line)
        if processed_line:
            invariants.append(processed_line)

    # Remove duplicates and sort for consistency
    unique_invariants = sorted(set(invariants))
    return unique_invariants
