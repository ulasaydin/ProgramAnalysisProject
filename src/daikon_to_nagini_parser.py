import re

def parse_daikon_output(daikon_output):
 
    invariants = []

    def process_line(line):
        """
        Process a single line of Daikon output and convert it to Nagini-compatible format.
        """
        # Replace `orig` with `Old`
        line = line.replace("orig(", "Old(").replace(")", ")")

        # Replace `size(array[])` with `len(array)`
        line = line.replace("size(", "len(").replace("[])", ")")

        # Convert `null` to `None`
        line = line.replace("null", "None")

        # Handle "one of {}" by converting to or
        if "one of {" in line:
            match = re.search(r"(\w+)\s+one\s+of\s+\{(.+?)\}", line)
            if match:
                variable = match.group(1)
                values = match.group(2).split(",")
                values = [value.strip() for value in values]
                conditions = " or ".join(f"{variable} == {value}" for value in values)
                return f"Invariant({conditions})"

        # Handle `sorted(reverse=True)`
        if "sorted(reverse=True)" in line:
            return f"Invariant({line.strip()})"

        # Wrap mathematical and logical operations in `Invariant()` if not already wrapped
        if any(op in line for op in ["==", "!=", ">=", "<=", ">", "<", "%", "**", "-", "+"]):
            if not line.startswith("Invariant("):
                return f"Invariant({line.strip()})"

        # Handle "has only one value"
        if "has only one value" in line:
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
