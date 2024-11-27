# Usage
Run the benchmark as follows:

`python3.9 src/benchmark.py [-o /path/to/output/directory]`

Run the invariant finder on a program to find its invariants:

`python3.9 src/invariant_finder.py /path/to/program {name-of-entry-point-method} [-o /path/to/output/directory]`

Run Nagini to verify a specific method in a program: (you need to change directory to `converted`)

`nagini --select {name-of-method} /path/to/program`