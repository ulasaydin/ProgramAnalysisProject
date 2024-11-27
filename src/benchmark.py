from datetime import datetime
import os
from tkinter import FALSE
from platformdirs import user_data_dir
import sys
import shutil
import argparse

current_dir = os.path.dirname(__file__)
sys.path.append(current_dir)


from config import APP_AUTHOR, APP_NAME, TEST_CASES
from invariant_finder import find_invariants


parser = argparse.ArgumentParser(prog="Loop Invariant Finder Benchmark")
parser.add_argument(
    "-o",
    "--output-dir",
    help="Output directory",
    required=False,
)
args = parser.parse_args()

if args.output_dir:
    benchmark_dir = args.output_dir
else:
    user_data_directory = user_data_dir(APP_NAME, APP_AUTHOR)
    benchmark_dir_name = f"Benchmark-{datetime.now().strftime('%Y-%m-%d_%H-%M-%S')}"
    benchmark_dir = os.path.join(user_data_directory, benchmark_dir_name)


# Path to the existing 'theories' folder
existing_theories_path = os.path.join(os.path.dirname(__file__), '..', 'converted', 'theories')

print(f"Running benchmark and writing results to {benchmark_dir}:")

for program_file_path, entry_point_method in TEST_CASES:
    output_dir_name = f"{os.path.basename(program_file_path)}-{entry_point_method}"
    output_dir = os.path.join(benchmark_dir, output_dir_name)
    
    os.makedirs(output_dir, exist_ok=True)
    
    if os.path.exists(existing_theories_path):
        theories_dest_path = os.path.join(output_dir, 'theories')
        if not os.path.exists(theories_dest_path):
            shutil.copytree(existing_theories_path, theories_dest_path)
            print(f"Copied existing 'theories' folder from {existing_theories_path} to {theories_dest_path}")
        else:
            print(f"'theories' folder already exists at {theories_dest_path}")
    find_invariants(os.path.normpath(os.path.join(os.path.dirname(__file__), program_file_path)), entry_point_method, output_dir)


