import sys

def line_analyser(line, status, variables):
    if line.startswith("def "):
        status['in_function'] = True
        fout.write(line + "\n")
        


if len(sys.argv)!=2:
    print("usage python3 prog <file>")
    exit()

fin = open(sys.argv[1], "r")
fout = open(sys.argv[1]+".dtrace" , "w")

status={
    'in_function': False,
}
variables = {}

for line in fin.readlines():
    line_analyser(line.strip(), status, variables)
