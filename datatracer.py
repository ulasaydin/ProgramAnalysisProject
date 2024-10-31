import sys

def variableReader(var_string, variables_dict):
    # var_string -> "n: int, m: int"
    for var in var_string.split(','):
        var_name = var.split(':')[0].strip()
        var_type = var.split(':')[1].strip()
        variables_dict[var_name] = {
            'type': var_type,
            'value': 1, 
            # 0 means unititialized, 1 means initialized	
            # this is passed by someone so i hope is initialized
        }

def line_analyser(line, status, variables):
    if line.startswith("def "):
        status['in_function'] = True
        fout.write(line + "\n")
        variableReader(line.split('(')[1].split(')')[0], variables)



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
