import sys
# check example.py.dtrace.py for output

var_print_fun = "def variablePrinter(var_name): \n"+\
"\t"+   "# int -> just print \n"+\
"\t"+   "# bool -> print 1/0 \n"+\
"\t"+   "# array -> [ 1 2 3 4 5] \n"+\
"\t"+   "if (isinstance(var_name, int)):\n"+\
"\t"+   "\tprint(var_name)\n"+\
"\t"+   "elif (isinstance(var_name, bool)):\n"+\
"\t"+   "\tif (var_name): # if true \n"+\
"\t"+   "\t\tprint(1) \n"+\
"\t"+   "\telse: # if true \n"+\
"\t"+   "\t\tprint(0) # if true \n"+\
"\t"+   "elif (isinstance(var_name, list)):  \n"+\
"\t"+   "\tprint(\'[\'+\' \'.join(var_name+\']\'))\n"


def variableReader(var_string, variables_dict):
    # var_string -> "n: int, m: int"
    for var in var_string.split(','):
        var_name = var.split(':')[0].strip()
        var_type = var.split(':')[1].strip()
        variables_dict[var_name] = {
            'type': var_type,
            'modified': 1, 
            # 0 means unititialized, 1 means initialized	
            # this is passed by someone so i hope is initialized
        }
        fout.write('\t'*status['depth']+f"print('{var_name}') \n")   #var name
        fout.write('\t'*status['depth']+f'variablePrinter({var_name})\n')   #var value
        fout.write('\t'*status['depth']+"print(1) \n")     #var modified

def line_analyser(line, status, variables):
    if line.startswith("def "):
        status['in_function'] = True
        status['depth'] += 1
        status['fun_name'].append(line[3:].split('(')[0].strip())
        fout.write(line + "\n")
        fout.write('\t'*status['depth']+f"print('{status['fun_name'][-1]}:::ENTER') \n")
        # print nonce?
        variableReader(line.split('(')[1].split(')')[0], variables)



if len(sys.argv)!=2:
    print("usage python3 prog <file>")
    exit()

fin = open(sys.argv[1], "r")
fout = open(sys.argv[1]+".dtrace.py" , "w")

status={
    'in_function': False,
    'fun_name': [],
    'depth': 0,
}
variables = {}
fout.write(var_print_fun)

for line in fin.readlines():
    line_analyser(line.strip(), status, variables)
