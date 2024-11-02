import sys, tree_sitter, tree_sitter_python
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
"\t"+   "\tprint(\'[\'+\' \'.join(var_name+\']\'))\n"\
"\t"+   "print('1') #modified\n"


def variableReader(var_string, status):
    # var_string -> "n: int, m: int"
    for var in var_string.split(','):
        var_name = var.split(':')[0].strip()
        var_type = var.split(':')[1].strip()
        fout.write('\t'*status['depth']+f"print('{var_name}') \n")   #var name
        fout.write('\t'*status['depth']+f'variablePrinter({var_name})\n')   #var value
        #fout.write('\t'*status['depth']+"print(1) \n")     #var modified

def line_analyser(line, status):
    i = 0
    line = line.replace('    ','\t')
    while line[i]=='\t':
        i+=1
    status['depth'] = i

    if status['depth'] < status['function_depth'] and status['fun_name']:
        fout.write('\t'*status['depth']+f"print('{status['fun_name'][-1]}:::EXIT') \n")
        status['fun_name'].pop()
    
    if status['just_entered_function']:
        status['function_depth'] = status['depth']
        status['just_entered_function'] = False
        fout.write('\t'*status['depth']+f"print('{status['fun_name'][-1]}:::ENTER') \n")
        # print nonce?
        variableReader(status['fun_declaration'].split('(')[1].split(')')[0], status)

    if line.startswith("def "):
        status['fun_name'].append(line[3:].split('(')[0].strip())
        status['just_entered_function'] = True
        status['fun_declaration'] = line
        fout.write(line + "\n")
    elif 'Requires' in line or 'Ensures' in line or 'Invariant' in line or 'Assert' in line:
        return
    elif '=' in line:
        var_name = line.split('=')[0].strip().rstrip('+/-*%^&')
        fout.write(line + "\n")
        fout.write('\t'*status['depth']+f"print('{var_name}') \n")   #var name
        fout.write('\t'*status['depth']+f'variablePrinter({var_name})\n')   #var value
    elif 'if' in line or 'while' in line or 'for' in line:
        fout.write(line + "\n")
    else:
        fout.write(line + "#---NOT RECOGNIZED---\n")
        


if len(sys.argv)!=2:
    print("usage python3 prog <file>")
    exit()

fin = open(sys.argv[1], "r")
fout = open(sys.argv[1]+".dtrace.py" , "w")

fout.write(var_print_fun)

status = {
    'fun_name': [],
    'function_depth': 0,
    'just_entered_function': False,
    'depth': 0,
}
for line in fin.readlines():
    line_analyser(line.rstrip(), status)

while status['fun_name']:
    fout.write('\t'*status['depth']+f"print('{status['fun_name'][-1]}:::EXIT') \n")
    status['fun_name'].pop()