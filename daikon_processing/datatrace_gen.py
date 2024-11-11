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
"\t"+   "\tprint(\'[\'+\' \'.join(var_name+\']\'))\n"\
"\t"+   "print('1') #modified\n"


def functionVariableReader(var_string, status):
    # var_string -> "n: int, m: int"
    for var in var_string.split(','):
        var_name = var.split(':')[0].strip()
        # var_type = var.split(':')[1].strip()
        if var_name not in status['variables']: # sets are cool, but not ordered :/
            status['variables'].append(var_name)

def line_analyser(line, status):
    i = 0
    line = line.replace('    ','\t')
    while i<len(line) and line[i]=='\t':
        i+=1

    if status['depth'] > i and status['iter_invariant_stack']:
        fout.write('\n'+'\t'*status['depth']+f"print('\\n{status['iter_invariant_stack'][-1]}:::EXIT{status['exit_counter']}') \n")
        for var_name in status['variables']:
            fout.write('\t'*status['depth']+f"print('{var_name}') \n")   #var name
            fout.write('\t'*status['depth']+f'variablePrinter({var_name})\n')   #var value

        status['depth'] = i
        fout.write('\n'+'\t'*status['depth']+f"print('\\n{status['loop_invariant_stack'][-1]}:::EXIT{status['exit_counter']}') \n")
        for var_name in status['variables']:
            fout.write('\t'*status['depth']+f"print('{var_name}') \n")   #var name
            fout.write('\t'*status['depth']+f'variablePrinter({var_name})\n')   #var value
        status['loop_invariant_stack'].pop()
        status['exit_counter'] += 1

    status['depth'] = i

    if status['depth'] < status['function_depth'] and status['fun_name']:
        # fout.write('\t'*status['depth']+f"print('{status['fun_name'][-1]}:::EXIT') \n")
        status['fun_name'].pop()
        status['variables'] = []
    
    if status['just_entered_function']:
        status['function_depth'] = status['depth']
        status['just_entered_function'] = False
        functionVariableReader(status['fun_declaration'].split('(')[1].split(')')[0], status)

    is_invariant = False    
    if line.startswith("def "):
        status['fun_name'].append(line[3:].split('(')[0].strip())
        status['just_entered_function'] = True
        status['fun_declaration'] = line
        fout.write(line + "\n")
    elif 'Requires' in line or 'Ensures' in line or 'Assert' in line:
        return
    elif 'while' in line or 'for' in line:
        status['loop_invariant_stack'].append('loop_inv_'+ str(status['loop_invariant_counter'])+'()')
        status['loop_invariant_counter'] += 1

        fout.write('\t'*status['depth']+f"print('\\n{status['loop_invariant_stack'][-1]}:::ENTER') \n")
        for var_name in status['variables']:
            fout.write('\t'*status['depth']+f"print('{var_name}') \n")   #var name
            fout.write('\t'*status['depth']+f'variablePrinter({var_name})\n')   #var value
        
        fout.write(line + "\n")
    elif 'Invariant' in line:
        if not status['just_entered_invariant']:
            is_invariant = True
            status['just_entered_invariant'] = True
            name = "iter_inv_" + str(status['iter_invariant_counter'])
            status['iter_invariant_counter'] += 1
            name+="()"
            
            status['iter_invariant_stack'].append(name)
            fout.write('\t'*status['depth']+f"print('\\n{status['iter_invariant_stack'][-1]}:::ENTER') \n")
            for var_name in status['variables']:
                fout.write('\t'*status['depth']+f"print('{var_name}') \n")   #var name
                fout.write('\t'*status['depth']+f'variablePrinter({var_name})\n')   #var value
        else:
            return
    elif 'if'not in line and '=' in line:
        var_name = line.split('=')[0].strip().rstrip('+/-*%^& ')
        if var_name not in status['variables']:
            status['variables'].append(var_name)
        fout.write(line + "\n")
    else:
        fout.write(line+"\n")	

    if not is_invariant:
        status['just_entered_invariant'] = False
        


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
    'just_entered_invariant': False,
    'loop_invariant_counter': 0,
    'loop_invariant_stack': [],
    'iter_invariant_counter': 0,
    'iter_invariant_stack': [],
    'exit_counter': 1,
    'depth': 0,
    'variables': []
}
for line in fin.readlines():
    line_analyser(line.rstrip(), status)

while status['fun_name']:
    #fout.write(f'\n{status['fun_name'].pop()}({', '.join(status['variables'])})\n')
    fout.write('\n\nprint("\\n\\n# EOF (added by Runtime.addShutdownHook)\\n")')
    status['fun_name'].pop()