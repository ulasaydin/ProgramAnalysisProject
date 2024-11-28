from pathlib import Path

class Instrumenter:
    var_print_fun = \
r"""type_comparability = {'index':1}
list_indexes = {'__index':1000}
print('decl-version 2.0')
def variablePrinter(var, var_name, dtrace, list_types): 
    # int -> just print 
    # bool -> print 1/0 
    # array -> [ 1 2 3 4 5] 
    if dtrace: 
        print(var_name)	
        if (isinstance(var, int)):
            print(var)
        elif (isinstance(var, bool)):
            if (var): # if true 
                print(1) 
            else: # if true 
                print(0) # if true 
        elif (isinstance(var, list)):  
            print(list_indexes[var_name])
            print('1')
            print(var_name+'[..]')	
            print('['+' '.join(str(x) for x in var)+']')
        print('1') #modified
    else:
        print('variable', var_name)
        if (isinstance(var, int)):
            print('var-kind variable\ndec-type int\nrep-type int')
            if ('int' not in type_comparability):
                type_comparability['int'] = type_comparability['index'] 
                type_comparability['index'] += 1 
            print('comparability', type_comparability['int'])
        elif (isinstance(var, bool)):
            print('var-kind variable\ndec-type bool\nrep-type bool')
            if ('bool' not in type_comparability):
                type_comparability['bool'] = type_comparability['index']  
                type_comparability['index'] += 1 
            print('comparability',type_comparability['bool'])
        elif (isinstance(var, list)):  
            print('var-kind variable\ndec-type []\nrep-type hashcode')
            if ('List' not in type_comparability):
                type_comparability['List'] = type_comparability['index']  
                type_comparability['index'] += 1 
            print('comparability',type_comparability['List'])
            if (var_name not in list_indexes):
                list_indexes[var_name] = list_indexes['__index']
                list_indexes['__index'] += 1
            print(f'variable {var_name}[..]\nvar-kind array\nenclosing-var {var_name}\ndec-type {list_types[var_name]}\nrep-type hashcode[]')
            if (list_types[var_name] not in type_comparability):
                type_comparability[list_types[var_name]] = type_comparability['index']  
                type_comparability['index'] += 1 
            print('comparability',type_comparability[list_types[var_name]])

"""

    fin = None
    fout = None




    def functionVariableReader(self, var_string):
        # var_string -> "n: int, m: int"
        self.status['list_types'] = 'list_types = {'
        for var in var_string.split(','):
            var_name = var.split(':')[0].strip()
            var_type = var.split(':')[1].strip()
            if 'List' in var_type:
                self.status['list_types'] += f"\'{var_name}\': \'{var_type.split('[')[1].split(']')[0].strip()}\',"
            if var_name not in self.status['variables']: # sets are cool, but not ordered :/
                self.status['variables'].append(var_name)
        self.status['list_types'] += '}'

    def line_analyser(self, line):
        i = 0
        line = line.replace('    ','\t')
        while i<len(line) and line[i]=='\t':
            i+=1
        if line=='':
            self.fout.write('\n')
            return
        if self.status['loop_depth'] > i and self.status['iter_invariant_stack']:
            self.fout.write('\n'+'\t'*self.status['depth']+f"print('\\n{self.status['iter_invariant_stack'][-1]}:::EXIT{self.status['exit_counter']}') \n")
            for var_name in self.status['variables']:
                self.fout.write('\t'*self.status['depth']+f'variablePrinter({var_name},\'{var_name}\',True,list_types)\n')   #var value
            self.status['iter_invariant_stack'].pop()

            self.status['depth'] = i
            self.fout.write('\n'+'\t'*self.status['depth']+f"print('\\n{self.status['loop_invariant_stack'][-1]}:::EXIT{self.status['exit_counter']}') \n")
            for var_name in self.status['variables']:
                self.fout.write('\t'*self.status['depth']+f'variablePrinter({var_name},\'{var_name}\',True,list_types)\n')   #var value
            self.status['loop_invariant_stack'].pop()
            self.status['exit_counter'] += 1

        self.status['depth'] = i

        if self.status['depth'] < self.status['function_depth'] and self.status['fun_name']:
            # self.fout.write('\t'*self.status['depth']+f"print('{self.status['fun_name'][-1]}:::EXIT') \n")
            self.status['fun_name'].pop()
            self.status['variables'] = []
        
        if self.status['just_entered_function']:
            self.status['function_depth'] = self.status['depth']
            self.status['just_entered_function'] = False
            self.functionVariableReader(self.status['fun_declaration'].split('(')[1].split(')')[0])
            self.fout.write('\t'*self.status['depth']+self.status['list_types'] + '\n')

        is_invariant = False    
        if line.startswith("def "):
            self.status['fun_name'].append(line[3:].split('(')[0].strip())
            self.status['just_entered_function'] = True
            self.status['fun_declaration'] = line
            self.fout.write(line + "\n")
        elif 'Requires' in line or 'Ensures' in line or 'Assert' in line:
            return
        elif 'while' in line or 'for' in line:
            self.status['loop_invariant_stack'].append('loop_inv_'+ str(self.status['loop_invariant_counter'])+'()')
            self.status['loop_invariant_counter'] += 1

            #declaration printer
            self.fout.write('\t'*self.status['depth']+f"print('\\nppt {self.status['loop_invariant_stack'][-1]}:::ENTER') \n")
            for var_name in self.status['variables']:
                self.fout.write('\t'*self.status['depth']+f'variablePrinter({var_name},\'{var_name}\',False,list_types)\n')   #var value
            self.fout.write('\t'*self.status['depth']+f"print('\\nppt {self.status['loop_invariant_stack'][-1]}:::EXIT{self.status['exit_counter']}') \n")
            for var_name in self.status['variables']:
                self.fout.write('\t'*self.status['depth']+f'variablePrinter({var_name},\'{var_name}\',False,list_types)\n')   #var value

            #datatrace printer
            self.fout.write('\t'*self.status['depth']+f"print('\\n{self.status['loop_invariant_stack'][-1]}:::ENTER') \n")
            for var_name in self.status['variables']:
                self.fout.write('\t'*self.status['depth']+f'variablePrinter({var_name},\'{var_name}\',True,list_types)\n')   #var value
            
            #bool for iterations
            self.fout.write('\t'*self.status['depth']+f"first_iter = True\n")
            self.fout.write(line + "\n")
        elif 'Invariant' in line:
            if not self.status['just_entered_invariant']:
                is_invariant = True
                self.status['just_entered_invariant'] = True
                name = "iter_inv_" + str(self.status['iter_invariant_counter'])
                self.status['iter_invariant_counter'] += 1
                name+="()"
                self.status['loop_depth'] = self.status['depth']
                
                self.status['iter_invariant_stack'].append(name)
                
                #bool check
                self.fout.write('\t'*self.status['depth']+f"if first_iter:\n")
                self.fout.write('\t'*(self.status['depth']+1)+f"first_iter = False\n")
                #declaration printer
                self.fout.write('\t'*(self.status['depth']+1)+f"print('\\nppt {self.status['iter_invariant_stack'][-1]}:::ENTER') \n")
                for var_name in self.status['variables']:
                    self.fout.write('\t'*(self.status['depth']+1)+f'variablePrinter({var_name},\'{var_name}\',False,list_types)\n')   #var value
                self.fout.write('\t'*(self.status['depth']+1)+f"print('\\nppt {self.status['iter_invariant_stack'][-1]}:::EXIT{self.status['exit_counter']}') \n")
                for var_name in self.status['variables']:
                    self.fout.write('\t'*(self.status['depth']+1)+f'variablePrinter({var_name},\'{var_name}\',False,list_types)\n')   #var value

                #datatrace printer
                self.fout.write('\t'*self.status['depth']+f"print('\\n{self.status['iter_invariant_stack'][-1]}:::ENTER') \n")
                for var_name in self.status['variables']:
                    self.fout.write('\t'*self.status['depth']+f'variablePrinter({var_name},\'{var_name}\',True,list_types)\n')   #var value
            else:
                return
        elif 'if'not in line and '=' in line:
            var_name = line.split('=')[0].strip().rstrip('+/-*%^& ')
            if var_name not in self.status['variables'] and not self.status['iter_invariant_stack']:
                self.status['variables'].append(var_name)
            self.fout.write(line + "\n")
        else:
            self.fout.write(line+"\n")	

        if not is_invariant:
            self.status['just_entered_invariant'] = False
            


    def instrument_file(self, filename_in, filename_out):
        self.fin = open(filename_in, "r")
        self.fout = open(filename_out, "w")
        self.fout.write(self.var_print_fun)
        self.status = {
            'fun_name': [],
            'function_depth': 0,
            'list_types': "",
            'just_entered_function': False,
            'just_entered_invariant': False,
            'loop_invariant_counter': 0,
            'loop_invariant_stack': [],
            'iter_invariant_counter': 0,
            'iter_invariant_stack': [],
            'loop_depth': 0,
            'exit_counter': 1,
            'depth': 0,
            'variables': []
        }
        for line in self.fin.readlines():
            self.line_analyser(line.rstrip())
        
        while self.status['iter_invariant_stack']:
            self.fout.write('\n'+'\t'*self.status['depth']+f"print('\\n{self.status['iter_invariant_stack'][-1]}:::EXIT{self.status['exit_counter']}') \n")
            for var_name in self.status['variables']:
                self.fout.write('\t'*self.status['depth']+f'variablePrinter({var_name},\'{var_name}\',True,list_types)\n')   #var value
            self.status['iter_invariant_stack'].pop()

        while self.status['loop_invariant_stack']:
            self.fout.write('\n'+'\t'*self.status['depth']+f"print('\\n{self.status['loop_invariant_stack'][-1]}:::EXIT{self.status['exit_counter']}') \n")
            for var_name in self.status['variables']:
                self.fout.write('\t'*self.status['depth']+f'variablePrinter({var_name},\'{var_name}\',True,list_types)\n')   #var value
            self.status['loop_invariant_stack'].pop()

        self.fout.write('\n\nprint("\\n\\n# EOF (added by Runtime.addShutdownHook)\\n")')
