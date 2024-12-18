type_comparability = {'index':1}
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
			if ('list' not in type_comparability):
				type_comparability['list'] = type_comparability['index']  
				type_comparability['index'] += 1 
			print('comparability',type_comparability['list'])
			if (var_name not in list_indexes):
				list_indexes[var_name] = list_indexes['__index']
				list_indexes['__index'] += 1
			print(f'variable {var_name}[..]\nvar-kind array\nenclosing-var {var_name}\ndec-type {list_types[var_name]}\nrep-type hashcode[]')
			if (list_types[var_name] not in type_comparability):
				type_comparability[list_types[var_name]] = type_comparability['index']  
				type_comparability['index'] += 1 
			print('comparability',type_comparability[list_types[var_name]])

def client(n: int) -> int:
	list_types = {}
	i = 0
	sum = 0
	# loop invariant ---> ENTER
	print('\nppt loop_inv_0():::ENTER') 
	variablePrinter(n,'n',False,list_types)
	variablePrinter(i,'i',False,list_types)
	variablePrinter(sum,'sum',False,list_types)
	print('\nppt loop_inv_0():::EXIT1') 
	variablePrinter(n,'n',False,list_types)
	variablePrinter(i,'i',False,list_types)
	variablePrinter(sum,'sum',False,list_types)
	print('\nloop_inv_0():::ENTER') 
	variablePrinter(n,'n',True,list_types)
	variablePrinter(i,'i',True,list_types)
	variablePrinter(sum,'sum',True,list_types)
	first_iter = True
	while i < n:
		if first_iter:
			first_iter = False
			print('\nppt iter_inv_0():::ENTER') 
			variablePrinter(n,'n',False,list_types)
			variablePrinter(i,'i',False,list_types)
			variablePrinter(sum,'sum',False,list_types)
			print('\nppt iter_inv_0():::EXIT1') 
			variablePrinter(n,'n',False,list_types)
			variablePrinter(i,'i',False,list_types)
			variablePrinter(sum,'sum',False,list_types)
		print('\niter_inv_0():::ENTER') 
		variablePrinter(n,'n',True,list_types)
		variablePrinter(i,'i',True,list_types)
		variablePrinter(sum,'sum',True,list_types)
		i += 1
		sum += i
		# iter invariant ---> EXIT

		print('\niter_inv_0():::EXIT1') 
		variablePrinter(n,'n',True,list_types)
		variablePrinter(i,'i',True,list_types)
		variablePrinter(sum,'sum',True,list_types)

	print('\nloop_inv_0():::EXIT1') 
	variablePrinter(n,'n',True,list_types)
	variablePrinter(i,'i',True,list_types)
	variablePrinter(sum,'sum',True,list_types)
	# loop invariant ---> EXIT
client(10)

print("\n\n# EOF (added by Runtime.addShutdownHook)\n")