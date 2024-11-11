type_comparability = {'index':1}
print('decl-version 2.0')
def variablePrinter(var, dtrace): 
	# int -> just print 
	# bool -> print 1/0 
	# array -> [ 1 2 3 4 5] 
	if dtrace: 
		if (isinstance(var, int)):
			print(var)
		elif (isinstance(var, bool)):
			if (var): # if true 
				print(1) 
			else: # if true 
				print(0) # if true 
		elif (isinstance(var, list)):  
			print('['+' '.join(str(x) for x in var)+']')
		print('1') #modified
	else:
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
			print('['+' '.join(str(x) for x in var)+']')

def client(n: int) -> int:
	i = 0
	sum = 0
	# loop invariant ---> ENTER
	print('\nppt loop_inv_0():::ENTER') 
	print('variable n') 
	variablePrinter(n, False)
	print('variable i') 
	variablePrinter(i, False)
	print('variable sum') 
	variablePrinter(sum, False)
	print('\nppt loop_inv_0():::EXIT1') 
	print('variable n') 
	variablePrinter(n, False)
	print('variable i') 
	variablePrinter(i, False)
	print('variable sum') 
	variablePrinter(sum, False)
	print('\nloop_inv_0():::ENTER') 
	print('n') 
	variablePrinter(n, True)
	print('i') 
	variablePrinter(i, True)
	print('sum') 
	variablePrinter(sum, True)
	first_iter = True
	while i < n:
		if first_iter:
			first_iter = False
			print('\nppt iter_inv_0():::ENTER') 
			print('variable n') 
			variablePrinter(n, False)
			print('variable i') 
			variablePrinter(i, False)
			print('variable sum') 
			variablePrinter(sum, False)
			print('\nppt iter_inv_0():::EXIT1') 
			print('variable n') 
			variablePrinter(n, False)
			print('variable i') 
			variablePrinter(i, False)
			print('variable sum') 
			variablePrinter(sum, False)
		print('\niter_inv_0():::ENTER') 
		print('n') 
		variablePrinter(n, True)
		print('i') 
		variablePrinter(i, True)
		print('sum') 
		variablePrinter(sum, True)
		i += 1
		sum += i
		# iter invariant ---> EXIT

		print('\niter_inv_0():::EXIT1') 
		print('n') 
		variablePrinter(n,True)
		print('i') 
		variablePrinter(i,True)
		print('sum') 
		variablePrinter(sum,True)

	print('\nloop_inv_0():::EXIT1') 
	print('n') 
	variablePrinter(n, True)
	print('i') 
	variablePrinter(i, True)
	print('sum') 
	variablePrinter(sum, True)
	# loop invariant ---> EXIT

client(10)
print("\n\n# EOF (added by Runtime.addShutdownHook)\n")