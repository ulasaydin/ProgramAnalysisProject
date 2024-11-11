def variablePrinter(var_name): 
	# int -> just print 
	# bool -> print 1/0 
	# array -> [ 1 2 3 4 5] 
	if (isinstance(var_name, int)):
		print(var_name)
	elif (isinstance(var_name, bool)):
		if (var_name): # if true 
			print(1) 
		else: # if true 
			print(0) # if true 
	elif (isinstance(var_name, list)):  
		print('['+' '.join(var_name+']'))
	print('1') #modified
def client(n: int) -> int:
	i = 0
	sum = 0
	print('\nloop_inv_0():::ENTER') 
	print('n') 
	variablePrinter(n)
	print('i') 
	variablePrinter(i)
	print('sum') 
	variablePrinter(sum)
	while i < n:
		print('\niter_inv_0():::ENTER') 
		print('n') 
		variablePrinter(n)
		print('i') 
		variablePrinter(i)
		print('sum') 
		variablePrinter(sum)
		i += 1
		sum += i
		# -->EXIT

		print('\niter_inv_0():::EXIT1') 
		print('n') 
		variablePrinter(n)
		print('i') 
		variablePrinter(i)
		print('sum') 
		variablePrinter(sum)

	print('\nloop_inv_0():::EXIT1') 
	print('n') 
	variablePrinter(n)
	print('i') 
	variablePrinter(i)
	print('sum') 
	variablePrinter(sum)

client(10)

print("\n\n# EOF (added by Runtime.addShutdownHook)\n")