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
	print('client:::ENTER') 
	print('n') 
	variablePrinter(n)
	i = 0
	print('i') 
	variablePrinter(i)
	sum = 0
	print('sum') 
	variablePrinter(sum)
	while i < n:
		i += 1
		print('i ') 
		variablePrinter(i )
		sum += i
		print('sum ') 
		variablePrinter(sum )
	print('client:::EXIT') 