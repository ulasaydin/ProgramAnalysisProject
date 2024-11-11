def variablePrinter(var): 
	# int -> just print 
	# bool -> print 1/0 
	# array -> [ 1 2 3 4 5] 
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
from nagini_contracts.contracts import *
from theories.TArrays import within

@Pure
def eq(a: list[int], aFrom: int, aTo: int, b: list[int], bFrom: int, bTo: int) -> bool:

	if aTo - aFrom != bTo - bFrom:
		return False
	else:
		if aFrom >= aTo:
			return True
		else:
			return (a[aFrom] == b[bFrom]) and eq(a, aFrom + 1, aTo, b, bFrom + 1, bTo)

def equals(a: list[int], a2: list[int]) -> bool:

	if a == a2:
		return True

	l = len(a)
	if len(a2) != l:
		return False

	ic = 0

	print('\nloop_inv_0():::ENTER') 
	print('a') 
	variablePrinter(a)
	print('a2') 
	variablePrinter(a2)
	print('l') 
	variablePrinter(l)
	print('ic') 
	variablePrinter(ic)
	while ic < l:
		print('\niter_inv_0():::ENTER') 
		print('a') 
		variablePrinter(a)
		print('a2') 
		variablePrinter(a2)
		print('l') 
		variablePrinter(l)
		print('ic') 
		variablePrinter(ic)

		if a[ic] != a2[ic]:
			return False

		ic += 1


		print('\niter_inv_0():::EXIT1') 
		print('a') 
		variablePrinter(a)
		print('a2') 
		variablePrinter(a2)
		print('l') 
		variablePrinter(l)
		print('ic') 
		variablePrinter(ic)

	print('\nloop_inv_0():::EXIT1') 
	print('a') 
	variablePrinter(a)
	print('a2') 
	variablePrinter(a2)
	print('l') 
	variablePrinter(l)
	print('ic') 
	variablePrinter(ic)
	return True

equals([1,2,3], [1,2,4])
print("\n\n# EOF (added by Runtime.addShutdownHook)\n")