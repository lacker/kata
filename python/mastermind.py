from random import shuffle

SIZE = 6
DIGITS = range(SIZE)

def all_perms(digits):
	if not digits:
		return [[]]
	subperms = all_perms(digits[1:])
	item = digits[0]
	answer = []
	for subperm in subperms:
		for i in range(len(digits)):
			# put item at spot i
			pre = subperm[:i]
    	raise Exception("todo")
