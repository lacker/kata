from random import shuffle

SIZE = 6
DIGITS = range(SIZE)

def all_perms(digits):
	if not digits:
		return [[]]
	subperms = all_perms(digits[1:])
	answer = []
	raise Exception("todo")
