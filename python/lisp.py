def evaluate(expr):
	if type(expr) in (int, float):
		return expr
	if type(expr) is not list:
		raise BaseException("can only evaluate lists")
	return t
	
assert evaluate(1) == 1
assert evaluate(1.25) == 1.25
#print(evaluate(evaluate))
print("ok")
