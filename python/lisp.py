def evaluate(expr):
	t = type(expr)
	if t in (int, float):
		return expr
	if t is not list:
		raise BaseException(f"cannot evaluate type: {t}")
		
	op = expr[0]
	args = rest[1:]
		if type(op) is not function:
			raise BaseException(f"{op} is not a function")
	return apply(op, args)
	
	
assert evaluate(1) == 1
assert evaluate(1.25) == 1.25
print(evaluate(evaluate))
print("ok")
