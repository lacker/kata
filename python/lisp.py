def evaluate(expr):
	t = type(expr)
	if t in (int, float):
		return expr
	if t is not list:
		raise BaseException(f"cannot evaluate type: {t}")
		
	op = expr[0]
	args = map(evaluate, expr[1:])
	if not callable(op):
		raise BaseException(f"{op} is not callable")
	return op(*args)
	
assert evaluate(1) == 1
assert evaluate(1.25) == 1.25
print(evaluate([sum, 1, 2, 3]))
print("ok")
print(type(evaluate))
