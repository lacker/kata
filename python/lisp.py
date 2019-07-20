def evaluate(expr):
	t = type(expr)
	if t in (int, float):
		return expr
	if t is list:
		return apply(expr[0], expr[1:])
	raise BaseException(f"cannot evaluate type: {t}")
	
assert evaluate(1) == 1
assert evaluate(1.25) == 1.25
print(evaluate(evaluate))
print("ok")
