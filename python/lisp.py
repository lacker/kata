def macro(f):
	f.macro = True
	return f

@macro
def quote(x):
	return x
	
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
	if op.macro:
		return op(*args)
	args = map(evalute, args)
	return op(args)
	
def add(*args):
	answer = 0
	for arg in args:
		answer += arg
	return answer	
	
assert evaluate(1) == 1
assert evaluate(1.25) == 1.25
print(evaluate([add, 1, 2, 3]))
print("ok")
