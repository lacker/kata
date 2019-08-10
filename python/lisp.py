ENV = {}

def macro(f):
	f.macro = True
	return f

@macro
def define(symbol, expr):
	ENV[symbol] = expr

@macro
def quote(x):
	return x
	
def is_macro(f):
	try:
		f.macro
	except AttributeError:
		return False
	return True
	
def evaluate(expr, local={}):
	t = type(expr)
	if t in (int, float):
		return expr
	if t is str:
		return evaluate(ENV[expr])
	if callable(expr):
		return expr
	if t is not list:
		raise BaseException(f"cannot evaluate type: {t}")
			
	op = evaluate(expr[0])
	args = map(evaluate, expr[1:])
	if not callable(op):
		raise BaseException(f"{op} is not callable")
	if is_macro(op):
		return op(*args)
	args = map(evaluate, args)
	return op(*args)
	
def add(*args):
	answer = 0
	for arg in args:
		answer += arg
	return answer	
	
assert evaluate(1) == 1
assert evaluate(1.25) == 1.25
assert evaluate([add, 1, 2, 3]) == 6
print("ok")
