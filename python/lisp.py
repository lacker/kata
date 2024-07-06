ENV = {}

def macro(f):
	f.macro = True
	return f
	
def expose(f):
	ENV[f.__name__] = f
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
		return evaluate(ENV[expr], local=local)
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
	
def let(varname, value, expr, local={}):
	new_local = dict(local)
	new_local[varname] = value
	return evaluate(expr, local=new_local)
	
@expose
def add(*args):
	answer = 0
	for arg in args:
		answer += arg
	return answer
	
@expose
def mul(*args):
	answer = 1
	for arg in args:
		answer *= arg
	return answer
	
@expose
def cons(first, rest):
	answer = [first]
	answer.extend(rest)
	return answer
	
@expose
def car(x):
	return x[0]
	
@expose
def cdr(x):
	return x[1:]
	
@expose
def xmap(f, items):
	return list(map(f, items))
	
def monolamb(expr):
	raise Exception("TODO")
	
def seq(exprs):
	res = None
	for expr in exprs:
		res = evaluate(expr)
	return res
	
assert evaluate(1) == 1
assert evaluate(1.25) == 1.25
assert evaluate([add, 1, 2, 3]) == 6
assert evaluate(["add", 1, 2, 3]) == 6
print("ok")
