#!/usr/bin/env python


class Expression:
	def __init__(self, token=None, left=None, right=None, variable_id=None):
		self.token = token
		self.left = left
		self.right = right
		self.variable_id = variable_id
		
		self.h = 0
		for x in [token, left, right, variable_id]:
			self.h = 2 * self.h + hash(x)

	def __str__(self):
		if self.variable_id is not None:
			return f"V{self.variable_id}"
		if self.left is None and self.right is None:
			return str(self.token)
		return f"({self.left} {self.token} {self.right})"

	def is_variable(self):
		return self.variable_id is not None
		
	def any(self, f):
		if f(self):
			return True
		if self.left and f(self.left):
			return True
		return self.right and f(self.right)
		
	def __hash__(self):
		return self.h
		
	def contains(self, h):
		return self.any(lambda x: x.h == h)
				
	def has_var(self, v):
		return self.any(lambda x: x.variable_id == v)	
				
	def replace(self, v, expr):
		if self.variable_id == v:
			return expr
		if self.left is None:
			new_left = None
		else:
			new_left = self.left.replace(v, expr)
		if self.right is None:
			new_right = None
		else:
			new_right = self.right.replace(v, expr)
		return Expression(left=new_left, right=new_right, variable_id=self.variable_id, token=self.token)
		
	def sub(self, varmap):
		answer = self
		for v, expr in varmap.items():
			answer = answer.replace(v, expr)
		return answer
		
	def __eq__(self, other):
		if self.token != other.token:
			return False
		if self.left != other.left:
			return False
			
				
def V(id):
	return Expression(variable_id=id)
	
def C(id):
	return Expression(token=id)

def unify(lhs, rhs):
	"""
	Returns a tuple of the varmap and the unified expression. 
	"""
	print(f"unifying {lhs} and {rhs}")
	if lhs is None:
		if rhs is None:
			return {}, None
		raise ValueError("cannot unify None")
	if rhs is None:
		raise ValueError("cannot unify None")
		
	if lhs.h == rhs.h:
		return {}, lhs
	if lhs.is_variable():
		if rhs.has_var(lhs.variable_id):
			raise ValueError("cannot unify with subtree")
		answer = {}
		answer[lhs.variable_id] = rhs
		return answer, rhs
	if rhs.is_variable():
		if lhs.has_var(rhs.variable_id):
			raise ValueError("cannot unify with subtree")
		answer = {}
		answer[rhs.variable_id] = lhs
		return answer, lhs
			
	if lhs.token != rhs.token:
		raise ValueError(f"token mismatch: {lhs.token} != {rhs.token}")
			
	lsubs, _ = unify(lhs.left, rhs.left)
	print("lsubs:", lsubs)
	new_lhs = lhs and lhs.sub(lsubs)
	print("new lhs:", new_lhs)
	new_rhs = rhs and rhs.sub(lsubs)
	print("new rhs:", new_rhs)
	
	rsubs, final_rhs = unify(new_lhs.right, new_rhs.right)
	final_lhs = new_lhs.sub(rsubs)
	
	subs = dict(lsubs)
	for k, v in rsubs:
		# todo: fail on mismatch
		subs[k] = v
	
	return Expression(token=lhs.token, right=final_rhs, left=final_lhs), subs
	
def add(left, right):
	return Expression(token="+", left=left, right=right)
	
def test():
	left = add(V(1), C(2))
	right = add(C(1), V(2))
	u = unify(left, right)
	print(u)
	
test()
