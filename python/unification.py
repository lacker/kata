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

	def is_variable(self):
		return self.variable_id is not None
		
	def any(self, f):
		if f(self):
			return True
		return f(self.left) or f(self.right)
		
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
		for v, expr in varmap:
			answer = answer.replace(v, expr)
		return answer
			
				
V = Variable
C = Constant

def unify(lhs, rhs):
	if lhs is None:
		if rhs is None:
			return {}
		raise ValueError("cannot unify None")
	if rhs is None:
		raise ValueError("cannot unify None")
		
	if lhs.h == rhs.h:
		return {}
	if lhs.is_variable():
		if rhs.has_var(lhs.variable_id):
			raise ValueError("cannot unify with subtree")
		answer = {}
		answer[lhs.variable_id] = rhs
		return answer
	if rhs.is_variable():
		if lhs.has_var(rhs.variable_id):
			raise ValueError("cannot unify with subtree")
			
	lsubs = lhs.left.unify(rhs.left)
	new_lhs = lhs.subs(lsubs)
	
	
	raise NotImplementedError
