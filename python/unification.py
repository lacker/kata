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

	def unify(self, other):
		"""
		Returns a map of variable id to expression, or raises a ValueError if we can't unify.
		"""
		if self.h == other.h:
			return {}
		
	def __hash__(self):
		return self.h
				
V = Variable
C = Constant

def unify(lhs, rhs):
	pass
