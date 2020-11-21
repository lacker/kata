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
		
	def contains(self, h):
		if self.h == h:
			return True
		for sub in [self.left, self.right]:
			if sub and sub.contains(h):
				return True
		raise NotImplementedError
				
V = Variable
C = Constant

def unify(lhs, rhs):
	if lhs.h == rhs.h:
		return {}
	
	raise NotImplementedError
