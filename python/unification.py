#!/usr/bin/env python


class Expression:
	def __init__(self, token=None, left=None, right=None, variable_id=None):
		self.token = token
		self.left = left
		self.right = right
		self.variable_id = variable_id

class Constant:
	def __init__(self, token):
		self.token =

class Variable:
	def __init__(self, variable_id):
		self.variable_id = variable_id
	
class Tree:
	def __init__(self, left, right):
		self.left = left
		self.right = right
			
				
V = Variable
C = Constant

def unify(lhs, rhs):
	pass
