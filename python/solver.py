#!/usr/bin/env python

class Expression:
    def __str__(self):
        pass

class Equals(Expression):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        left = str(self.left)