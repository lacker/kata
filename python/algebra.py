class Term(object):
    def __init__(self):
        pass
        
    def map(self, mapping):
        return self
        
    def is_constant(self):
        return False
        
    def is_variable(self):
        return False
        
class Constant(Term):
    def __init__(self, token):
        self.token = token
        
    def __eq__(self, other):
        return self.token == other.token
        
    def __str__(self):
        return str(self.token)
        
    def is_constant(self):
        return True
        
class Variable(Term):
    def __init__(self, number):
        self.number = number
        
    def map(self, mapping):
        return mapping.get(self.number, self)
        
    def is_variable(self):
        return True
        
class Composite(Term):
    def __init__(self, head, args):
        self.head = head
        self.args = args
    
    def map(self, mapping):
        head = self.head.map(mapping)
        args = [arg.map(mapping) for arg in self.args]
        
def unify(left, right, left_map=None, right_map=None):
    if left_map is None:
        left_map = {}
    if right_map is None:
        right_map = {}
    if left.is_variable():
        existing = left_map.get(left.number)
        left_map[left.number] = right