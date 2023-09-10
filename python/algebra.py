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
        
# Modifies the maps
def unify_var(n, term, var_map, term_map):
    existing = term_map.get(number)
    comp = var_map.get(number)
    if existing is not None:
        if existing == comp:
            return
        raise ValueError("cannot unify")
    term_map[number] = comp

def unify(left, right, left_map, right_map):
    if left.is_variable():
        unify_var(left.number, right, left_map, right_map)
        return
    if right.is_variable():
        unify_var(right.number, left, right_map, left_map)
        return
    if left == right:
        return