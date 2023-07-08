class Term(object):
    def __init__(self):
        pass
        
    def map(self, mapping):
        return self
        
class Atom(Term):
    def __init__(self, atom):
        self.atom = atom
        
    def __eq__(self, other):
        return self.atom == other.atom
        
    def __str__(self):
        return str(self.atom)
        
class Variable(Term):
    def __init__(self, number):
        self.number = number
        
    def map(self, mapping):
        return mapping.get(self.number, self)
        
class Composite(Term):
    def __init__(self, head, args):
        self.head = head
        self.args = args
    
    def map(self, mapping):
        pass
        
class Replaced:
    def __init__(self, term, mapping):
        self.term = term
        self.mapping = mapping
        
def unify(left, right, left_map=None, right_map=None):
    pass