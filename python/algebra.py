class Formula:
    def __init__(self):
        pass
        
class Atom:
    def __init__(self, atom):
        self.atom = atom
        
    def __eq__(self, other):
        return self.atom == other.atom
        
    def __str__(self):
        return str(self.atom)
        
class Variable:
    def __init__(self, number):
        self.number = number
        
class Term:
    def __init__(self, head, args):
        self.head = head
        self.args = args
        
class Replaced:
    def __init__(self, term, mapping):
        self.term = term
        self.mapping = mapping
        
def unify(left, right, left_map=None, right_map=None):
    pass