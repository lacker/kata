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
        
class Application:
    def __init__(self, left, right):
        self.left = left
        self.right = right
        
def unify(left, right, left_map=None):
    pass