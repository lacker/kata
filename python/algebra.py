class Formula:
    def __init__(self):
        pass
        
class Atom:
    def __init__(self, token):
        self.token = token
        
    def __eq__(self, other):
        return self.token == other.token