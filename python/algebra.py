class Formula:
    def __init__(self):
        pass
        
class Token:
    def __init__(self, token):
        self.token = token
        
    def __eq__(self, other):
        return self.token == other.token
        
class Variable:
    def __init__(self):
        pass