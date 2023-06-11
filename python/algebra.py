class Formula:
    def __init__(self):
        pass
        
class Token:
    def __init__(self, token):
        self.token = token
        
    def __eq__(self, other):
        return self.token == other.token
        
    def __str__(self):
        return self.token
        
class Variable:
    def __init__(self, number):
        self.number = number
        
class Application:
    def __init__(self, left, right):
        self.left = left
        self.right = right