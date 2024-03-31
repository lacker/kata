MAX = 10000

def generate():
    left = random.randrange(0, MAX)
    right = random.randrange(0, MAX)
    symbol = "+"
    answer = left + right
    s = f"{left} {symbol} {right}"
    return (s, answer)
    
class Tokenizer:
    def __init__(self):
        self.n_to_ch = []
        self.ch_to_n = {}
    
    def to_token(ch):
        if ch in self.ch_to_n:
            pass
    

def main():
    pass
    
