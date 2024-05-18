MAX = 10000

def generate_str_pair():
    left = random.randrange(0, MAX)
    right = random.randrange(0, MAX)
    symbol = "+"
    answer = str(left + right)
    s = f"{left} {symbol} {right}"
    return (s, answer)
    
class Tokenizer:
    def __init__(self):
        self.n_to_ch = []
        self.ch_to_n = {}
    
    def to_token(self, ch):
        if ch in self.ch_to_n:
            return self.ch_to_n[ch]
        n = len(self.ch_to_n)
        self.ch_to_n[ch] = n
        return n
        
    def to_char(self, n):
        return self.n_to_ch[n]
    
    def generate_token_pair():
        in_str, out_str = generate_str_pair()
        in_tokens = [self.to_token(ch) for ch in in_str]
        out_tokens = [self.to_token(ch) for ch in out_str]

def main():
    pass
    
