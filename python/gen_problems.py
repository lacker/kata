MAX = 100

def generate():
    left = random.randrange(0, MAX)
    right = random.randrange(0, MAX)
    symbol = "+"
    return f"{left} {symbol} {right}"
    

def main():
    pass