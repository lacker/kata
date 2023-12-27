class Term(object):
    def __init__(self):
        pass
        
    def map(self, mapping):
        return self
        
    def is_constant(self):
        return False
        
    def is_variable(self):
        return False
        
    def is_composite(self):
        if self.is_variable():
            return False
        return not self.is_constant()
        
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
    if not left.is_composite():
        raise ValueError("cannot unify")
    if not right.is_composite():
        raise ValueError("cannot unify")
    if len(left.args) != len(right.args):
        raise ValueError("arg len mismatch")
    unify(left.head, right.head, left_map, right_map)
    for left_arg, right_arg in zip(left.args, right.args):
        unify(left_arg, right_arg, left_map, right_map)
        
def split_on_char(s, ch):
    parts = []
    for i, part in enumerate(s.split(ch)):
        if i > 0:
            parts.append(ch)
        parts.append(part)
    return parts
        
def split_on_chars(s, chars):
    answer = [s]
    for ch in chars:
        new_answer = []
        for part in answer:
            new_parts = split_on_char(s, part)
            new_answer += new_parts
        answer = new_answer
    return answer

def sparse(string):
    """
    Parse an s expression into lists.
    """
    tokens = split_on_chars(string, "() ")
    for token in tokens:
        pass
        
def nest(tokens):
    """
    Turn the first parenthesized section
    into nested lists.
    Return a tuple of the nested
    section, then the rest of the tokens.
    """
    assert tokens
    first = tokens[0]
    rest = tokens[1:]
    if first == ")":
        raise ValueError("bad )")
    if first != "(":
        return first, rest
    if not rest or rest[-1] != ")":
        pass