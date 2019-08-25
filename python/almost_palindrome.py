def srev(s):
	return "".join(reversed(s))

def is_pal(s):
  return s == srev(s)
  
print(is_pal("foof"))
print(is_pal("boof"))
