# whether s from i to j inclusive is a palindrome
def seq_is_pal(s, i, j):
  if i >= j:
  	return True
  if s[i] != s[j]:
  	return False
  return seq_is_pal(s, i+1, j-1)
 
def is_almost_pal(s, i, j):
	 return "xxx"
	 
def is_pal(s):
	return seq_is_pal(s, 0, len(s)-1)
    
print(is_pal("foof"))
print(is_pal("boof"))
