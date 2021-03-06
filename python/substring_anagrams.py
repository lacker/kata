# Updates values in place
def update(values, key, delta):
	new_value = values.get(key, 0) + delta
	if new_value:
		values[key] = new_value
	else:
		del values[key]
		
def find_substring_anagrams(big, small):
	count = {}
	for ch in small:
		update(count, ch, -1)
	answer = []
	for i, ch in enumerate(big):
		update(count, ch, 1)
		j = i - len(small)
		if j >= 0:
			update(count, big[j], -1)
		if not count:
			answer.append(i - len(small) + 1)
	return answer
	
find_substring_anagrams("abcdefedcba", "feed")
find_substring_anagrams("","")
