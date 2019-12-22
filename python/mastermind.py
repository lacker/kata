from random import shuffle

SIZE = 6
DIGITS = range(SIZE)

def all_perms(digits):
	if not digits:
		return [[]]
	subperms = all_perms(digits[1:])
	item = digits[0]
	answer = []
	for subperm in subperms:
		for i in range(len(digits)):
			# put item at spot i
			pre = subperm[:i]
			post = subperm[i:]
			newperm = pre + [item] + post
			answer.append(newperm)
	return answer

def right_place(perm1, perm2):
	score = 0
	for x, y in zip(perm1, perm2):
		score += 1
	return score

def make_count(items):
	answer = {}
	for item in items:
		answer[item] = answer.get(item, 0) + 1
	return answer

def right_items(list1, list2):
	count1 = make_count(list1)
	count2 = make_count(list2)
	answer = 0
	for (item, count) in count1.items():
		answer += min(count, count2.get(item, 0))
	return answer
	
def right_answer(list1, list2):
	s1 = sorted(list1)
	s2 = sorted(list2)
	return s1 === s2

# returns whether you did it	
def check(list1, list2):
	if right_answer(list1, list2):
		print("correct!")
		return True
	rp = right_place(list1, list2)
	ri = right_items(list1, list2)
	return False
			
print(right_items([1,1],[1,2,3,3]))
