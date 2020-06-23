from random import choice, shuffle

SIZE = 6
DIGITS = range(SIZE)

def generate():
	answer = []
	for _ in range(SIZE):
		answer.append(choice(DIGITS))
	return answer

def all_possible(length):
	if length == 0:
		return [[]]
	answer = []
	tails = all_possible(length - 1)
	for first in DIGITS:
		for tail in tails:
			answer.append([first] + tail)
	return answer

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
		if x == y:
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
	return s1 == s2

def info(list1, list2):
	return (
		right_answer(list1, list2),
	  right_items(list1, list2),
	  right_place(list1, list2))

# returns whether you did it	
def check(list1, list2):
	ra, ri, rp = info(list1, list2)
	if ra:
		print("correct!")
		return True
	print(rp, "in the right place")
	print(ri - rp, "in the wrong place")
	return False		

def read():
	while True:
		line = input("guess:")
		chars = list(line.strip())
		try:
			digits = list(map(int, chars))
			if len(digits) != SIZE:
				continue
			return digits
		except:
			pass
	
class HumanPlayer:
	def __init__(self):
		pass
	
	def guess(self):
		return read()				
		
	def inform(self, guess, ra, ri, rp):
		if ra:
			print("correct!")
		print(rp, "in the right place")
		print(ri - rp, "in the wrong place")	


class ComputerPlayer():
	def __init__(self):
		self.possibilities = all_possible(SIZE)				

	def inform(self, guess, ra, ri, rp):
		new_possibilities = []
		for possibility in self.possibilities:
			ta, ti, tp = info(guess, possibility)
			if (ta, ti, tp) == (ra, ri, rp):
				new_possibilities.append(possibility)
		self.possibilities = new_possibilities	
				
	def guess(self):
		answer = self.possibilities[0]
		print("guessing:", answer)
		return answer																																																										
def play(player):
	print("let's play a game")
	guesses = 0
	target = generate()
	while True:
		guess = player.guess()
		if guess is None:
			raise Exception("guess is None")
		guesses += 1
		if check(target, guess):
			print("you win with", guesses, "guesses")
			return guesses
		ra, ri, rp = info(target, guess)
		player.inform(guess, ra, ri, rp)

def average(player, rounds):
	total
	for _ in range(rounds):
		total += play(player)


play(ComputerPlayer())
