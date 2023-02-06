#!/usr/bin/env python
"""
One-dimensional chess. See https://gumroad.com/l/1DChess
"""

import random
import sys

START = "KQRBNP....pnbrqk"

WHITE = "white"
BLACK = "black"

def get_color(char):
	if "A" <= char <= "Z":
		return WHITE
	if "a" <= char <= "z":
		return BLACK
	if char == ".":
		return None

def opposite_color(c):
	if c == WHITE:
		return BLACK
	elif c == BLACK:
		return WHITE
	else:
		raise RuntimeError("oc of " + str(c))

def empty(board, i):
	if i < 0:
		return False
	if i >= len(board):
		return False
	return board[i] == "."

def movable(board, color, i):
	if i < 0 or i >= len(board):
		return False
	if empty(board, i):
		return True
	return get_color(board[i]) == opposite_color(color)

def step_helper(board, color, i, steps):
	answer = []
	for step in steps:
		delta = step
		while empty(board, i + delta):
			answer.append((i, i + delta))
			delta += step
		if movable(board, color, i + delta):
			answer.append((i, i + delta))
	return answer

def legal_moves(board, color):
	"""
	Moves are represented as a (i, j) tuple, where the piece is moving from board[i] to board[j].
	"""
	if winner(board):
		return []
	moves = []
	for i, piece in enumerate(board):
		if get_color(board[i]) != color:
			continue
		if piece == "P":
			if movable(board, WHITE, i+1):
				moves.append((i, i+1))
			if i == 5 and empty(board, 6) and empty(board, 7):
				moves.append((5, 7))
		elif piece == "p":
			if movable(board, BLACK, i-1):
				moves.append((i, i-1))
			if i == 10 and empty(board, 9) and empty(board, 8):
				moves.append((10, 8))
		elif piece in "Nn":
			for delta in (-3, -2, 2, 3):
				if movable(board, color, i + delta):
					moves.append((i, i + delta))
		elif piece in "Bb":
			moves += step_helper(board, color, i, (-2, 2))
		elif piece in "Rr":
			moves += step_helper(board, color, i, (-1, 1))
		elif piece in "Qq":
			moves += step_helper(board, color, i, (-2, -1, 1, 2))
		elif piece in "Kk":
			for delta in (-1, 1):
				if movable(board, color, i + delta):
					moves.append((i, i + delta))
	return moves
	
def make_move(board, move):
	pre, post = move
	new_board = list(board)
	new_board[post] = new_board[pre]
	new_board[pre] = "."
	return "".join(new_board)
				
def is_capture(board, move):
	pre, post = move
	return board[post] != "."
				
def invert(board):
	chars = list(board)
	inverted_chars = []
	for char in chars:
		if char.islower():
			inverted_chars.append(char.upper())
		elif char.isupper():
			inverted_chars.append(char.lower())
		else:
			inverted_chars.append(char)
	return "".join(reversed(inverted_chars))
			
def winner(board):
	if "K" not in board:
		return BLACK
	if "k" not in board:
		return WHITE
	return None

MAX_SCORE = 2000			

SCORE_MAP = {
	"K": 100,
	"k": -100,
	"Q": 9,
	"q": -9,
	"R": 5,
	"r": -5,
	"B": 3,
	"b": -3,
	"N": 3,
	"n": -3,
	"P": 1,
	"p": -1,
	".": 0,
}

def get_score(board, player, to_move):
	"""
	Returns a score for the given player.
	"""
	# classic chess material, knight = 3 etc
	material = 0
	# non-king pieces total, to see if it's endgame
	nonking = 0
	
	for ch in board:
		material += SCORE_MAP[ch]
		if ch not in ".kK":
			nonking += 1
			
	if nonking == 0:
		# endgame
		wk_pos = board.index("K")
		bk_pos = board.index("k")
		diff = abs(wk_pos - bk_pos)
		zugzwang = (diff % 2 == 0)
		# incentivize forcing the win
		value = 900 - 10 * diff
		if zugzwang == (player == to_move):
			# we lose in zugzwang
			return -value
		else:
			return value

			
	if player == WHITE:
		return material
	if player == BLACK:
		return -material
	raise ValueError("bad player value")
	
def invert_move(move):
	if move is None:
		return None
	return tuple(len(START) - 1 - i for i in move)	
	
def tree_search(board, player, alpha=MAX_SCORE, beta=-MAX_SCORE, depth=4, cache=None):
	"""
	Return (score, move, positions searched) for the player to move.
	Positive scores are better.
	Score can be truncated to the (alpha, beta) range.
	If we can't find any move that even achieves alpha, return (alpha, None).
	cache maps (board, player) to a score when we have exhausted the game tree.
	"""
	if cache is None:
		cache = {}
	key = (board, player)
	if key in cache:
		b, p = cache[key]
		return b, p, 1
		
	w = winner(board)
	if w:
		if w == player:
			return 1000, None, 1
		return -1000, None, 1

	if depth <= 0:		
		s = get_score(board, player, player)
		return s, None, 1
	subdepth = depth - 1
	
	best_score = alpha
	best_moves = []
	legal = legal_moves(board, player)
	position_count = 1
	
	for move in legal:
		new_board = make_move(board, move)
			
		subscore, submove, subcount = tree_search(new_board, opposite_color(player), -beta, -alpha, subdepth)
		possible_score = -subscore
		position_count += subcount
		
		# Incentivize not stalling forever
		if possible_score > 900:
			possible_score -= 1
			
		if possible_score >= beta:
			if abs(possible_score) > 100:
				cache[key] = possible_score, move
			return possible_score, move, position_count
			
		if possible_score > best_score:
			best_score = possible_score
			best_moves = [move]
		elif possible_score == best_score:
			best_moves.append(move)
		
	if not best_moves:
		return alpha, None, position_count

	return best_score, random.choice(best_moves), position_count


def deepen_search(board, turn):
	depth = 4
	start = time()
	while True:
		score, move, count = tree_search(board, turn, depth=depth)
		if abs(score) > 100:
			return score, move, count
		elapsed = time() - start
	
	
def play_game():
	board = START
	# todo: use n positions not depth
	depth = 4
	turn = WHITE
	print()
	while True:
		score, move, count = tree_search(board, turn, -MAX_SCORE, MAX_SCORE, depth)
		print(f"{turn} score:", score, "move:", move)
		if move is None:
			print(f"{turn} resigns")
			return opposite_color(turn)
		board = make_move(board, move)
		print("board:", board)
		if winner(board):
			print(f"{turn} wins")
			return turn
		turn = opposite_color(turn)
		

def test():
	# Black to move should win
	board = "KQ...n...B..brqk"
	print("starting board:", board)
	legal = legal_moves(board, BLACK)
	# print("legal:", legal)
	for move in legal:
		new_board = make_move(board, move)
		score = get_score(new_board, BLACK)
		print(move, score)

	score, move = tree_search(board, 1, BLACK)
	print("best move:", move, "with score", score)
	
def test2():
	board = "K........R.P.rk."
	print("starting board:", board)
																
play_game()
# test()
	
