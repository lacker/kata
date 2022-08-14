#!/usr/bin/env python
"""
One-dimensional chess. See https://gumroad.com/l/1DChess
"""

import random
import sys

START = "KQRBNP....pnbrqk"

WHITE = "WHITE"
BLACK = "BLACK"

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

def get_score(board, player):
	"Returns a score for the given player"
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
		pass		
			
	if player == WHITE:
		return material
	if player == BLACK:
		return -material
	raise ValueError("bad player value")
	
def invert_move(move):
	if move is None:
		return None
	return tuple(len(START) - 1 - i for i in move)
	
def tree_search(board, depth, player):
	"""
	Return (score, move) for the player to move.
	Positive scores are better.
	"""
	w = winner(board)
	if w:
		if w == player:
			return 1000, None
		return -1000, None
	
	if depth == 0:		
		s = get_score(board, player)
		return s, None
	
	possible = []
	for move in legal_moves(board, player):
		new_board = make_move(board, move)
		subdepth = depth - 1
		if is_capture(board, move):
			subdepth += 1
		subscore, submove = tree_search(new_board, subdepth, opposite_color(player))
		possible.append((-subscore, move))
	if not possible:
		raise ValueError("game is over")
	best_score = max(s for s, _ in possible)
	candidates = [move for s, move in possible
								if s == best_score]
	return best_score, random.choice(candidates)
	
	
def play_game():
	board = START
	depth = 2
	print()
	for i in range(100):
		score, move = tree_search(board, depth, WHITE)
		print("white score:", score, "move:", move)
		board = make_move(board, move)
		print("board:", board)
		if winner(board):
			print("white wins")
			break
		score, move = tree_search(board, depth, BLACK)
		print("black score:", score, "move:", move)
		board = make_move(board, move)
		print("board:", board)
		if winner(board):
			print("black wins")
			break

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
						
play_game()
# test()
	
