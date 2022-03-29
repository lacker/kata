#!/usr/bin/env python
"""
One-dimensional chess. See https://gumroad.com/l/1DChess
"""

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
	if i < 0 or i > len(board):
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
	assert board[post] == "."
	new_board = list(board)
	new_board[post] = new_board[pre]
	new_board[pre] = "."
	return "".join(new_board)
				
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
			
for move in legal_moves(START, WHITE):
	print(move)
	board = make_move(START, move)
	print(board)
	print(invert(board))
	
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
}

def get_score(board):
	pass
