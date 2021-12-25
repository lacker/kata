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

def step_helper(board, color, i, steps):
	answer = []
	for step in steps:
		delta = step
		while empty(board, i + delta):
			answer.append((i, i + delta))
			delta += step
	return answer

def legal_moves(board, color):
	"""
	Moves are represented as a (i, j) tuple, where the piece is moving from board[i] to board[j].
	"""
	moves = []
	for i, piece in enumerate(board):
		if get_color(board, i) != color:
			continue
		if piece == "P":
			if empty(board, i+1):
				moves.append((i, i+1))
			if i == 5 and empty(board, 6) and empty(board, 7):
				moves.append((5, 7))
		elif piece == "p":
			if empty(board, i-1):
				moves.append((i, i-1))
			if i == 10 and empty(board, 9) and empty(board, 8):
				moves.append((10, 8))
		elif piece in "Nn":
			for delta in (-3, -2, 2, 3):
				if empty(board, i + delta):
					moves.append((i, i + delta))
		elif piece in "Bb":
			moves += step_helper(board, i, (-2, 2))
		elif piece in "Rr":
			moves += step_helper(board, i, (-1, 1))
		elif piece in "Qq":
			moves += step_helper(board, i, (-2, -1, 1, 2))
		elif piece in "Kk":
			for delta in (-1, 1):
				if empty(board, i + delta):
					moves.append((i, i + delta))
	return moves
				
			
print(legal_moves(START, WHITE))
		

