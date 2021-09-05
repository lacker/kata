#!/usr/bin/env python
"""
One-dimensional chess. See https://gumroad.com/l/1DChess
"""

START = "KQRBNP....pnbrqk"

WHITE = "WHITE"
BLACK = "BLACK"

def color(char):
	if "A" <= char <= "Z":
		return WHITE
	if "a" <= char <= "z":
		return BLACK
	if char == ".":
		return None

def empty(board, i):
	if i < 0:
		return False
	if i >= len(board):
		return False
	return True

def legal_moves(board):
	"""
	Moves are represented as a (i, j) tuple, where the piece is moving from board[i] to board[j].
	"""
	moves = []
	for i, piece in enumerate(board):
		if piece == ".":
			continue
		if piece == "P":
			if empty(board, i+1):
				moves.append(i, i+1)
			if i == 5 and empty(6) and empty(7):
				moves.append(5, 7)
		elif piece == "p":
			if empty(i-1):
				moves.append(i, i-1)
			if i == 10 and empty(board, 9) and empty(board, 8):
				moves.append(10, 8)
		elif piece in "Nn":
			for delta in (-3, -2, 2, 3):
				if empty(i + delta):
					moves.append(i, i + delta)
		elif piece in "Bb":
			for step in (-2, 2):
				delta = step
				while empty(board, i + delta):
					moves.append(i, i + delta)
					delta += step
		elif piece in "Rr":
			for step in (-1, 1):
				delta = step
				while empty(board, i + delta):
					moves.append(i, i + delta)
				
				
			
		

