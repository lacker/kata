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

def legal_moves(board):
	"""
	Moves are represented as a (i, j) tuple, where the piece is moving from board[i] to board[j].
	"""
	moves = []
	for i, piece in enumerate(board):
		if piece == ".":
			continue

