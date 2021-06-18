#!/usr/bin/env python
"""
One-dimensional chess. See https://gumroad.com/l/1DChess
"""

START = "KQRBNP....pnbrqk"

def legal_moves(board):
  """
  Moves are represented as a (i, j) tuple, where the piece is moving from board[i] to board[j].
  """
  for i, piece in enumerate(board):
    pass
