"""
From SAT Assignment Part 1 - Non-consecutive Sudoku Encoder (Puzzle -> CNF)

Replace this code with your solution for assignment 1

Implement: to_cnf(input_path) -> (clauses, num_vars)

You're required to use a variable mapping as follows:
    var(r,c,v) = r*N*N + c*N + v
where r,c are in range (0...N-1) and v in (1...N).

You must encode:
  (1) Exactly one value per cell
  (2) For each value v and each row r: exactly one column c has v
  (3) For each value v and each column c: exactly one row r has v
  (4) For each value v and each sqrt(N)×sqrt(N) box: exactly one cell has v
  (5) Non-consecutive: orthogonal neighbors cannot differ by 1
  (6) Clues: unit clauses for the given puzzle
"""


from typing import Tuple, Iterable
from typing import Tuple, Iterable
import math


# --------------------
# Helper functions
# --------------------

def read_text(input_path):
    with open(input_path) as f:
        grid = [list(map(int, line.split())) for line in f]
    return grid


def map_to_var(r, c, v, N):
    return r * N * N + c * N + v


# --------------------
# Constraints
# --------------------

# 1. Exactly one value per cell
def one_value_per_cell_helper(var_ls):
  """
  for one box
  return [[at least one(or)] and [at most one (or)]]
  """
  clauses = []

  # at least one
  clauses.append(list(var_ls))

  # at most one (can not have two values in same cell)
  nr_var = len(var_ls)
  for i in range(nr_var):
      for j in range(i + 1, nr_var):
          clauses.append([-var_ls[i], -var_ls[j]])

  return clauses


def one_value_per_cel(N):
  clauses = []

  for r in range(N):
    for c in range(N):
      # numbers 1 to N for every box
      var_ls = [map_to_var(r, c, v, N) for v in range(1, N + 1)]
      clauses.extend(one_value_per_cell_helper(var_ls))

  return clauses


# 2. Row constraint
def row_constraint(N):
  """
  For each value v and each row r, exactly one column c has v.
  """
  clauses = []

  for r in range(N):
    for v in range(1, N + 1):
      # all the column options
      var_ls = [map_to_var(r, c, v, N) for c in range(N)]
      clauses.extend(one_value_per_cell_helper(var_ls))

  return clauses


# 3. Column constraint
def col_constraint(N):
  """
  For each value v and each column c, exactly one row r has v.
  """
  clauses = []

  for c in range(N):
    for v in range(1, N + 1):
      # all the row options
      var_ls = [map_to_var(r, c, v, N) for r in range(N)]
      clauses.extend(one_value_per_cell_helper(var_ls))

  return clauses


# 4. Box constraint
def box_constraint(N):
  """
  For each value v and each B × B box, exactly one cell in that box has v.
  """
  clauses = []
  B = int(math.sqrt(N))

  # go through grid per box
  for outer_r in range(0, N, B):
    for outer_c in range(0, N, B):
      # go into box
      # create value options for the box
      for v in range(1, N + 1):
        var_ls = []
        for inner_r in range(B):
          for inner_c in range(B):
            # grid row and column
            r = outer_r + inner_r
            c = outer_c + inner_c
            var_ls.append(map_to_var(r, c, v, N))
        clauses.extend(one_value_per_cell_helper(var_ls))
  return clauses


# 5. Non-consecutive rule
def non_consecutive(N):
  """
  For each cell v, adjacent cells cannot be v+1
  """
  clauses = []

  for r in range(N):
    for c in range(N):
      # check right and down neighbors
      n_right = (r, c + 1)
      n_down = (r + 1, c)
      for (r2, c2) in (n_down, n_right):
        # check if neighbours are still on grid
        if 0 <= r2 < N and 0 <= c2 < N:
          for v in range(1, N):
            # non consecutive
            clauses.append([-map_to_var(r, c, v, N), -map_to_var(r2, c2, v + 1, N)])
            clauses.append([-map_to_var(r, c, v + 1, N), -map_to_var(r2, c2, v, N)])

  return clauses


# 6. Clues
def clues(grid, N):
  clauses = []

  # loop through grid
  for r in range(N):
    for c in range(N):
      v = grid[r][c]
      # if it's a clue
      if v != 0:
        clauses.append([map_to_var(r, c, v, N)])

  return clauses


# --------------------
# Conjunction
# --------------------

def to_cnf(input_path: str) -> Tuple[Iterable[Iterable[int]], int]:
  """
  Read puzzle from input_path and return (clauses, num_vars).

  - clauses: iterable of iterables of ints (each clause), no trailing 0s
  - num_vars: must be N^3 with N = grid size
  """

  grid = read_text(input_path)
  N = len(grid)
  clauses = []
  num_vars = N ** 3

  clauses += one_value_per_cel(N)
  clauses += row_constraint(N)
  clauses += col_constraint(N)
  clauses += box_constraint(N)
  clauses += non_consecutive(N)
  clauses += clues(grid, N)

  return (clauses, num_vars)
