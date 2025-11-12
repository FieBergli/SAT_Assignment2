#!/usr/bin/env python3
"""
SAT Assignment Part 2 - Non-consecutive Sudoku Solver (puzzle -> SAT/UNSAT)

Do NOT modify this file - instead, implement your function in encoder.py

Usage:
  python main.py --in <puzzle.txt>

Behavior:
  - Reads a Sudoku puzzle in plain text format (N x N grid, 0 = empty).
  - Encodes it to CNF, runs the solver, and decides satisfiability.
  - Prints exactly one line to stdout:
        SAT
     or
        UNSAT
"""

import argparse
from typing import Tuple, Iterable
from encoder import to_cnf
from solver import solve_cnf

def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("--in", dest="inp", required=True)
    p.add_argument("--sat", dest="sat", action='store_true')
    return p.parse_args()

def main():

    args = parse_args()

    if(args.sat):
      clauses, num_vars = parse_dimacs(args.inp)
    else:
      clauses, num_vars = to_cnf(args.inp)

    status, _ = solve_cnf(clauses, num_vars)
    print(status)


def parse_dimacs(input_path: str) -> Tuple[Iterable[Iterable[int]], int]:
    close = False
    if isinstance(input_path, str):
        file = open(input_path, "r")
        close = True
    else:
        file = input_path


    line = file.readline()

    components = line.strip().split(" ")

    if len(components)!= 4 or components[0]!="p" or components[1]!="cnf":
      print("Wrong file format! Expected first line to be 'p cnf NUM_VARS NUM_CLAUSES")
      exit(1)

    num_vars=int(components[2])
    num_clauses=int(components[3])

    clauses=[]

    line=file.readline()
    while(line):
       numbers = [int(x) for x in line.strip().split(" ")]

       if(numbers[-1]!=0):
          print("Wrong format! Clause lines must be terminated with a 0")

       clauses.append(numbers[:-1])

       line=file.readline()


    return clauses, num_vars

if __name__ == "__main__":
    main()
