"""
SAT Assignment Part 2 - Non-consecutive Sudoku Solver (Puzzle -> SAT/UNSAT)

THIS is the file to edit.

Implement: solve_cnf(clauses) -> (status, model_or_None)"""


from typing import Iterable, List, Tuple, Set, Dict


def convert_clauses(clauses):
  """Convert clauses to a list-of-sets"""
  return [set(c) for c in clauses]

# --------------------
# Simplification rules
# --------------------

def unit_clause_rule(clauses, assignment):
    clauses = clauses[:]
    assignment = dict(assignment)

    while True:
      # find unit clauses
      unit_lits = []
      for c in clauses:
        if len(c) == 1:
          unit_lits.append(next(iter(c)))

      if not unit_lits:
        break

      for lit in unit_lits:
        # check boolean of literal
        var = abs(lit)
        val = (lit > 0)

        # check for conflict
        if var in assignment:
          if assignment[var] != val:
              return clauses, assignment, True
          else:
              continue

        # put variable in assignment
        assignment[var] = val

        # simplify clauses:
        new_clauses = []
        # loop through clauses and check if the contain the unit lit
        for c in clauses:
          # unit clause satisfied, so remove
          if lit in c:
            continue
          # literal falsified, so remove
          if -lit in c:
            new_c = set(c)
            new_c.remove(-lit)
            # empty clause, so conflict
            if len(new_c) == 0:
              return clauses, assignment, True
            new_clauses.append(new_c)
          # unit literal not in clause 
          else:
            new_clauses.append(c)
        clauses = new_clauses
        
    return clauses, assignment, False


def pure_literal_rule(clauses, assignment):
    clauses = clauses[:]
    assignment = dict(assignment)

    while True:
      pos_occ: Dict[int,int] = {}
      neg_occ: Dict[int,int] = {}
      
      for c in clauses:
        for lit in c:
          var = abs(lit)
          # already assigned variable, so skip
          if var in assignment:
            continue
          # add positive literal to the dict
          if lit > 0:
            pos_occ[var] = pos_occ.get(var,0) + 1
          # add negative literal to the dict
          else:
            neg_occ[var] = neg_occ.get(var,0) + 1

      pure_vars = []
      for var in set(list(pos_occ.keys()) + list(neg_occ.keys())):
        # already assigned, so continue
        if var in assignment:
          continue
        p = pos_occ.get(var,0)
        n = neg_occ.get(var,0)
        # add true pure variable
        if p > 0 and n == 0:
          pure_vars.append((var, True))
        # add false pure variable
        elif n > 0 and p == 0:
          pure_vars.append((var, False))

      if not pure_vars:
          break

      # assign and simplify
      for var, val in pure_vars:
        # assign pure literal
        assignment[var] = val
        # update the clauses
        lit = var if val else -var
        new_clauses = []
        for c in clauses:
          # clause is satisfied, so skip
          if lit in c:
            continue
          # clause does not have pure literal so don't change
          new_clauses.append(c)
        clauses = new_clauses

    return clauses, assignment


# --------------------
# Split
# --------------------

def split(clauses, assignment, num_vars):
    """
    Chosen heuristic for splitting: DLCS
    Dynamic largest combined sum: CP(v) + CN(v) (= most frequent v)
    If CP(v)>CN(v) then v=1 else v=0
    """
    pos_count = {}
    neg_count = {}

    for c in clauses:
      for lit in c:
        var = abs(lit)
        # already assigned, so skip
        if var in assignment:
            continue
        # count positive occurences of literal
        if lit > 0:
            pos_count[var] = pos_count.get(var, 0) + 1
        # count negative occurences of literal
        else:
            neg_count[var] = neg_count.get(var, 0) + 1

    best_var = None
    best_score = -1
    best_pref = True

    for var in range(1, num_vars + 1):
      if var in assignment:
        continue
      p = pos_count.get(var, 0)
      n = neg_count.get(var, 0)
      score = p + n
      # update best score
      if score > best_score:
        best_score = score
        best_var = var
        best_pref = (p >= n)

    return best_var, best_pref


# --------------------
# Simplify
# --------------------
def check_empty_clause(clauses):
  return any(len(c) == 0 for c in clauses)

def simplify_after_assignment(clauses, lit):
    """
    Given assignment of literal `lit` to True, remove satisfied clauses and remove -lit from other clauses.
    """
    new_clauses = []
    for c in clauses:
      # clause satisfied, so skip
      if lit in c:
        continue
      # remove the negations of the literal from the clause
      if -lit in c:
        new_c = set(c)
        new_c.remove(-lit)
        new_clauses.append(new_c)
      # clause not affected by literal
      else:
        new_clauses.append(c)
    return new_clauses


# --------------------
# DPLL
# --------------------

def dpll(clauses, assignment, num_vars):
    """Recursive DPLL."""
    # 1. Unit clause rule
    clauses, assignment, conflict = unit_clause_rule(clauses, assignment)
    if conflict:
        return False, {}
    
    # 2. Pure literal elimination
    clauses, assignment = pure_literal_rule(clauses, assignment)

    # 3. Check base cases
    if not clauses:
        # no clauses -> satisfied
        return True, assignment
    if check_empty_clause(clauses):
        return False, {}

    # 4. Choose variable to split (heuristic)
    var, pref_val = split(clauses, assignment, num_vars)
    # if all variables already assigned, but not all clauses satisfied
    if var is None:
      return False, {}

    # 5. SPlit: try preferred polarity first
    for try_val in (pref_val, not pref_val):
      lit = var if try_val else -var
      
      new_assignment = dict(assignment)
      new_assignment[var] = try_val
      new_clauses = simplify_after_assignment(clauses, lit)
      # if empty clause, not satisfied,backtrack, try oher value
      if any(len(c) == 0 for c in new_clauses):
        continue
      # recursion, move to next level in our tree
      sat, final_assignment = dpll(new_clauses, new_assignment, num_vars)
      if sat:
        return True, final_assignment

    return False, {}

def build_model(assignment, num_vars):
    """
    Build a full DIMACS-style model
    Unassigned variables are set to False
    """
    model = []
    for v in range(1, num_vars + 1):
        val = assignment.get(v, False)
        model.append(v if val else -v)
    return model

def solve_cnf(clauses, num_vars):
    """
    Implement your SAT solver here.
    Must return:
      ("SAT", model)  where model is a list of ints (DIMACS-style), or
      ("UNSAT", None)
    """
  
    clause_sets = convert_clauses(clauses)
    sat, assignment = dpll(clause_sets, {}, num_vars)
    
    if sat:
      model = build_model(assignment, num_vars)
      return "SAT", model
    else:
      return "UNSAT", None

# python main.py --in puzzle.txt
# command to run in terminal: python3 main.py --in ../"EXAMPLE puzzles (input)"/example_n9.txt  --out example.cnf

