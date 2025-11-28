"""
SAT Assignment Part 2 - Non-consecutive Sudoku Solver (Puzzle -> SAT/UNSAT)

THIS is the file to edit.

Implement: solve_cnf(clauses) -> (status, model_or_None)"""


from typing import Iterable, List, Tuple, Set, Dict
import copy

def _clauses_to_sets(clauses: Iterable[Iterable[int]]) -> List[Set[int]]:
  """Convert list-of-lists clauses to list-of-sets (for efficient ops)."""
  return [set(c) for c in clauses]

def _is_satisfied_clause(clause: Set[int], assignment: Dict[int, bool]) -> bool:
  """Return True if clause is satisfied under assignment."""
  for lit in clause:
    var = abs(lit)
    if var in assignment:
      val = assignment[var]
      if (lit > 0 and val) or (lit < 0 and not val):
        return True
  return False

def _contains_empty_clause(clauses: List[Set[int]]) -> bool:
  """Return True if any clause is empty."""
  return any(len(c) == 0 for c in clauses)

# --------------------
# Simplification
# --------------------

def _unit_propagate(clauses: List[Set[int]], assignment: Dict[int, bool]) -> Tuple[List[Set[int]], Dict[int, bool], bool]:
    """
    Perform unit propagation until fixpoint.
    - clauses: list of clause-sets (modified copy)
    - assignment: dict var->bool (modified copy)
    Returns (new_clauses, new_assignment, conflict_flag)
    conflict_flag True indicates a contradiction encountered.
    """
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


def _pure_literal_elim(clauses: List[Set[int]], assignment: Dict[int, bool]) -> Tuple[List[Set[int]], Dict[int, bool]]:
    """
    Detect pure literals (only one polarity present) and assign them to satisfy all clauses where they appear.
    Repeat until no more pure literals are found.
    """
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

def _choose_branch_var(clauses: List[Set[int]], assignment: Dict[int, bool], num_vars: int) -> Tuple[int, bool]:
    """
    Choose a branching variable and preferred polarity.
    We implement a DLCS-like heuristic: choose var with maximum (pos_count + neg_count).
    Return (var, preferred_value).
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

def _simplify_after_assignment(clauses: List[Set[int]], lit: int) -> List[Set[int]]:
    """
    Given assignment of literal `lit` to True, remove satisfied clauses and remove -lit from other clauses.
    Returns new clauses list. Does NOT detect empty clause (caller should check).
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

def _build_model(assignment: Dict[int, bool], num_vars: int) -> List[int]:
    """
    Build a full DIMACS-style model (list of ints 1..num_vars).
    Unassigned variables are set to False (negative) for determinism.
    """
    model = []
    for v in range(1, num_vars + 1):
      val = assignment.get(v, False)
      model.append(v if val else -v)
    return model

def _dpll(clauses: List[Set[int]], assignment: Dict[int, bool], num_vars: int) -> Tuple[bool, Dict[int, bool]]:
    """
    Core recursive DPLL.
    Returns (sat_flag, assignment_if_sat)
    """
    # 1. Unit clause rule
    clauses, assignment, conflict = _unit_propagate(clauses, assignment)
    if conflict:
        return False, {}
    
    # 2. Pure literal elimination
    clauses, assignment = _pure_literal_elim(clauses, assignment)

    # 3. Check base cases
    if not clauses:
        # no clauses -> satisfied
        return True, assignment
    if _contains_empty_clause(clauses):
        return False, {}

    # 4. Choose variable to branch (heuristic)
    var, pref_val = _choose_branch_var(clauses, assignment, num_vars)
    # if all variables already assigned, but not all clauses satisfied
    if var is None:
      return False, {}

    # 5. Branch: try preferred polarity first
    for try_val in (pref_val, not pref_val):
      lit = var if try_val else -var
      
      new_assignment = dict(assignment)
      new_assignment[var] = try_val
      new_clauses = _simplify_after_assignment(clauses, lit)
      # if empty clause, not satisfied,backtrack, try oher value
      if any(len(c) == 0 for c in new_clauses):
        continue
      # recursion, move to next level in our tree
      sat, final_assignment = _dpll(new_clauses, new_assignment, num_vars)
      if sat:
        return True, final_assignment

    return False, {}

def solve_cnf(clauses: Iterable[Iterable[int]], num_vars: int) -> Tuple[str, List[int] | None]:
    """
    Public solver function required by the assignment.

    clauses: iterable of lists of ints
    num_vars: number of variables

    Returns:
      ("SAT", model_list) or ("UNSAT", None)
    """
  
    clause_sets = _clauses_to_sets(clauses)
    sat, assignment = _dpll(clause_sets, {}, num_vars)
    
    if sat:
      model = _build_model(assignment, num_vars)
      return "SAT", model
    else:
      return "UNSAT", None


