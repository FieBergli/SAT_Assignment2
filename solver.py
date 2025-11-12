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

def _unit_propagate(clauses: List[Set[int]], assignment: Dict[int, bool]) -> Tuple[List[Set[int]], Dict[int, bool], bool]:
    """
    Perform unit propagation until fixpoint.
    - clauses: list of clause-sets (modified copy)
    - assignment: dict var->bool (modified copy)
    Returns (new_clauses, new_assignment, conflict_flag)
    conflict_flag True indicates a contradiction encountered.
    """
    clauses = clauses[:]  # shallow copy of list; sets inside are same objects but will be replaced when needed
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
            var = abs(lit)
            val = (lit > 0)

            # if var already assigned and inconsistent => conflict
            if var in assignment:
                if assignment[var] != val:
                    return clauses, assignment, True
                else:
                    # already assigned consistently; skip
                    continue

            # assign
            assignment[var] = val

            # simplify clauses:
            new_clauses = []
            for c in clauses:
                if lit in c:
                    # clause satisfied -> drop it
                    continue
                if -lit in c:
                    # remove the falsified literal
                    new_c = set(c)
                    new_c.remove(-lit)
                    if len(new_c) == 0:
                        # empty clause -> conflict
                        return clauses, assignment, True
                    new_clauses.append(new_c)
                else:
                    new_clauses.append(c)
            clauses = new_clauses
            # after assigning one unit literal, we break to restart scanning for unit clauses
            # (but outer while will pick up newly created unit clauses)
        # continue loop to find newly created unit clauses

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
                if var in assignment:
                    # skip already assigned vars
                    continue
                if lit > 0:
                    pos_occ[var] = pos_occ.get(var,0) + 1
                else:
                    neg_occ[var] = neg_occ.get(var,0) + 1

        pure_vars = []
        for var in set(list(pos_occ.keys()) + list(neg_occ.keys())):
            if var in assignment:
                continue
            p = pos_occ.get(var,0)
            n = neg_occ.get(var,0)
            if p > 0 and n == 0:
                pure_vars.append((var, True))
            elif n > 0 and p == 0:
                pure_vars.append((var, False))

        if not pure_vars:
            break

        # assign and simplify
        for var, val in pure_vars:
            assignment[var] = val
            lit = var if val else -var
            new_clauses = []
            for c in clauses:
                if lit in c:
                    # satisfied
                    continue
                # if -lit in c, we just keep c (no need to remove -lit because assignment is global)
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
            if var in assignment:
                continue
            if lit > 0:
                pos_count[var] = pos_count.get(var, 0) + 1
            else:
                neg_count[var] = neg_count.get(var, 0) + 1

    best_var = None
    best_score = -1
    best_pref = True

    # consider all variables 1..num_vars (some may have zero count)
    for var in range(1, num_vars + 1):
        if var in assignment:
            continue
        p = pos_count.get(var, 0)
        n = neg_count.get(var, 0)
        score = p + n
        if score > best_score:
            best_score = score
            best_var = var
            best_pref = (p >= n)  # prefer the polarity that appears more often
    # if everything assigned (best_var None) it will be handled by caller
    return best_var, best_pref

def _simplify_after_assignment(clauses: List[Set[int]], lit: int) -> List[Set[int]]:
    """
    Given assignment of literal `lit` to True, remove satisfied clauses and remove -lit from other clauses.
    Returns new clauses list. Does NOT detect empty clause (caller should check).
    """
    new_clauses = []
    for c in clauses:
        if lit in c:
            continue
        if -lit in c:
            new_c = set(c)
            new_c.remove(-lit)
            new_clauses.append(new_c)
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
    # 1. Unit propagation
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
    if var is None:
        # no unassigned variable left but clauses still exist -> unsat (shouldn't normally happen)
        return False, {}

    # 5. Branch: try preferred polarity first
    for try_val in (pref_val, not pref_val):
        lit = var if try_val else -var
        # copy data structures for recursion
        new_assignment = dict(assignment)
        new_assignment[var] = try_val
        new_clauses = _simplify_after_assignment(clauses, lit)
        # check immediate conflict
        if any(len(c) == 0 for c in new_clauses):
            continue
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
    # Convert clauses to sets for internal processing
    clause_sets = _clauses_to_sets(clauses)
    sat, assignment = _dpll(clause_sets, {}, num_vars)
    if sat:
        model = _build_model(assignment, num_vars)
        return "SAT", model
    else:
        return "UNSAT", None

def solve_cnf(clauses: Iterable[Iterable[int]], num_vars: int) -> Tuple[str, List[int] | None]:
    """
    Implement your SAT solver here.
    Must return:
      ("SAT", model)  where model is a list of ints (DIMACS-style), or
      ("UNSAT", None)
    """
    raise NotImplementedError
