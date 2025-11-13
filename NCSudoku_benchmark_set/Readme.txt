In this repo, you'll find a benchmark set of non-consecutive SUDOKU puzzles, in .txt format, as well as a csv describing them.

All of those puzzles are non-trivial; ie. when solved with a SOTA SAT solver, they required branching, and couldn't be solved with pure propagation and literal elimination. This is not a deterministic behaviour - with some luck, and a certain set of heuristics, your solver might solve some of those without branching; it's quite an unlikely result, but possible. The number of conflicts and decisions made using the reference solver are stored in the .csv file.

The solving time is quantified into categories:
< 0.1s
< 0.5s
< 1s
< 5s
< 30s

Those times are reference times for a State-Of-The-Art solver, and are not by any measure the required times to "hit". Taking a minute or so on a 16x16 puzzle is very reasonable, and solving a 25x25 puzzle can take even longer - remember the complexity scales according to n^3.

The set des not include 16x16 and 25x25 unsat puzzles - such puzzles have such rich structure, that generating a non-trivial unsat puzzle of this size seems impossible. Use 9x9 sets for additional SAT/UNSAT checks (on top of the previously provided set), as well as benchmarking both kinds of problems; the 16 and 25 sets are useful if you want to check how does your solver scale for larger, non-trivial problems.

Good luck!