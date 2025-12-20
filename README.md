# Topology_in_Lean_Project_6_Compactness

The goal of this project is to prove Heine-Borel and the extreme value theorem.

```
Heine Borel
Subsets of R^n are compact iff they are closed and bounded.
```
What we will need for Heine Borel:
- Compactness.lean => TopologicalSpaces.lean, ContinuousFunctions.lean, Filters.lean => MetricSpaces.lean => Bases.lean
- Hausdorff
- subcover
- tychonoff theorem
- closed
- bounded

```
Corollary (Extreme value theorem):
f : R^n -> R continuous and K is a compact subset of R^n then
exists x in K s.t. for any y in K f(y) <= f(x)
```

What we will need for Extreme value theorem:
- ContinuousFunctions.lean, Compactness.lean => TopologicalSpaces.lean

What we don't need up to now:
- Connectedness.lean





## Remainder
Today (1,12): Compactness
Next Week: Tikhonov's Thm
Last Week: fundamental groups

## Definitions
The folder Definitions contains all the definitions and theorems introduced and proved in Class.