## Schrödinger's hats: a puzzle about parities and permutations

Meet Schrödinger, who travels the world with an unusually clever clowder of *n*
talking cats. In their latest show, the cats stand in a line. Schrödinger asks
a volunteer (not a plant!) to take *n*+1 hats, numbered zero to *n*, and
randomly assign one to each cat, so that there is one spare. Each cat sees all
of the hats in front of it, but not its own hat, nor those behind, nor the
spare hat. The cats then take turns, each calling out a single number from the
set {0..*n*}, without repeating any number previously called, and without any
other communication. Although the first call is allowed to be wrong, the
remaining cats always call out the numbers on their own hats.

How do they do this? `Puzzle.thy` has the answer, with a proof in
[Isabelle/HOL][]. There is a PDF rendering of the entire proof, with detailed
commentary, in the `document` folder.

The `extras` folder contains miscellaneous proofs, including:

- a more direct, bottom-up version of the main proof, in
  `Puzzle_Bottom_Up.thy`.
- a proof that the `parity` function calculates the evenness of the number of
  inversions, in `Parity_Inversions.thy`.
- a proof that `parity` can be calculated as a side-effect of a merge sort,
  in `Parity_Merge_Sort.thy`.

The `lib` folder contains:

- A handful of lemmas about lists and sets, in `Lib.thy`.
- Some syntax for presenting theorems in rule format, in
  `LaTeX_Rule_Sugar.thy`. This was taken from the Isabelle/HOL distribution,
  which has a BSD-style license.

[Isabelle/HOL]: https://isabelle.in.tum.de/
