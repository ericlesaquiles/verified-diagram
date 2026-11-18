# Design log

Running record of design decisions and why they were made. Newest at the bottom.

## Goal

Option (b): formalize the *argument of the picture*, not just the theorem it depicts.

```
image  ⇄  IR  ⇄  Lean
```

## Plan

See the research plan in `README.md` (§5 Work plan).

## Rules for a "faithful" proof

- The main identity must come from operations on diagrams plus counting,
  never from `omega` / `ring` / `nlinarith` on the identity itself.
- Arithmetic tactics are allowed for local facts (membership of a single cell,
  `(k+1) + k = 2k+1`).
- `statement` is a separate `def`, so it can be reviewed independently of the proof.
- `#print axioms` must show only `propext`, `Classical.choice`, `Quot.sound`.

## Decisions

### 2026-11-17: Discrete diagrams are `Finset (ℕ × ℕ)`
A dot is a grid cell; the number represented is the cardinality. Shapes are
definitions, operations are "shape = disjoint union of shapes" lemmas
(Jamnik's operations, Diamond ch. 6). Recursive schematic proofs become
ordinary induction, so no ω-rule is needed.

### 2026-11-17: Sum of odds indexed from 0
Stated as `∑ k ∈ range n, (2k+1) = n * n` (Mathlib style) rather than
`1 + 3 + ⋯ + (2n−1)`. Ell `k` has `2k+1` dots.

## Open questions

- Should the IR record *views* of a shape (square as rows / columns / ells)
  explicitly, as Diamond does, or derive them from the operation?
- How to represent rotation/reflection (bijections preserving cardinality)?
  Needed for Tri(n) proofs.
