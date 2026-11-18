import Mathlib

/-!
# Dot diagrams

A *dot diagram* is a finite set of cells of the grid `ℕ × ℕ`; each cell is one dot,
and a dot stands for the natural number `1`. The number a diagram represents is
its cardinality.

Shapes (`square`, `ell`, …) are definitions, and diagrammatic *operations*
(in Jamnik's sense: "split an ell off a square", …) are lemmas stating that a
shape is a disjoint union of other shapes. A faithful proof is then a chain of
such operations followed by counting.

Coordinates: a cell is `(i, j)` with `i` the row and `j` the column.
-/

namespace VerifiedImage.Dots

open Finset

/-- A dot diagram: a finite set of grid cells. -/
abbrev Diagram := Finset (ℕ × ℕ)

/-! ## Shapes -/

/-- The `n × n` square of dots: cells `(i, j)` with `i, j < n`. -/
def square (n : ℕ) : Diagram := range n ×ˢ range n

/-- Bottom arm of the `k`-th ell: row `k`, columns `0 … k` (that is `k + 1` dots). -/
def ellRow (k : ℕ) : Diagram := {k} ×ˢ range (k + 1)

/-- Side arm of the `k`-th ell: column `k`, rows `0 … k-1` (that is `k` dots). -/
def ellCol (k : ℕ) : Diagram := range k ×ˢ {k}

/-- The `k`-th ell (gnomon): the L-shaped layer that turns `square k` into
`square (k + 1)`. -/
def ell (k : ℕ) : Diagram := ellRow k ∪ ellCol k

/-! ## Counting basic shapes -/

/-- Reading a square: `n` rows of `n` dots. -/
theorem card_square (n : ℕ) : (square n).card = n * n := by
  simp [square, card_product]

theorem card_ellRow (k : ℕ) : (ellRow k).card = k + 1 := by
  simp [ellRow]

theorem card_ellCol (k : ℕ) : (ellCol k).card = k := by
  simp [ellCol]

theorem disjoint_ellRow_ellCol (k : ℕ) : Disjoint (ellRow k) (ellCol k) := by
  rw [disjoint_left]
  rintro ⟨i, j⟩ h₁ h₂
  simp [ellRow, ellCol] at h₁ h₂
  omega

/-- An ell is made of its two arms: `(k + 1) + k = 2k + 1` dots. -/
theorem card_ell (k : ℕ) : (ell k).card = 2 * k + 1 := by
  rw [ell, card_union_of_disjoint (disjoint_ellRow_ellCol k), card_ellRow, card_ellCol]
  omega

/-! ## Operations -/

/-- Operation *split an ell*: `square (n + 1)` is `square n` with the `n`-th ell
attached. -/
theorem square_succ (n : ℕ) : square (n + 1) = square n ∪ ell n := by
  ext ⟨i, j⟩
  simp [square, ell, ellRow, ellCol]
  omega

theorem disjoint_square_ell (n : ℕ) : Disjoint (square n) (ell n) := by
  rw [disjoint_left]
  rintro ⟨i, j⟩ h₁ h₂
  simp [square, ell, ellRow, ellCol] at h₁ h₂
  omega

/-- Distinct ells never overlap. -/
theorem disjoint_ell {a b : ℕ} (h : a ≠ b) : Disjoint (ell a) (ell b) := by
  rw [disjoint_left]
  rintro ⟨i, j⟩ h₁ h₂
  simp [ell, ellRow, ellCol] at h₁ h₂
  omega

/-- Recursive decomposition (the schematic proof): repeatedly splitting ells
exhausts the square, so `square n` is the union of the ells `0 … n-1`. -/
theorem square_eq_biUnion_ell (n : ℕ) : square n = (range n).biUnion ell := by
  induction n with
  | zero => simp [square]
  | succ n ih => rw [square_succ, ih, range_add_one, biUnion_insert, union_comm]

end VerifiedImage.Dots
