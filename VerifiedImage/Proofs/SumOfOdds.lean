import VerifiedImage.Diagram.Dots

/-!
# Sum of odd numbers  (proofs/sum-of-odds)

`1 + 3 + 5 + ⋯ + (2n - 1) = n²`

**The picture.** An `n × n` square of dots, cut into nested L-shaped layers
(ells). The `k`-th ell has `2k + 1` dots, and the ells `0 … n-1` exactly fill the
square.

**Faithfulness.** The proof follows the picture step by step:
1. each layer is an ell with `2k + 1` dots (`card_ell`),
2. the ells are pairwise disjoint (`disjoint_ell`),
3. together they make up the square (`square_eq_biUnion_ell`),
4. the square has `n * n` dots (`card_square`).
Arithmetic tactics are only used to check individual cells, never for the
identity itself.
-/

namespace VerifiedImage.SumOfOdds

open Finset VerifiedImage.Dots

/-- The theorem the picture depicts, stated independently of its proof. -/
def statement : Prop := ∀ n : ℕ, ∑ k ∈ range n, (2 * k + 1) = n * n

theorem proof : statement := by
  intro n
  calc ∑ k ∈ range n, (2 * k + 1)
      = ∑ k ∈ range n, (ell k).card := by simp [card_ell]
    _ = ((range n).biUnion ell).card :=
        (card_biUnion fun a _ b _ hab => disjoint_ell hab).symm
    _ = (square n).card := by rw [square_eq_biUnion_ell]
    _ = n * n := card_square n

end VerifiedImage.SumOfOdds
