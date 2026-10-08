import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

/-! # Denominator-free sums of quadratic polynomials -/
namespace Lambert
open Finset

/-- Six times a quadratic sum over a natural interval equals the difference of its integer-coefficient cubic antiderivative. -/
theorem six_mul_sum_quadratic_Ico {R : Type*} [CommRing R] (a b c : R)
    (l u : ℕ) (hlu : l ≤ u) :
    6 * (∑ r ∈ Ico l u, (a * (r : R) ^ 2 + b * r + c)) =
      (2 * a * (u : R) ^ 3 + 3 * (b - a) * u ^ 2 + (a - 3 * b + 6 * c) * u) -
      (2 * a * (l : R) ^ 3 + 3 * (b - a) * l ^ 2 + (a - 3 * b + 6 * c) * l) := by
  let F : ℕ → R := fun r => 2 * a * (r : R) ^ 3 + 3 * (b - a) * r ^ 2 +
    (a - 3 * b + 6 * c) * r
  calc
    _ = ∑ r ∈ Ico l u, (F (r + 1) - F r) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      dsimp [F]
      push_cast
      ring
    _ = F u - F l := sum_Ico_sub _ hlu
    _ = _ := rfl

theorem sum_range_pairs (f : ℕ → ℤ) (s : ℕ) :
    (∑ r ∈ range (2 * s), f r) = ∑ i ∈ range s, (f (2 * i) + f (2 * i + 1)) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show 2 * (s + 1) = 2 * s + 1 + 1 by omega]
    simp only [sum_range_succ, ih]
    ring


theorem six_mul_sum_neg_consecutive (b : ℤ) (s : ℕ) :
    6 * (∑ t ∈ range s, -((b + 2 * t) * (b + 2 * t + 1))) =
      -6 * s * (b ^ 2 + b) - (12 * b + 6) * s * (s - 1) -
        4 * s * (s - 1) * (2 * s - 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [sum_range_succ]
    push_cast
    linear_combination ih



end Lambert
