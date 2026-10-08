import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Lambert.Arithmetic.QuadraticSum

/-!
# Constrained node costs at the zero place

The costs are doubled to keep all arithmetic integral. Pole nodes have capacity
two and tail nodes have capacity one. The pointwise minimizer respects the
pole capacity and never enters the tail.
-/

namespace Lambert

/-- Twice the pole contribution at position `r` is an integral quadratic in
its node index. -/
def lambertZeroPoleCost (h r j : ℤ) : ℤ := j * (j + 2 * h - 1 - 4 * r)

/-- The constrained optimal node is the larger of the capacity lower bound
and the unconstrained quadratic minimizer. -/
def lambertZeroOptimalNode (h r : ℤ) : ℤ := max (r / 2) (2 * r - h)

/-- The optimal node minimizes the quadratic cost among indices allowed by
the capacity-two lower bound. -/
theorem lambertZeroPoleCost_min (h r j : ℤ) (hj : r / 2 ≤ j) :
    lambertZeroPoleCost h r (lambertZeroOptimalNode h r) ≤ lambertZeroPoleCost h r j := by
  unfold lambertZeroPoleCost lambertZeroOptimalNode
  by_cases hm : r / 2 ≤ 2 * r - h
  · rw [max_eq_right hm]
    by_cases hle : j ≤ 2 * r - h
    · nlinarith [sq_nonneg (j - (2 * r - h))]
    · have hj' : 2 * r - h + 1 ≤ j := by omega
      nlinarith [mul_nonneg (show 0 ≤ j - (2 * r - h) by omega)
        (show 0 ≤ j - (2 * r - h) - 1 by omega)]
  · rw [max_eq_left (by omega)]
    by_cases he : j = r / 2
    · rw [he]
    · have h1 : 0 ≤ j - r / 2 := by omega
      have h2 : 0 ≤ j + r / 2 + 2 * h - 1 - 4 * r := by omega
      nlinarith [mul_nonneg h1 h2]

open Finset

private theorem optimal_low (s e i : ℕ) (he : e ≤ 2) (hi : i < s) (b : ℕ) (hb : b ≤ 1) :
    lambertZeroOptimalNode (3 * s + e) (2 * i + b) = i := by
  unfold lambertZeroOptimalNode
  omega

private theorem optimal_high (s e t : ℕ) (he : e ≤ 2) (ht : 0 < t) :
    lambertZeroOptimalNode (3 * s + e) (2 * s + t) = s + 2 * t - e := by
  unfold lambertZeroOptimalNode
  omega

private theorem low_pair_sum (h : ℤ) (s : ℕ) :
    6 * (∑ i ∈ range s, 2 * (i : ℤ) * (2 * h - 3 - 7 * i)) =
      (s : ℤ) * (s - 1) * (12 * h - 28 * s - 4) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [sum_range_succ]
    push_cast
    linear_combination ih


/-- The optimal doubled costs have the exact residue-class cubic sum. -/
theorem lambertZeroOptimalCost_sum (s e : ℕ) (he : e ≤ 2) :
    6 * (∑ r ∈ range (3 * s + e),
      lambertZeroPoleCost (3 * s + e) r (lambertZeroOptimalNode (3 * s + e) r)) =
      -18 * (s : ℤ) ^ 3 - 18 * e * s ^ 2 + (6 - 6 * (e : ℤ) ^ 2) * s := by
  let f : ℕ → ℤ := fun r =>
    lambertZeroPoleCost (3 * s + e) r (lambertZeroOptimalNode (3 * s + e) r)
  change 6 * (∑ r ∈ range (3 * s + e), f r) = _
  rw [show 3 * s + e = 2 * s + (s + e) by omega, sum_range_add, sum_range_pairs]
  have hlo : (∑ i ∈ range s, (f (2 * i) + f (2 * i + 1))) =
      ∑ i ∈ range s, 2 * (i : ℤ) * (2 * (3 * s + e) - 3 - 7 * i) := by
    apply sum_congr rfl
    intro i hi
    dsimp only [f]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have h0 := optimal_low s e i he (mem_range.mp hi) 0 (by omega)
    have h1 := optimal_low s e i he (mem_range.mp hi) 1 (by omega)
    simp only [Nat.cast_zero, add_zero] at h0
    rw [h0, h1]
    unfold lambertZeroPoleCost
    ring
  have hhi : (∑ t ∈ range (s + e), f (2 * s + t)) =
      (∑ t ∈ range (s + e), -(((s : ℤ) - e + 2 * t) * (s - e + 2 * t + 1))) +
        (if e = 2 then 2 else 0) := by
    by_cases hn : s + e = 0
    · have hs : s = 0 := by omega
      have he0 : e = 0 := by omega
      simp [hs, he0]
    · have hc : (∑ t ∈ range (s + e), if t = 0 ∧ e = 2 then (2 : ℤ) else 0) =
          if e = 2 then 2 else 0 := by
        by_cases he2 : e = 2 <;> simp [he2]
      rw [← hc, ← sum_add_distrib]
      apply sum_congr rfl
      intro t ht
      dsimp only [f]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      by_cases ht0 : t = 0
      · subst t
        have hm : lambertZeroOptimalNode (3 * s + e) (2 * s + 0) = s := by
          unfold lambertZeroOptimalNode
          omega
        simp only [Nat.cast_zero]
        rw [hm]
        unfold lambertZeroPoleCost
        interval_cases e <;> norm_num <;> ring
      · rw [optimal_high s e t he (by omega)]
        simp only [ht0, false_and, ↓reduceIte, add_zero]
        unfold lambertZeroPoleCost
        ring
  rw [hlo, hhi]
  have hl := low_pair_sum (3 * s + e) s
  have hh := six_mul_sum_neg_consecutive ((s : ℤ) - e) (s + e)
  push_cast at hh
  interval_cases e <;> norm_num at hl hh ⊢ <;> linear_combination hl + hh

end Lambert
