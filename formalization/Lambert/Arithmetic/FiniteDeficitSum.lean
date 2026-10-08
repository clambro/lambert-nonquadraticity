import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Finite positive-part sums

Splitting a finite deficit sum into even and odd indices isolates the terms
used in local determinant cancellation.
-/

namespace Lambert

open Finset

/-- Extending a deficit sum beyond its natural support does not change it. -/
theorem sum_deficits_cutoff (h n T : ℕ) (hn : 0 < n) (hT : h ≤ T) :
    ∑ k ∈ range T, (h - (k + 1) * n) = ∑ k ∈ range h, (h - (k + 1) * n) := by
  apply eventually_constant_sum
  · intro k hk
    have he : k + 1 ≤ (k + 1) * n := Nat.le_mul_of_pos_right _ hn
    omega
  · exact hT

/-- Splitting a deficit sum separates even multiples and the odd tail. -/
theorem sum_deficits_even_odd (h n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range h, (h - (k + 1) * n) =
      (∑ k ∈ range h, (h - (k + 1) * (2 * n))) + (h - n) +
        ∑ k ∈ range h, (h - (2 * k + 3) * n) := by
  have split (f : ℕ → ℕ) (t : ℕ) :
      ∑ k ∈ range (2 * t), f k =
        (∑ k ∈ range t, f (2 * k)) + ∑ k ∈ range t, f (2 * k + 1) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show 2 * (t + 1) = (2 * t + 1) + 1 by omega]
      simp only [sum_range_succ, ih]
      omega
  have hs := split (fun k => h - (k + 1) * n) h
  rw [sum_deficits_cutoff h n (2 * h) hn (by omega)] at hs
  have heven : (∑ k ∈ range h, (h - (2 * k + 1 + 1) * n)) =
      ∑ k ∈ range h, (h - (k + 1) * (2 * n)) := by
    apply sum_congr rfl
    intro k _
    congr 1
    ring
  have hodd : (∑ k ∈ range h, (h - (2 * k + 1) * n)) =
      (h - n) + ∑ k ∈ range h, (h - (2 * k + 3) * n) := by
    have ht := sum_range_succ' (fun k => h - (2 * k + 1) * n) h
    rw [sum_range_succ] at ht
    have hz : h - (2 * h + 1) * n = 0 := by
      have he : 2 * h + 1 ≤ (2 * h + 1) * n := Nat.le_mul_of_pos_right _ hn
      omega
    simp only [hz, add_zero, mul_zero, zero_add, one_mul] at ht
    rw [ht, add_comm]
    congr 1
  rw [heven, hodd] at hs
  omega

end Lambert
