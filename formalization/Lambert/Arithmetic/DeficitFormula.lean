import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Lambert.Arithmetic.FiniteDeficitSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith

/-! # Exact affine formulas between the breakpoints of a deficit sum -/
namespace Lambert
open Finset

/-- Between consecutive multiples of the spacing, a finite deficit sum has an exact arithmetic-progression formula. -/
theorem sum_deficits_affine (H n m : ℕ) (hn : 0 < n)
    (hlo : m*n ≤ H) (hhi : H ≤ (m+1)*n) :
    2 * ((∑ r ∈ range H, (H-(r+1)*n) : ℕ) : ℝ) =
      (m : ℝ) * (2*H-(m+1)*n) := by
  have hm : m ≤ H := (Nat.le_mul_of_pos_right m hn).trans hlo
  have hs : (∑ r ∈ range H, (H-(r+1)*n)) = ∑ r ∈ range m, (H-(r+1)*n) := by
    symm
    apply sum_subset (range_mono hm)
    intro r _ hr
    have hmr : m ≤ r := by simpa only [mem_range, not_lt] using hr
    have he := Nat.mul_le_mul_right n (show m+1 ≤ r+1 by omega)
    omega
  rw [hs, Nat.cast_sum]
  have ht (r : ℕ) (hr : r ∈ range m) :
      ((H-(r+1)*n : ℕ) : ℝ) = H-((r : ℝ)+1)*n := by
    have he := (Nat.mul_le_mul_right n (show r+1 ≤ m by simpa using hr)).trans hlo
    push_cast [he]
    rfl
  rw [sum_congr rfl ht]
  rw [sum_sub_distrib, ← sum_mul, sum_add_distrib]
  simp only [sum_const, card_range, nsmul_eq_mul]
  have he (t : ℕ) : 2 * (∑ r ∈ range t, (r : ℝ)) = (t : ℝ)*(t-1) := by
    induction t with
    | zero => simp
    | succ m ih => rw [sum_range_succ]; push_cast; nlinarith
  nlinarith [he m]

end Lambert
