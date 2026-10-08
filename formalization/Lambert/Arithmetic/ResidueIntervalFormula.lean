import Mathlib.Tactic.Ring
import Lambert.Arithmetic.ResidueIntervalCount
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Affine formulas for residue-tail prefix counts -/
namespace Lambert
open Finset

/-- Natural subtraction becomes the positive part of real subtraction after casting. -/
theorem natCast_sub_eq_max (a b : ℕ) : ((a-b : ℕ) : ℝ) = max ((a : ℝ)-b) 0 := by
  by_cases h : b ≤ a
  · have he : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [Nat.cast_sub h, max_eq_left (by linarith)]
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero, max_eq_right (by
      have he : (a : ℝ) ≤ b := by exact_mod_cast (show a ≤ b by omega)
      linarith)]

/-- An inclusive period cell gives the exact real residue-prefix count, including its final partial period. -/
theorem sum_positive_residue_tail_cell (M n d m : ℕ) (hn : 0 < n) (hd : d ≤ n)
    (hm : 0 < m) (hlo : m*n ≤ M) (hhi : M ≤ (m+1)*n) :
    ((∑ v ∈ range M, if n ≤ v ∧ d ≤ v%n then 1 else 0 : ℕ) : ℝ) =
      ((m : ℝ)-1)*((n : ℝ)-d)+max ((M : ℝ)-m*n-d) 0 := by
  have hMn : n ≤ M := (Nat.le_mul_of_pos_left n hm).trans hlo
  rw [sum_positive_residue_tail M n d hn hd, if_neg (by omega)]
  by_cases he : M=(m+1)*n
  · subst M
    rw [Nat.mul_div_left _ hn, Nat.mul_mod_left]
    simp only [Nat.add_sub_cancel, Nat.zero_sub, add_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [Nat.cast_sub hd]
    have hz : 0 ≤ ((m : ℝ)+1)*n-m*n-d := by
      have hdn : (d : ℝ) ≤ n := by exact_mod_cast hd
      nlinarith
    rw [max_eq_left hz]
    ring
  · have hq : M/n=m := Nat.div_eq_of_lt_le hlo (by omega)
    rw [hq, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (show 1 ≤ m by omega),
      Nat.cast_one, Nat.cast_sub hd, natCast_sub_eq_max]
    have hr : (M%n : ℝ) = (M : ℝ)-m*n := by
      have ht := Nat.div_add_mod M n
      rw [hq] at ht
      have htR : (n : ℝ)*m+(M%n : ℕ)=M := by exact_mod_cast ht
      nlinarith
    rw [hr]

end Lambert
