import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq

/-! # Counting residue tails in finite intervals -/
namespace Lambert
open Finset

/-- The number of indices below M whose residue lies at or above d splits into complete periods and one final partial period. -/
theorem sum_residue_tail (M n d : ℕ) (hn : 0 < n) (hd : d ≤ n) :
    (∑ v ∈ range M, if d ≤ v % n then 1 else 0) =
      M/n * (n-d) + (M%n-d) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih]
    have hr := Nat.mod_lt M hn
    by_cases hw : M%n+1=n
    · have hm : (M+1)%n=0 := by
        rw [← Nat.mod_add_mod, hw, Nat.mod_self]
      rw [Nat.succ_div_of_mod_eq_zero hm, hm, Nat.add_mul]
      split_ifs <;> omega
    · have hm : (M+1)%n=M%n+1 := by
        rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt (by omega)]
      rw [Nat.succ_div_of_mod_ne_zero (by omega), hm]
      split_ifs <;> omega

/-- Removing the initial period from a residue-tail count leaves the harmonic-index-positive prefix count. -/
theorem sum_positive_residue_tail (M n d : ℕ) (hn : 0 < n) (hd : d ≤ n) :
    (∑ v ∈ range M, if n ≤ v ∧ d ≤ v%n then 1 else 0) =
      if M < n then 0 else (M/n-1)*(n-d)+(M%n-d) := by
  by_cases hM : M < n
  · rw [if_pos hM]
    apply sum_eq_zero
    intro v hv
    simp only [mem_range] at hv
    simp [show ¬n ≤ v by omega]
  · rw [if_neg hM]
    have hMn : n ≤ M := by omega
    have hsum : (∑ v ∈ range M, if d ≤ v%n then 1 else 0) =
        (n-d) + ∑ v ∈ range M, if n ≤ v ∧ d ≤ v%n then 1 else 0 := by
      conv_lhs => rw [show M=n+(M-n) by omega, sum_range_add]
      rw [sum_residue_tail n n d hn hd]
      simp only [Nat.div_self hn, one_mul, Nat.mod_self, Nat.zero_sub, add_zero]
      congr 1
      conv_rhs => rw [show M=n+(M-n) by omega, sum_range_add]
      have hz : (∑ v ∈ range n, if n ≤ v ∧ d ≤ v%n then 1 else 0)=0 := by
        apply sum_eq_zero
        intro v hv
        simp [show ¬n ≤ v by simpa using hv]
      rw [hz, zero_add]
      apply sum_congr rfl
      intro v _
      simp [show n ≤ n+v by omega]
    rw [sum_residue_tail M n d hn hd] at hsum
    have hdiv : 1 ≤ M/n := Nat.div_pos hMn hn
    have he : M/n * (n-d) = (M/n-1)*(n-d)+(n-d) := by
      calc
        _ = (M/n-1+1)*(n-d) := by rw [show M/n-1+1=M/n by omega]
        _ = _ := by rw [Nat.add_mul, Nat.one_mul]
    omega

end Lambert
