import Mathlib.Tactic

/-! # Exponential bounds for weighted determinants -/
namespace Lambert
open Finset Matrix

/-- Entrywise exponential bounds and a bound on every permutation weight give an exponential determinant bound. -/
theorem norm_det_le_exp_of_permutation_bound (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (w : Fin n → Fin n → ℝ) (C S : ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ Real.exp (C + w i j))
    (hw : ∀ σ : Equiv.Perm (Fin n), (∑ j, w (σ j) j) ≤ S) :
    ‖A.det‖ ≤ Real.exp ((n : ℝ) ^ 2 + n * C + S) := by
  have hp (σ : Equiv.Perm (Fin n)) :
      ‖(Equiv.Perm.sign σ : ℂ) * ∏ j, A (σ j) j‖ ≤ Real.exp (n * C + S) := by
    have hs : ‖(Equiv.Perm.sign σ : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with he | he <;> simp [he]
    rw [norm_mul, hs, one_mul, norm_prod]
    calc
      _ ≤ ∏ j, Real.exp (C + w (σ j) j) := prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hA _ _)
      _ = Real.exp (n * C + ∑ j, w (σ j) j) := by
        rw [← Real.exp_sum, sum_add_distrib]
        simp
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [hw σ])
  have hf : (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by
    calc
      _ ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
      _ ≤ (Real.exp n) ^ n := pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (n : ℝ)]) n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc
    ‖A.det‖ ≤ ∑ σ : Equiv.Perm (Fin n), ‖(Equiv.Perm.sign σ : ℂ) * ∏ j, A (σ j) j‖ := by
      rw [det_apply']; exact norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), Real.exp (n * C + S) := sum_le_sum (fun σ _ => hp σ)
    _ = n.factorial * Real.exp (n * C + S) := by simp [Fintype.card_perm]
    _ ≤ Real.exp ((n : ℝ) ^ 2) * Real.exp (n * C + S) := mul_le_mul_of_nonneg_right hf (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Lambert
