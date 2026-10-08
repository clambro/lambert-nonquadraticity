import Lambert.Determinants.MomentData
import Mathlib.Analysis.Complex.Basic

/-! # Complex growth of Lambert entries -/
namespace Lambert
noncomputable section
open Polynomial Finset Matrix
open scoped Classical

private theorem reciprocal_bound (u : ℂ) (hq : 1 < ‖u‖) (i : ℕ) :
    ‖(1 / (u ^ (i + 1) - 1))‖ ≤ (‖u‖ - 1)⁻¹ := by
  have hp : ‖u‖ ≤ ‖u‖^(i+1) := le_self_pow₀ hq.le (by omega)
  have he := norm_sub_norm_le (u^(i+1)) (1 : ℂ)
  simp only [norm_pow, norm_one] at he
  rw [norm_div, norm_one]
  simpa only [one_div] using one_div_le_one_div_of_le (by linarith : 0<‖u‖-1)
    (show ‖u‖-1 ≤ ‖u^(i+1)-1‖ by linarith)

/-- At a complex base of modulus greater than one, a complex Lambert entry is bounded by its geometric power times a linear prefix bound. -/
theorem lambertPoleEntry_norm_le_of_one_lt_norm (u : ℂ) (hq : 1 < ‖u‖) (z : ℂ) (i j : ℕ) :
    ‖(lambertPoleEntry u i j).eval z‖ ≤
      ‖u‖ ^ (i * j) * (‖z‖ + (i + j : ℕ) * (‖u‖ - 1)⁻¹) := by
  have hq0 := zero_lt_one.trans hq
  have hc : 0 ≤ (‖u‖ - 1)⁻¹ := by positivity
  have hnorm (k : ℕ) : ‖u ^ k‖ = ‖u‖ ^ k := by
    rw [norm_pow]
  induction i with
  | zero =>
    simp only [lambertPoleEntry_zero, eval_sub, eval_X, eval_C, zero_mul, pow_zero, one_mul, zero_add]
    apply (norm_sub_le _ _).trans
    apply add_le_add_right
    unfold geometricMomentPrefix
    calc
      _ ≤ ∑ k ∈ range j, ‖(1 / (u ^ (k + 1) - 1))‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range j, (‖u‖ - 1)⁻¹ := sum_le_sum (fun k _ => reciprocal_bound u hq k)
      _ = _ := by simp
  | succ i ih =>
    rw [lambertPoleEntry_succ, eval_sub, eval_mul, eval_C, eval_C]
    apply (norm_sub_le _ _).trans
    rw [norm_mul, hnorm]
    have hh := mul_le_mul_of_nonneg_left ih (pow_nonneg hq0.le j)
    have hr := reciprocal_bound u hq i
    have ho : 1 ≤ ‖u‖ ^ ((i + 1) * j) := one_le_pow₀ hq.le
    have hp : ‖u‖ ^ ((i + 1) * j) = ‖u‖ ^ j * ‖u‖ ^ (i * j) := by rw [Nat.add_mul, one_mul, pow_add]; ring
    push_cast at hh ⊢
    rw [hp] at ho ⊢
    nlinarith


end
end Lambert
