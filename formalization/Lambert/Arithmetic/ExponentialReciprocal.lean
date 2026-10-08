import Mathlib.NumberTheory.Bernoulli

/-!
# Regularized exponential reciprocals

Multiplication by the formal parameter removes the possible simple pole of
`1 / (z exp(a ε) - 1)`. Bernoulli's generating series treats the singular case.
-/

namespace Lambert

noncomputable section

open PowerSeries
open scoped Classical

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The regularized exponential reciprocal represents the formal parameter
divided by `z exp(a ε) - 1`, for nonzero scale `a`. -/
def exponentialReciprocal (z a : K) : PowerSeries K :=
  if z = 1 then C a⁻¹ * rescale a (bernoulliPowerSeries K)
  else X * rescale a ((C z * exp K - 1)⁻¹)

/-- Regularization gives the exact reciprocal identity at every nonzero scale. -/
theorem exponentialReciprocal_mul (z a : K) (ha : a ≠ 0) :
    exponentialReciprocal z a * (C z * rescale a (exp K) - 1) = X := by
  classical
  by_cases hz : z = 1
  · subst z
    simp only [exponentialReciprocal, ↓reduceIte, map_one, one_mul]
    rw [mul_assoc, ← map_one (rescale a), ← map_sub, ← map_mul,
      bernoulliPowerSeries_mul_exp_sub_one, rescale_X, ← mul_assoc, ← map_mul]
    simp [ha]
  · simp only [exponentialReciprocal, if_neg hz]
    have hc : constantCoeff (C z * exp K - 1) ≠ 0 := by simpa using sub_ne_zero.mpr hz
    have he := congrArg (rescale a) (PowerSeries.inv_mul_cancel (C z * exp K - 1) hc)
    have hC : rescale a (C z) = C z := by ext r; simp [coeff_rescale, coeff_C]; split_ifs <;> simp_all
    rw [map_mul, map_sub, map_mul, hC, map_one] at he
    rw [mul_assoc, he, mul_one]

/-- The residue of the exponential reciprocal is the inverse scale at phase one
and zero at every other phase. -/
theorem exponentialReciprocal_coeff_zero (z a : K) :
    coeff 0 (exponentialReciprocal z a) = if z = 1 then a⁻¹ else 0 := by
  classical
  by_cases hz : z = 1 <;>
    simp [exponentialReciprocal, hz, coeff_rescale, bernoulliPowerSeries, bernoulli_zero]

/-- The inverse-power exponential kernel represents the negative `j`th power
of a nonzero phased exponential. -/
def exponentialInversePower (z : K) (j : ℕ) : PowerSeries K :=
  C (z⁻¹ ^ j) * rescale (-(j : K)) (exp K)

/-- The inverse-power exponential kernel cancels the corresponding positive power. -/
theorem exponentialInversePower_mul (z : K) (hz : z ≠ 0) (j : ℕ) :
    exponentialInversePower z j * (C z * exp K) ^ j = 1 := by
  rw [exponentialInversePower, mul_pow, exp_pow_eq_rescale_exp, ← map_pow]
  calc
    _ = (C (z⁻¹ ^ j) * C (z ^ j)) *
        (rescale (-(j : K)) (exp K) * rescale (j : K) (exp K)) := by ring
    _ = 1 := by
      rw [← map_mul, ← mul_pow, inv_mul_cancel₀ hz, one_pow, map_one,
        exp_mul_exp_eq_exp_add, neg_add_cancel]
      simp

/-- Multiplying a regularized reciprocal by a rescaled series preserves the
homogeneous dependence of all positive-order coefficients on the scale. -/
theorem exponentialReciprocal_twisted_coeff_succ (z a : K) (ha : a ≠ 0)
    (E : PowerSeries K) (r : ℕ) :
    coeff (r + 1) (rescale a E * exponentialReciprocal z a) = a ^ r *
      (if z = 1 then coeff (r + 1) (E * bernoulliPowerSeries K)
       else coeff r (E * (C z * exp K - 1)⁻¹)) := by
  by_cases hz : z = 1
  · rw [exponentialReciprocal, if_pos hz, if_pos hz]
    rw [show rescale a E * (C a⁻¹ * rescale a (bernoulliPowerSeries K)) =
      C a⁻¹ * rescale a (E * bernoulliPowerSeries K) by rw [map_mul]; ring]
    rw [coeff_C_mul, coeff_rescale, pow_succ]
    rw [← mul_assoc, mul_comm (a ^ r), inv_mul_cancel_left₀ ha]
  · rw [exponentialReciprocal, if_neg hz, if_neg hz]
    rw [show rescale a E * (X * rescale a (C z * exp K - 1)⁻¹) =
      X * rescale a (E * (C z * exp K - 1)⁻¹) by rw [map_mul]; ring]
    rw [coeff_succ_X_mul, coeff_rescale]

/-- Twisting a regularized reciprocal by the matching inverse power leaves
its residue unchanged. -/
theorem exponentialReciprocal_inversePower_coeff_zero (z a : K) (j : ℕ) :
    coeff 0 (rescale a (exponentialInversePower z j) * exponentialReciprocal z a) =
      if z = 1 then a⁻¹ else 0 := by
  have hr : constantCoeff (exponentialReciprocal z a) = if z = 1 then a⁻¹ else 0 := by
    simpa only [coeff_zero_eq_constantCoeff] using exponentialReciprocal_coeff_zero z a
  have hc (b : K) (F : PowerSeries K) : constantCoeff (rescale b F) = constantCoeff F := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff]
  rw [coeff_zero_eq_constantCoeff, map_mul, hr]
  by_cases hz : z = 1 <;> simp [exponentialInversePower, hc, hz]

end

end Lambert
