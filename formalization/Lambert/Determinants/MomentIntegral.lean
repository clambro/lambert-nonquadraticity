import Lambert.Analysis.NodalIntegral
import Lambert.Determinants.MomentData
import Lambert.Basic

/-!
# Real Lambert values and the geometric moment integral

The formal unknown is specialized to the convergent Lambert series. Every
polynomial numerator then agrees with integration against the positive nodal measure.
-/
namespace Lambert
noncomputable section
open Polynomial MeasureTheory Finset Matrix
open scoped Classical

/-- The Lambert value is the Markov transform at one of the inverse-base geometric measure. -/
theorem lambertValue_eq_markov (q : ℝ) (hq : 1 < q) :
    lambertValue q = markovTransform (geometricMomentMeasure q⁻¹) 1 := by
  rw [markovTransform_geometricMomentMeasure_eq _ _ (inv_pos.mpr (zero_lt_one.trans hq)).le]
  unfold lambertValue
  apply tsum_congr
  intro n
  simpa only [inv_inv, one_div] using
    (geometricReciprocalMoment_inverse_base q⁻¹ (inv_ne_zero (zero_lt_one.trans hq).ne') (n + 1)).symm

/-- Evaluating the polynomial part of the Lambert functional gives the geometric moment integral. -/
theorem lambertPolynomialFunctional_eval_integral (q : ℝ) (hq : 1 < q) (z : ℝ) (p : ℝ[X]) :
    (lambertPolynomialFunctional q p).eval z = ∫ t, p.eval t ∂geometricMomentMeasure q⁻¹ := by
  have hu := inv_pos.mpr (zero_lt_one.trans hq)
  have hu1 := inv_lt_one_of_one_lt₀ hq
  let := geometricMomentMeasure_isFinite q⁻¹ hu.le hu1
  let μp := compactPolynomialIntegral (geometricMomentMeasure q⁻¹) isCompact_Icc
    (geometricMomentMeasure_ae_mem _ hu.le hu1.le) (fun _ => 1) continuousOn_const
  have he : (Polynomial.leval z).comp (lambertPolynomialFunctional q) = μp := by
    apply Polynomial.lhom_ext'
    intro n
    apply LinearMap.ext
    intro a
    change (lambertPolynomialFunctional q (monomial n a)).eval z = μp (monomial n a)
    rw [show monomial n a = a • (X ^ n : ℝ[X]) by rw [← monomial_one_right_eq_X_pow, smul_monomial]; simp]
    simp only [map_smul, eval_smul, lambertPolynomialFunctional_X_pow, eval_C]
    congr 1
    change 1 / (q ^ (n + 1) - 1) = ∫ t, 1 * (X ^ n : ℝ[X]).eval t ∂geometricMomentMeasure q⁻¹
    simp only [eval_pow, eval_X, one_mul]
    rw [geometricMomentMeasure_moment _ hu.le hu1,
      geometricReciprocalMoment_inverse_base _ hu.ne', inv_inv, one_div]
  have hp := LinearMap.congr_fun he p
  simpa only [LinearMap.comp_apply, Polynomial.leval_apply, μp, compactPolynomialIntegral,
    LinearMap.coe_mk, AddHom.coe_mk, one_mul] using hp


end
end Lambert
