import Lambert.Refinement.IntegerReal
import Lambert.Determinants.ComplexBound

/-! # Complex specialization and growth of integer Lambert certificates -/
namespace Lambert
noncomputable section
open Polynomial

/-- Complexifying the integer certificate preserves its exact scalar-times-determinant identity. -/
theorem lambertRefinementSpecializedIntegerPolynomial_map_complex (N : ℕ) (a b : ℤ)
    (hb : b ≠ 0) (hq : (1 : ℚ) < (a : ℚ) / b) :
    (lambertRefinementSpecializedIntegerPolynomial N a b).map (Int.castRingHom ℂ) =
      C (lambertRefinementIntegerScale N a b : ℂ) *
        lambertRefinementNormalizedDeterminant (((a : ℝ) / b : ℝ) : ℂ) N := by
  simpa only [Polynomial.map_mul, Polynomial.map_C, lambertRefinementNormalizedDeterminant_map,
    Polynomial.map_map, RingHom.eq_intCast', map_intCast, Polynomial.map_intCast, Complex.ofRealHom_eq_coe]
    using congrArg (Polynomial.map Complex.ofRealHom)
      (lambertRefinementSpecializedIntegerPolynomial_map_real N a b hb hq)

/-- An integer Lambert certificate has a complex logarithmic upper bound given by its clearing scale and an explicit quadratic window cost. -/
def lambertRefinementComplexLogBound (N : ℕ) (a b : ℤ) (z : ℂ) : ℝ :=
  Real.log (lambertRefinementIntegerScale N a b : ℝ) +
    (516*N : ℝ)^2 + 516*N*(1+‖z‖+(1084*N)*(((a : ℝ)/b)-1)⁻¹) -
      516*N*Real.log (geometricProductFloor (((a : ℝ)/b)⁻¹))

/-- The explicit complex bound controls every integer Lambert certificate at positive ordered integer base coordinates. -/
theorem lambertRefinementComplexLogBound_bound (N : ℕ) (a b : ℤ)
    (hb : 0 < b) (hab : b < a) (z : ℂ) :
    ‖(lambertRefinementSpecializedIntegerPolynomial N a b).eval₂ (Int.castRingHom ℂ) z‖ ≤
      Real.exp (lambertRefinementComplexLogBound N a b z) := by
  have hq : (1 : ℝ) < (a : ℝ)/b := (one_lt_div (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)
  have hqQ : (1 : ℚ) < (a : ℚ)/b := (one_lt_div (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)
  rw [eval₂_eq_eval_map, lambertRefinementSpecializedIntegerPolynomial_map_complex _ a b hb.ne' hqQ,
    eval_mul, eval_C, norm_mul]
  have hJ := lambertRefinementIntegerScale_pos N a b hb hab
  have he : ‖(lambertRefinementIntegerScale N a b : ℂ)‖ =
      (lambertRefinementIntegerScale N a b : ℝ) := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hJ]
  rw [he]
  have hnorm : (1 : ℝ) < ‖(((a : ℝ)/b : ℝ) : ℂ)‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hq)] using hq
  have hbound := lambertAugmented_normalized_norm_le_exp_of_one_lt_norm
    (((a : ℝ)/b : ℝ) : ℂ) hnorm z (500*N) (27*N) (16*N) (41*N)
  simp only [show 500*N+16*N=516*N by omega,
    show 500*N+41*N+27*N+516*N=1084*N by omega,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hq)] at hbound
  change ‖(lambertRefinementNormalizedDeterminant _ N).eval z‖ ≤ _ at hbound
  apply (mul_le_mul_of_nonneg_left hbound hJ.le).trans_eq
  rw [← Real.exp_log hJ, ← Real.exp_add]
  congr 1
  dsimp [lambertRefinementComplexLogBound]
  push_cast
  ring

end
end Lambert
