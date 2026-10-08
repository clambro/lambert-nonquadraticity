import Lambert.Determinants.Moments
import Lambert.Determinants.MomentIntegral

/-! # Positive measures on movable Lambert pole windows -/
namespace Lambert
noncomputable section
open Polynomial MeasureTheory Finset Matrix
open scoped Classical

/-- The real pole-window measure weights the inverse-base geometric atoms by the
reciprocal product of the positive factors `q^(k+j)-t`. -/
def lambertPoleMeasure (q : ℝ) (k L : ℕ) : Measure ℝ :=
  nodalMomentMeasure (geometricMomentMeasure q⁻¹) univ (fun j : Fin L => q ^ (k + j.val))

private theorem below (q : ℝ) (hq : 1 < q) (k L : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc 0 q⁻¹) (j : Fin L) : t < q ^ (k + j.val) :=
  ht.2.trans_lt ((inv_lt_one_of_one_lt₀ hq).trans_le (one_le_pow₀ hq.le))

/-- At the actual Lambert value, every pole-window numerator has its positive nodal integral. -/
theorem lambertNumeratorFunctional_eval_integral (q : ℝ) (hq : 1 < q) (k L : ℕ) (p : ℝ[X]) :
    (lambertNumeratorFunctional q k L p).eval (lambertValue q) =
      ∫ t, p.eval t ∂lambertPoleMeasure q k L := by
  have hu := inv_pos.mpr (zero_lt_one.trans hq)
  have hu1 := inv_lt_one_of_one_lt₀ hq
  let := geometricMomentMeasure_isFinite q⁻¹ hu.le hu1
  rw [lambertPoleMeasure, integral_polynomial_nodalFunctional _ isCompact_Icc
    (geometricMomentMeasure_ae_mem _ hu.le hu1.le) (fun j : Fin L => q ^ (k + j.val))
    (fun i j hij => Fin.ext (Nat.add_left_cancel ((pow_right_strictMono₀ hq).injective hij))) (below q hq k L)]
  simp only [lambertNumeratorFunctional, LinearMap.smul_apply, eval_smul,
    nodalFunctional_apply, eval_add, eval_finsetSum, eval_smul, eval_neg,
    eval_sub, eval_X, eval_C, smul_eq_mul]
  rw [lambertPolynomialFunctional_eval_integral q hq]
  simp only [compactPolynomialIntegral, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
  congr 1
  congr 1
  apply sum_congr rfl
  intro j _
  have he := markovTransform_geometric_orbit q⁻¹ hu hu1 (k + j.val)
  simp only [inv_inv, inv_pow, one_div, inv_inv] at he
  rw [← lambertValue_eq_markov q hq] at he
  rw [he]

/-- Specializing any shifted Lambert determinant gives its shifted moment integral determinant. -/
theorem lambertPoleDeterminant_eval_gram (q : ℝ) (hq : 1 < q) (h k L s : ℕ) :
    (lambertPoleDeterminant q h k L s).eval (lambertValue q) =
      (Matrix.of fun i j : Fin h => ∫ t, t ^ (i.val + j.val + s) ∂lambertPoleMeasure q k L).det := by
  have he := (Polynomial.evalRingHom (lambertValue q)).map_det
    (Matrix.of fun i j : Fin h => lambertPoleMoment q k L (i.val + j.val + s))
  change (Polynomial.evalRingHom (lambertValue q)) _ = _
  unfold lambertPoleDeterminant
  rw [he]
  congr 1
  apply Matrix.ext
  intro i j
  simpa only [coe_evalRingHom, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    lambertPoleMoment, eval_pow, eval_X] using
    lambertNumeratorFunctional_eval_integral q hq k L (X ^ (i.val + j.val + s))

end
end Lambert
