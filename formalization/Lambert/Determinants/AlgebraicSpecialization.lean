import Lambert.Determinants.CertificateIntegerPolynomial
import Lambert.Determinants.CertificateSpecialization

/-! # Exact polynomial certificates at algebraic and complex bases -/
namespace Lambert
noncomputable section
open Polynomial

/-- Specializing the integer base variable recovers the cleared normalized determinant at every base with distinct powers. -/
theorem lambertCertificateIntegerPolynomial_specialize
    {K : Type} [Field K] [CharZero K] (q : K)
    (hq : Function.Injective (fun n : ℕ => q^n)) (h k : ℕ) :
    (lambertCertificateIntegerPolynomial h k).map (eval₂RingHom (Int.castRingHom K) q) =
      C ((lambertCertificateClearingPolynomial h k).eval₂ (Int.castRingHom K) q) *
        lambertNormalizedDeterminant q h k := by
  have eval_int (p : ℤ[X]) :
      RatFunc.eval (Rat.castHom K) q (integerPolynomialRatFunc p) =
        p.eval₂ (Int.castRingHom K) q := by
    simp only [integerPolynomialRatFunc, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      RatFunc.eval_algebraMap, Algebra.algebraMap_self, RingHom.id_apply, eval₂_map]
    congr 1
    exact Subsingleton.elim _ _
  ext i
  have he := congrArg (RatFunc.eval (Rat.castHom K) q)
    (congrArg (fun p : (RatFunc ℚ)[X] => p.coeff i)
      (lambertCertificateIntegerPolynomial_map h k))
  simp only [coeff_map, coeff_C_mul] at he
  rw [eval_int, RatFunc.eval_mul _ _
    (show (integerPolynomialRatFunc (lambertCertificateClearingPolynomial h k)).denom.eval₂
      (Rat.castHom K) q ≠ 0 from ratFuncRegularAt₂_polynomial _ _
        ((lambertCertificateClearingPolynomial h k).map (Int.castRingHom ℚ)))
    (lambertNormalizedDeterminant_coeff_regular q hq h k i),
    eval_int, lambertNormalizedDeterminant_coeff_specialize_of_pow_injective q hq] at he
  simpa only [coeff_map, coeff_C_mul, coe_eval₂RingHom] using he

end
end Lambert
