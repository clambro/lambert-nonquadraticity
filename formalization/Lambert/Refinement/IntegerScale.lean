import Lambert.Refinement.IntegerPolynomial
import Lambert.Refinement.Specialization
import Lambert.Arithmetic.HomogeneousCyclotomic

/-!
# The exact integer scale at a rational base

Homogenization converts the polynomial clearing factor to the claimed product
of powers of the numerator and homogeneous cyclotomic values, with no extra scale.
-/
namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical

/-- The translated-window integer scale is the numerator's zero-pole power times
the homogeneous cyclotomic factors with their local pole exponents. -/
def lambertRefinementIntegerScale (N : ℕ) (a b : ℤ) : ℤ :=
  a ^ lambertRefinementClearingZeroExponent N * ∏ n ∈ Ico 1 (543*N),
    homogeneousCyclotomicValue n a b ^ lambertRefinementClearingExponent N n

/-- Homogenizing the shifted-window clearing polynomial gives exactly its prescribed
integer scale, without an additional power of the second coordinate. -/
theorem lambertRefinementIntegerScale_eq_homogeneous (N : ℕ) (a b : ℤ) :
    lambertRefinementIntegerScale N a b =
      integerPolynomialHomogeneousEvaluation a b (lambertRefinementClearingPolynomial N) := by
  simp only [lambertRefinementClearingPolynomial, map_mul, map_pow, map_prod,
    integerPolynomialHomogeneousEvaluation_X, lambertRefinementIntegerScale]
  congr 1
  apply prod_congr rfl
  intro n hn
  congr 1
  simp only [integerPolynomialHomogeneousEvaluation, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, homogeneousCyclotomicValue, homogeneousCyclotomic, natDegree_cyclotomic]

/-- The integer scale equals the clearing polynomial evaluated at `a/b` times
exactly the common homogenizing power of `b`. -/
theorem lambertRefinementIntegerScale_rat (N : ℕ) (a b : ℤ) (hb : b ≠ 0) :
    (lambertRefinementIntegerScale N a b : ℚ) =
      ((lambertRefinementClearingPolynomial N).map (Int.castRingHom ℚ)).eval ((a : ℚ) / b) *
        (b : ℚ) ^ (lambertRefinementClearingPolynomial N).natDegree := by
  rw [lambertRefinementIntegerScale_eq_homogeneous]
  exact integerPolynomial_homogeneous_eval _ _ le_rfl a b hb

/-- The shifted-window clearing polynomial is positive at every rational base greater than one. -/
theorem lambertRefinementClearingPolynomial_eval_pos (N : ℕ) (q : ℚ) (hq : 1 < q) :
    0 < ((lambertRefinementClearingPolynomial N).map (Int.castRingHom ℚ)).eval q := by
  simp only [lambertRefinementClearingPolynomial, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_prod, map_cyclotomic_int, eval_mul, eval_pow,
    eval_X, eval_prod]
  apply mul_pos (pow_pos (lt_trans zero_lt_one hq) _)
  exact prod_pos (fun n _ => pow_pos (cyclotomic_pos' n hq) _)

/-- At a rational base greater than one, the constructed integer polynomial is
exactly the prescribed integer scale times the shifted-window Lambert determinant. -/
theorem lambertRefinementSpecializedIntegerPolynomial_map (N : ℕ) (a b : ℤ) (hb : b ≠ 0)
    (hq : (1 : ℚ) < (a : ℚ) / b) :
    (lambertRefinementSpecializedIntegerPolynomial N a b).map (Int.castRingHom ℚ) =
      C (lambertRefinementIntegerScale N a b : ℚ) *
        lambertRefinementNormalizedDeterminant ((a : ℚ) / b) N := by
  rw [lambertRefinementIntegerScale_rat N a b hb]
  exact clearedSpecializedIntegerPolynomial_map _ _ _ (500*N)
    (lambertRefinementNormalizedDeterminant_natDegree_le (RatFunc.X : RatFunc ℚ) N) (lambertRefinementClearedCoefficient_natDegree_le N)
    (lambertRefinementDeterminant_denom_dvd N) a b hb
    (lambertRefinementClearingPolynomial_eval_pos N _ hq).ne' _
    (lambertRefinementNormalizedDeterminant_coeff_specialize _ hq N)

end
end Lambert
