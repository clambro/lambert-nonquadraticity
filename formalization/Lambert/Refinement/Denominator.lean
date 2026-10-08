import Lambert.Arithmetic.CyclotomicPoleClearing
import Lambert.Refinement.Normalization

/-! # Integer clearing for the six-presentation Lambert family -/
namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical

/-- The shifted-window clearing polynomial is the zero factor with its exact
exponent times the cyclotomic factors with their proved local exponents. -/
def lambertRefinementClearingPolynomial (N : ℕ) : ℤ[X] :=
  X ^ lambertRefinementClearingZeroExponent N * ∏ n ∈ Ico 1 (543*N), cyclotomic n ℤ ^ lambertRefinementClearingExponent N n

/-- The shifted-window clearing polynomial is monic, including at rank zero. -/
theorem lambertRefinementClearingPolynomial_monic (N : ℕ) :
    (lambertRefinementClearingPolynomial N).Monic := by
  apply Monic.mul (monic_X.pow _)
  exact monic_prod_of_monic _ _ (fun n _ => (cyclotomic.monic n ℤ).pow _)

/-- The reduced denominator of every normalized Lambert coefficient divides the
prescribed zero and cyclotomic clearing polynomial. -/
theorem lambertRefinementDeterminant_denom_dvd (N i : ℕ) :
    ((lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N).coeff i).denom ∣
      (lambertRefinementClearingPolynomial N).map (Int.castRingHom ℚ) := by
  simp only [lambertRefinementClearingPolynomial, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_prod, map_cyclotomic_int]
  exact ratFunc_denom_dvd_cyclotomic_clearing _ _ _ _
    (lambertRefinementNormalizedDeterminant_denominator_support N i) (lambertRefinementNormalizedDeterminant_zero_power_bound N i)
    (fun n e => lambertRefinementNormalizedDeterminant_cyclotomic_power_bound N n i e)
    (fun n _ hN => lambertRefinementClearingExponent_eq_zero N n hN)

/-- Multiplying any normalized Lambert coefficient by the prescribed clearing
polynomial gives an integer polynomial in the formal base. -/
theorem lambertRefinementDeterminant_coeff_cleared (N i : ℕ) :
    ∃ P : ℤ[X], integerPolynomialRatFunc P =
      integerPolynomialRatFunc (lambertRefinementClearingPolynomial N) *
        (lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N).coeff i :=
  monicIntegralRatFunc_clear (lambertRefinementNormalizedDeterminant_coeff_monicIntegral N i)
    _ (lambertRefinementClearingPolynomial_monic N).ne_zero
    (lambertRefinementDeterminant_denom_dvd N i)

end
end Lambert
