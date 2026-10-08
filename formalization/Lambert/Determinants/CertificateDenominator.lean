import Lambert.Arithmetic.CyclotomicPoleClearing
import Lambert.Determinants.Normalization

/-!
# Integer clearing of normalized shifted Lambert determinants

The signed normalization is applied before denominator clearing. Monic integer
descent supplies integrality, and the root-order cutoff is explicit.
-/
namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical

/-- The shifted-window clearing polynomial is the zero factor with its exact
exponent times the cyclotomic factors with their proved local exponents. -/
def lambertCertificateClearingPolynomial (h k : ℕ) : ℤ[X] :=
  X ^ lambertCertificateClearingZeroExponent h k * ∏ n ∈ Ico 1 ((h+k)), cyclotomic n ℤ ^ lambertTranslatedCyclotomicExponent h k n

/-- The shifted-window clearing polynomial is monic, including at rank zero. -/
theorem lambertCertificateClearingPolynomial_monic (h k : ℕ) :
    (lambertCertificateClearingPolynomial h k).Monic := by
  apply Monic.mul (monic_X.pow _)
  exact monic_prod_of_monic _ _ (fun n _ => (cyclotomic.monic n ℤ).pow _)

/-- The reduced denominator of every normalized Lambert coefficient divides the
prescribed zero and cyclotomic clearing polynomial. -/
theorem lambertCertificateDeterminant_denom_dvd (h k i : ℕ) :
    ((lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k).coeff i).denom ∣
      (lambertCertificateClearingPolynomial h k).map (Int.castRingHom ℚ) := by
  simp only [lambertCertificateClearingPolynomial, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_prod, map_cyclotomic_int]
  exact ratFunc_denom_dvd_cyclotomic_clearing _ _ _ _
    (lambertNormalizedDeterminant_denominator_support h k i) (lambertNormalizedDeterminant_zero_power_bound h k i)
    (fun n e => lambertNormalizedDeterminant_cyclotomic_power_bound h k n i e)
    (fun n hn hN => lambertTranslatedCyclotomicExponent_eq_zero h k n hn hN)

/-- Multiplying any normalized Lambert coefficient by the prescribed clearing
polynomial gives an integer polynomial in the formal base. -/
theorem lambertCertificateDeterminant_coeff_cleared (h k i : ℕ) :
    ∃ N : ℤ[X], integerPolynomialRatFunc N =
      integerPolynomialRatFunc (lambertCertificateClearingPolynomial h k) *
        (lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k).coeff i :=
  monicIntegralRatFunc_clear (lambertNormalizedDeterminant_coeff_monicIntegral h k i)
    _ (lambertCertificateClearingPolynomial_monic h k).ne_zero
    (lambertCertificateDeterminant_denom_dvd h k i)

end
end Lambert
