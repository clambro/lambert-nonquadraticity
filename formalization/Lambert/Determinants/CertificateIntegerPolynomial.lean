import Lambert.Determinants.CertificateDenominator
import Lambert.Arithmetic.IntegerCertificate

/-!
# The integer polynomial underlying the normalized shifted Lambert construction

The local pole exponents clear all coefficients over the integers. Boundedness
at infinity gives the exact degree needed for homogeneous rational specialization.
-/
namespace Lambert
noncomputable section
open Polynomial
open scoped Classical

/-- The integer numerator of the `i`th normalized shifted Lambert coefficient after clearing
its zero and cyclotomic poles by the prescribed polynomial. -/
def lambertCertificateClearedCoefficient (h k i : ℕ) : ℤ[X] :=
  clearedIntegerCoefficient (lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k)
    (lambertCertificateClearingPolynomial h k)
    (lambertCertificateDeterminant_coeff_cleared h k) i

/-- Each cleared coefficient has base degree at most that of the clearing polynomial. -/
theorem lambertCertificateClearedCoefficient_natDegree_le (h k i : ℕ) :
    (lambertCertificateClearedCoefficient h k i).natDegree ≤
      (lambertCertificateClearingPolynomial h k).natDegree :=
  clearedIntegerCoefficient_natDegree_le (lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k)
    (lambertCertificateClearingPolynomial h k)
    (lambertCertificateDeterminant_coeff_cleared h k)
    (lambertCertificateClearingPolynomial_monic h k).ne_zero i (lambertNormalizedDeterminant_coeff_inftyValuation h k i)

/-- The normalized shifted Lambert integer polynomial has the unknown Lambert value as its
outer variable and the formal base as its inner variable. -/
def lambertCertificateIntegerPolynomial (h k : ℕ) : (ℤ[X])[X] :=
  clearedIntegerPolynomial (lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k)
    (lambertCertificateClearingPolynomial h k)
    (lambertCertificateDeterminant_coeff_cleared h k) h

/-- The normalized shifted Lambert integer polynomial has degree at most its matrix rank
in the unknown Lambert value. -/
theorem lambertCertificateIntegerPolynomial_natDegree_le (h k : ℕ) :
    (lambertCertificateIntegerPolynomial h k).natDegree ≤ h :=
  clearedIntegerPolynomial_natDegree_le (lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k)
    (lambertCertificateClearingPolynomial h k)
    (lambertCertificateDeterminant_coeff_cleared h k) h

/-- Every coefficient of the integer certificate has base degree at most the clearing degree. -/
theorem lambertCertificateIntegerPolynomial_coeff_natDegree_le (h k i : ℕ) :
    ((lambertCertificateIntegerPolynomial h k).coeff i).natDegree ≤
      (lambertCertificateClearingPolynomial h k).natDegree := by
  by_cases hi : i < h+1
  · rw [lambertCertificateIntegerPolynomial, clearedIntegerPolynomial, ofFn_coeff_eq_val_of_lt _ hi]
    exact lambertCertificateClearedCoefficient_natDegree_le h k i
  · rw [lambertCertificateIntegerPolynomial, clearedIntegerPolynomial, ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi),
      natDegree_zero]
    exact Nat.zero_le _

/-- Embedding the integer polynomial recovers precisely the cleared original
Lambert determinant, rather than a different polynomial with the same pole bounds. -/
theorem lambertCertificateIntegerPolynomial_map (h k : ℕ) :
    (lambertCertificateIntegerPolynomial h k).map integerPolynomialRatFunc =
      C (integerPolynomialRatFunc (lambertCertificateClearingPolynomial h k)) *
        lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k :=
  clearedIntegerPolynomial_map (lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k)
    (lambertCertificateClearingPolynomial h k)
    (lambertCertificateDeterminant_coeff_cleared h k) h
    (lambertNormalizedDeterminant_natDegree_le _ h k)

end
end Lambert
