import Lambert.Refinement.Denominator
import Lambert.Arithmetic.IntegerCertificate

/-! # Integer certificates for the six-presentation Lambert family -/
namespace Lambert
noncomputable section
open Polynomial
open scoped Classical

/-- The integer numerator of the `i`th normalized shifted Lambert coefficient after clearing
its zero and cyclotomic poles by the prescribed polynomial. -/
def lambertRefinementClearedCoefficient (N i : ℕ) : ℤ[X] :=
  clearedIntegerCoefficient (lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N)
    (lambertRefinementClearingPolynomial N)
    (lambertRefinementDeterminant_coeff_cleared N) i

/-- Each cleared coefficient has base degree at most that of the clearing polynomial. -/
theorem lambertRefinementClearedCoefficient_natDegree_le (N i : ℕ) :
    (lambertRefinementClearedCoefficient N i).natDegree ≤
      (lambertRefinementClearingPolynomial N).natDegree :=
  clearedIntegerCoefficient_natDegree_le (lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N)
    (lambertRefinementClearingPolynomial N)
    (lambertRefinementDeterminant_coeff_cleared N)
    (lambertRefinementClearingPolynomial_monic N).ne_zero i (lambertRefinementNormalizedDeterminant_coeff_inftyValuation N i)

/-- The rational-base normalized shifted Lambert integer polynomial homogenizes each cleared
coefficient to the common degree of the prescribed clearing polynomial. -/
def lambertRefinementSpecializedIntegerPolynomial (N : ℕ) (a b : ℤ) : ℤ[X] :=
  clearedSpecializedIntegerPolynomial (lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N)
    (lambertRefinementClearingPolynomial N)
    (lambertRefinementDeterminant_coeff_cleared N) (500*N) a b

/-- The rational-base integer polynomial retains degree at most the matrix rank. -/
theorem lambertRefinementSpecializedIntegerPolynomial_natDegree_le (N : ℕ) (a b : ℤ) :
    (lambertRefinementSpecializedIntegerPolynomial N a b).natDegree ≤ 500*N :=
  clearedSpecializedIntegerPolynomial_natDegree_le (lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N)
    (lambertRefinementClearingPolynomial N)
    (lambertRefinementDeterminant_coeff_cleared N) (500*N) a b


end
end Lambert
