import Lambert.Determinants.NormalizationBounds
import Lambert.Refinement.Orbit
import Lambert.Refinement.ZeroPole
import Lambert.Refinement.Infinity

/-! # Signed normalization of the six-presentation Lambert family -/
namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical WithZero

/-- The normalized determinant uses the signed infinity exponent without truncating it. -/
def lambertRefinementNormalizedDeterminant {K : Type*} [Field K] (q : K) (N : ℕ) : K[X] :=
  C (q ^ lambertTranslatedInfinityExponent (500*N) (27*N) (16*N) (41*N)) * lambertPoleDeterminant q (500*N) (27*N) (516*N) (41*N)

/-- Signed normalization preserves the degree bound in the unknown Lambert value. -/
theorem lambertRefinementNormalizedDeterminant_natDegree_le {K : Type*} [Field K]
    (q : K) (N : ℕ) : (lambertRefinementNormalizedDeterminant q N).natDegree ≤ 500*N :=
  (natDegree_C_mul_le _ _).trans (lambertPoleDeterminant_natDegree_le q (500*N) (27*N) (516*N) (41*N))

/-- The normalized coefficient is exactly the signed base power times the original coefficient. -/
theorem lambertRefinementNormalizedDeterminant_coeff {K : Type*} [Field K]
    (q : K) (N i : ℕ) :
    (lambertRefinementNormalizedDeterminant q N).coeff i =
      q ^ lambertTranslatedInfinityExponent (500*N) (27*N) (16*N) (41*N) * (lambertPoleDeterminant q (500*N) (27*N) (516*N) (41*N)).coeff i :=
  coeff_C_mul _

/-- Normalization by the signed infinity exponent bounds every coefficient at infinity. -/
theorem lambertRefinementNormalizedDeterminant_coeff_inftyValuation (N i : ℕ) :
    RatFunc.inftyValuation ℚ ((lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N).coeff i) ≤ 1 := by
  simpa only [lambertRefinementNormalizedDeterminant, lambertRectangularNormalizedDeterminant, show 500*N+16*N=516*N by omega] using
    lambertRectangularNormalizedDeterminant_coeff_inftyValuation (500*N) (27*N) (16*N) (41*N) i

/-- Every normalized coefficient satisfies the signed zero-place bound A-B. -/
theorem lambertRefinementNormalizedDeterminant_zero_coeff_valuation (N i : ℕ) :
    Valued.v (lambertZeroMap ((lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N).coeff i)) ≤
      WithZero.exp ((lambertRefinementZeroExponent N : ℤ) - lambertTranslatedInfinityExponent (500*N) (27*N) (16*N) (41*N)) := by
  simpa only [lambertRefinementNormalizedDeterminant, lambertRectangularNormalizedDeterminant, show 500*N+16*N=516*N by omega] using
    lambertRectangularNormalizedDeterminant_zero_coeff_valuation (500*N) (27*N) (16*N) (41*N) i (lambertRefinementZeroExponent N : ℤ)
      (by simpa only [show 500*N+16*N=516*N by omega] using lambertRefinementFamily_zero_coeff_valuation N i)

/-- Multiplication by an integer base power does not change a nonzero-phase local valuation. -/
theorem lambertRefinementNormalizedDeterminant_coeff_valuation_le {K : Type*} [Field K] [Algebra ℚ K]
    (ζ : K) (N n i : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      ((lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N).coeff i)) ≤
        WithZero.exp (lambertRefinementClearingExponent N n : ℤ) := by
  simpa only [lambertRefinementNormalizedDeterminant, lambertRectangularNormalizedDeterminant, show 500*N+16*N=516*N by omega] using
    lambertRectangularNormalizedDeterminant_coeff_valuation_le ζ (500*N) (27*N) (16*N) (41*N) n i hn hζ (lambertRefinementClearingExponent N n : ℤ)
      (by simpa only [show 500*N+16*N=516*N by omega] using lambertRefinementFamily_coeff_valuation_le ζ N n i hn hζ)

/-- Normalized coefficients still have integer numerators and monic integer denominators. -/
theorem lambertRefinementNormalizedDeterminant_coeff_monicIntegral (N i : ℕ) :
    (lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N).coeff i ∈ monicIntegralRatFunc := by
  simpa only [lambertRefinementNormalizedDeterminant, lambertRectangularNormalizedDeterminant, show 500*N+16*N=516*N by omega] using
    lambertRectangularNormalizedDeterminant_coeff_monicIntegral (500*N) (27*N) (16*N) (41*N) i

/-- Signed normalization introduces no denominator factors other than the base variable. -/
theorem lambertRefinementNormalizedDeterminant_denominator_support (N i : ℕ) :
    (lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N).coeff i ∈
      ratFuncPoleSupport IsLambertPoleFactor := by
  simpa only [lambertRefinementNormalizedDeterminant, lambertRectangularNormalizedDeterminant, show 500*N+16*N=516*N by omega] using
    lambertRectangularNormalizedDeterminant_denominator_support (500*N) (27*N) (16*N) (41*N) i

/-- The natural clearing exponent retains the signed A-B value before any nonnegative conversion. -/
def lambertRefinementClearingZeroExponent (N : ℕ) : ℕ :=
  ((lambertRefinementZeroExponent N : ℤ) - lambertTranslatedInfinityExponent (500*N) (27*N) (16*N) (41*N)).toNat

/-- Every power of the base variable in a normalized coefficient denominator is bounded by the clearing exponent. -/
theorem lambertRefinementNormalizedDeterminant_zero_power_bound (N i e : ℕ)
    (he : (X : ℚ[X]) ^ e ∣ ((lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N).coeff i).denom) :
    e ≤ lambertRefinementClearingZeroExponent N := by
  exact lambertZeroMap_denominator_power_bound _ _
    (lambertRefinementNormalizedDeterminant_zero_coeff_valuation N i) e he

/-- Every cyclotomic multiplicity in a normalized coefficient denominator satisfies the shifted bound. -/
theorem lambertRefinementNormalizedDeterminant_cyclotomic_power_bound (N n i e : ℕ) (hn : 0 < n)
    (he : cyclotomic n ℚ ^ e ∣ ((lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N).coeff i).denom) :
    e ≤ lambertRefinementClearingExponent N n := by
  exact lambertLocalMap_denominator_power_bound _ n _ hn
    (fun ζ hζ => lambertRefinementNormalizedDeterminant_coeff_valuation_le ζ N n i hn hζ) e he

end
end Lambert
