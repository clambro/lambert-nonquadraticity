import Lambert.Determinants.NormalizationBounds
import Lambert.Determinants.CyclotomicBounds
import Lambert.Determinants.ZeroPole

/-!
# Signed normalization of shifted Lambert determinants

Multiplication by the signed infinity power makes every coefficient bounded
at infinity and changes its zero-place exponent from A to A-B.
-/
namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical WithZero

/-- The normalized determinant uses the signed infinity exponent without truncating it. -/
def lambertNormalizedDeterminant {K : Type*} [Field K] (q : K) (h k : ℕ) : K[X] :=
  C (q ^ lambertTranslatedInfinityExponent h k 0 k) * lambertPoleDeterminant q h k h k

/-- Signed normalization preserves the degree bound in the unknown Lambert value. -/
theorem lambertNormalizedDeterminant_natDegree_le {K : Type*} [Field K]
    (q : K) (h k : ℕ) : (lambertNormalizedDeterminant q h k).natDegree ≤ h :=
  (natDegree_C_mul_le _ _).trans (lambertPoleDeterminant_natDegree_le q h k h k)

/-- The normalized coefficient is exactly the signed base power times the original coefficient. -/
theorem lambertNormalizedDeterminant_coeff {K : Type*} [Field K]
    (q : K) (h k i : ℕ) :
    (lambertNormalizedDeterminant q h k).coeff i =
      q ^ lambertTranslatedInfinityExponent h k 0 k * (lambertPoleDeterminant q h k h k).coeff i :=
  coeff_C_mul _

/-- Normalization by the signed infinity exponent bounds every coefficient at infinity. -/
theorem lambertNormalizedDeterminant_coeff_inftyValuation (h k i : ℕ) :
    RatFunc.inftyValuation ℚ ((lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k).coeff i) ≤ 1 := by
  simpa only [lambertNormalizedDeterminant, lambertRectangularNormalizedDeterminant, Nat.add_zero] using
    lambertRectangularNormalizedDeterminant_coeff_inftyValuation h k 0 k i

/-- Every normalized coefficient satisfies the signed zero-place bound A-B. -/
theorem lambertNormalizedDeterminant_zero_coeff_valuation (h k i : ℕ) :
    Valued.v (lambertZeroMap ((lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k).coeff i)) ≤
      WithZero.exp (lambertZeroExponent h k - lambertTranslatedInfinityExponent h k 0 k) := by
  simpa only [lambertNormalizedDeterminant, lambertRectangularNormalizedDeterminant, Nat.add_zero] using
    lambertRectangularNormalizedDeterminant_zero_coeff_valuation h k 0 k i (lambertZeroExponent h k)
      (by simpa only [Nat.add_zero] using lambertPoleDeterminant_zero_coeff_valuation h k i)

/-- Multiplication by an integer base power does not change a nonzero-phase local valuation. -/
theorem lambertNormalizedDeterminant_coeff_valuation_le {K : Type*} [Field K] [Algebra ℚ K]
    (ζ : K) (h k n i : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      ((lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k).coeff i)) ≤
        WithZero.exp (lambertTranslatedCyclotomicExponent h k n : ℤ) := by
  simpa only [lambertNormalizedDeterminant, lambertRectangularNormalizedDeterminant, Nat.add_zero] using
    lambertRectangularNormalizedDeterminant_coeff_valuation_le ζ h k 0 k n i hn hζ (lambertTranslatedCyclotomicExponent h k n : ℤ)
      (by simpa only [Nat.add_zero] using lambertPoleDeterminant_coeff_valuation_le ζ h k n i hn hζ)

/-- Normalized coefficients still have integer numerators and monic integer denominators. -/
theorem lambertNormalizedDeterminant_coeff_monicIntegral (h k i : ℕ) :
    (lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k).coeff i ∈ monicIntegralRatFunc := by
  simpa only [lambertNormalizedDeterminant, lambertRectangularNormalizedDeterminant, Nat.add_zero] using
    lambertRectangularNormalizedDeterminant_coeff_monicIntegral h k 0 k i

/-- Signed normalization introduces no denominator factors other than the base variable. -/
theorem lambertNormalizedDeterminant_denominator_support (h k i : ℕ) :
    (lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k).coeff i ∈
      ratFuncPoleSupport IsLambertPoleFactor := by
  simpa only [lambertNormalizedDeterminant, lambertRectangularNormalizedDeterminant, Nat.add_zero] using
    lambertRectangularNormalizedDeterminant_denominator_support h k 0 k i

/-- The natural clearing exponent retains the signed A-B value before any nonnegative conversion. -/
def lambertCertificateClearingZeroExponent (h k : ℕ) : ℕ :=
  (lambertZeroExponent h k - lambertTranslatedInfinityExponent h k 0 k).toNat

/-- Every power of the base variable in a normalized coefficient denominator is bounded by the clearing exponent. -/
theorem lambertNormalizedDeterminant_zero_power_bound (h k i e : ℕ)
    (he : (X : ℚ[X]) ^ e ∣ ((lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k).coeff i).denom) :
    e ≤ lambertCertificateClearingZeroExponent h k := by
  exact lambertZeroMap_denominator_power_bound _ _
    (lambertNormalizedDeterminant_zero_coeff_valuation h k i) e he

/-- Every cyclotomic multiplicity in a normalized coefficient denominator satisfies the shifted bound. -/
theorem lambertNormalizedDeterminant_cyclotomic_power_bound (h k n i e : ℕ) (hn : 0 < n)
    (he : cyclotomic n ℚ ^ e ∣ ((lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k).coeff i).denom) :
    e ≤ lambertTranslatedCyclotomicExponent h k n := by
  exact lambertLocalMap_denominator_power_bound _ n _ hn
    (fun ζ hζ => lambertNormalizedDeterminant_coeff_valuation_le ζ h k n i hn hζ) e he

end
end Lambert
