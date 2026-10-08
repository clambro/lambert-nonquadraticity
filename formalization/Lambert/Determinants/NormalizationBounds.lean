import Lambert.Determinants.DenominatorSupport
import Lambert.Determinants.ZeroPoleData
import Lambert.Determinants.TranslatedInfinity
import Lambert.Determinants.LocalMap

/-! # Signed normalization for arbitrary translated Lambert windows -/
namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical WithZero

/-- The normalized determinant uses the signed infinity exponent without truncating it. -/
def lambertRectangularNormalizedDeterminant {K : Type*} [Field K] (q : K) (h k d s : ℕ) : K[X] :=
  C (q ^ lambertTranslatedInfinityExponent h k d s) * lambertPoleDeterminant q h k (h+d) s

/-- The normalized coefficient is exactly the signed base power times the original coefficient. -/
private theorem lambertRectangularNormalizedDeterminant_coeff {K : Type*} [Field K]
    (q : K) (h k d s i : ℕ) :
    (lambertRectangularNormalizedDeterminant q h k d s).coeff i =
      q ^ lambertTranslatedInfinityExponent h k d s * (lambertPoleDeterminant q h k (h+d) s).coeff i :=
  coeff_C_mul _

/-- Normalization by the signed infinity exponent bounds every coefficient at infinity. -/
theorem lambertRectangularNormalizedDeterminant_coeff_inftyValuation (h k d s i : ℕ) :
    RatFunc.inftyValuation ℚ ((lambertRectangularNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k d s).coeff i) ≤ 1 := by
  rw [lambertRectangularNormalizedDeterminant_coeff, map_mul, map_zpow₀, RatFunc.inftyValuation.X,
    ← WithZero.exp_zsmul, zsmul_eq_mul, mul_one]
  have he := mul_le_mul' (le_refl (WithZero.exp (lambertTranslatedInfinityExponent h k d s)))
    (lambertPoleDeterminant_coeff_inftyValuation h k d s i)
  simpa only [Nat.add_zero, Int.cast_id, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero] using he

/-- If an unnormalized coefficient has zero-place exponent at most `E`, signed infinity normalization subtracts the infinity exponent from that bound. -/
theorem lambertRectangularNormalizedDeterminant_zero_coeff_valuation (h k d s i : ℕ) (E : ℤ)
    (hb : Valued.v (lambertZeroMap
      ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h+d) s).coeff i)) ≤ WithZero.exp E) :
    Valued.v (lambertZeroMap ((lambertRectangularNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k d s).coeff i)) ≤
      WithZero.exp (E - lambertTranslatedInfinityExponent h k d s) := by
  rw [lambertRectangularNormalizedDeterminant_coeff, map_mul, map_mul, map_zpow₀, lambertZeroMap_X, map_zpow₀]
  have hx : Valued.v (lambertZeroBase ℚ) = WithZero.exp (-1 : ℤ) := by
    simpa only [pow_one, Nat.cast_one] using lambertZeroBase_pow_valuation (K := ℚ) 1
  rw [hx, ← WithZero.exp_zsmul, zsmul_eq_mul, mul_neg_one]
  have he := mul_le_mul' (le_refl (WithZero.exp (-lambertTranslatedInfinityExponent h k d s)))
    hb
  simpa only [Int.cast_id, ← WithZero.exp_add, sub_eq_add_neg, add_comm] using he

/-- Multiplication by an integer base power does not change a nonzero-phase local valuation. -/
theorem lambertRectangularNormalizedDeterminant_coeff_valuation_le {K : Type*} [Field K] [Algebra ℚ K]
    (ζ : K) (h k d s n i : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (E : ℤ)
    (hb : Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h+d) s).coeff i)) ≤ WithZero.exp E) :
    Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      ((lambertRectangularNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k d s).coeff i)) ≤
        WithZero.exp E := by
  rw [lambertRectangularNormalizedDeterminant_coeff, map_mul, map_mul, map_zpow₀, lambertLocalMap_X, map_zpow₀]
  have hx : Valued.v ((lambertLocalBase ζ : PowerSeries K) : LaurentSeries K) = 1 := by
    have ho : (lambertLocalBase ζ).order = 0 := by
      by_contra ho
      have he := PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp ho
      apply hζ.ne_zero hn.ne'
      simpa [lambertLocalBase] using he
    simpa only [Nat.cast_zero, neg_zero, WithZero.exp_zero] using
      laurentSeries_valuation_eq_of_order (lambertLocalBase ζ) 0 ho
  rw [hx, one_zpow, one_mul]
  exact hb

/-- Normalized coefficients still have integer numerators and monic integer denominators. -/
theorem lambertRectangularNormalizedDeterminant_coeff_monicIntegral (h k d s i : ℕ) :
    (lambertRectangularNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k d s).coeff i ∈ monicIntegralRatFunc := by
  rw [lambertRectangularNormalizedDeterminant_coeff]
  apply monicIntegralRatFunc.mul_mem
  · apply subring_zpow_mem_of_inv_mem
    · simpa [integerPolynomialRatFunc] using integerPolynomialRatFunc_mem (X : ℤ[X])
    · simpa [integerPolynomialRatFunc] using integerPolynomialRatFunc_inv_mem (monic_X : (X : ℤ[X]).Monic)
  · exact lambertPoleDeterminant_coeff_monicIntegral h k d s i

/-- Signed normalization introduces no denominator factors other than the base variable. -/
theorem lambertRectangularNormalizedDeterminant_denominator_support (h k d s i : ℕ) :
    (lambertRectangularNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k d s).coeff i ∈
      ratFuncPoleSupport IsLambertPoleFactor := by
  rw [lambertRectangularNormalizedDeterminant_coeff]
  apply (ratFuncPoleSupport IsLambertPoleFactor).mul_mem
  · apply subring_zpow_mem_of_inv_mem
    · exact ratFuncPoleSupport_polynomial _ X
    · change ((algebraMap ℚ[X] (RatFunc ℚ)) X)⁻¹ ∈ _
      exact ratFuncPoleSupport_inverse IsLambertPoleFactor (X : ℚ[X])
        (fun p hp hd => Or.inl (hp.associated_of_dvd irreducible_X hd))
  · exact lambertPoleDeterminant_denominator_support h k d s i

end
end Lambert
