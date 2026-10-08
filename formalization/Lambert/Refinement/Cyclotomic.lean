import Lambert.Determinants.BorderedResidue
import Lambert.Determinants.BorderedLocalIdentity
import Lambert.Determinants.Local

/-! # Coefficientwise cyclotomic bounds with numerator zeros -/
namespace Lambert
noncomputable section
open Finset PowerSeries Matrix
open scoped Classical WithZero

/-- The bordered local order is the larger of the harmonic-periodic filtration bound and the corrected residue corank. -/
def lambertRefinementLocalOrder (h A b d s n : ℕ) : ℕ :=
  max (∑ r ∈ range (h + d + A), (h + d + A - 2 * n * (r + 1)))
    (h - lambertRectangularResidualCount (h + A) d s n - (b + (h + d) - max b n))

/-- The signed coefficient pole bound accounts for rank regularization and both Vandermondes before subtracting the bordered local order. -/
def lambertRefinementCyclotomicExponent (h A b d s n : ℕ) : ℤ :=
  (h : ℤ) + (∑ r ∈ range (h + d), (h + d - (r + 1) * n) : ℕ) +
    (∑ r ∈ range A, (A - (r + 1) * n) : ℕ) - lambertRefinementLocalOrder h A b d s n

/-- The bordered local determinant attains the larger of its two proven order bounds. -/
theorem lambertBorderedLocalMatrix_order_ge {K : Type*} [Field K] [Algebra ℚ K]
    (ζ x : K) (h A b d s n : ℕ) (hAb : A ≤ b) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    (lambertRefinementLocalOrder h A b d s n : ℕ∞) ≤
      (lambertBorderedLocalMatrix ζ x h A b d s).det.order := by
  change max (↑(∑ r ∈ range (h + d + A), (h + d + A - 2 * n * (r + 1))) : ℕ∞)
    (↑(h - lambertRectangularResidualCount (h + A) d s n - (b + (h + d) - max b n))) ≤ _
  exact max_le (lambertBorderedLocalMatrix_order_ge_filtration ζ x h A b d s n
    (h + d + A) hAb hn hζ) (lambertBorderedLocalMatrix_order_ge_residue ζ x h A b d s n hζ)

/-- Every constant evaluation of a numerator-weighted determinant satisfies the signed cyclotomic bound. -/
theorem lambertRefinementDeterminant_eval_valuation_le {K : Type*} [Field K] [Algebra ℚ K]
    (ζ : K) (h A b d s n : ℕ) (hAb : A ≤ b) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (x : K) :
    Valued.v (((lambertRefinementDeterminant (RatFunc.X : RatFunc ℚ) h A b (h + d) s).map
      (lambertLocalMap ζ (hζ.ne_zero hn.ne'))).eval (algebraMap K (LaurentSeries K) x)) ≤
        WithZero.exp (lambertRefinementCyclotomicExponent h A b d s n) := by
  let f := HahnSeries.ofPowerSeries ℤ K
  let V := ∑ r ∈ range (h + d), (h + d - (r + 1) * n)
  let W := ∑ r ∈ range A, (A - (r + 1) * n)
  let D := lambertRefinementLocalOrder h A b d s n
  let E := lambertRefinementCyclotomicExponent h A b d s n
  have hB := laurentSeries_valuation_le_of_order (lambertBorderedLocalMatrix ζ x h A b d s).det D
    (lambertBorderedLocalMatrix_order_ge ζ x h A b d s n hAb hn hζ)
  rw [lambertBorderedLocalMatrix_identity ζ x (hζ.ne_zero hn.ne')] at hB
  have hv : Valued.v (f (vandermonde (fun j : Fin (h + d) => lambertLocalBase ζ ^ (b + j.val))).det) =
      WithZero.exp (-(V : ℤ)) :=
    laurentSeries_valuation_eq_of_order _ V (lambertTranslatedLocalVandermonde_order ζ (h + d) b n hn hζ)
  have hw : Valued.v (f (vandermonde (fun j : Fin A => lambertLocalBase ζ ^ j.val)).det) =
      WithZero.exp (-(W : ℤ)) :=
    laurentSeries_valuation_eq_of_order _ W (lambertLocalVandermonde_order_deficits ζ A n hn hζ)
  have hx : Valued.v (f (PowerSeries.X : PowerSeries K) ^ h) = WithZero.exp (-(h : ℤ)) := by
    simpa only [map_pow] using
      laurentSeries_valuation_eq_of_order ((PowerSeries.X : PowerSeries K) ^ h) h (order_X_pow h)
  have hs : Valued.v (lambertBorderedLocalSign h A d : LaurentSeries K) = 1 := by
    rcases sq_eq_one_iff.mp (lambertBorderedLocalSign_sq h A d) with hs | hs <;> simp [hs]
  have hb : Valued.v (f (lambertLocalBase ζ)) = 1 := by
    have ho : (lambertLocalBase ζ).order = 0 := by
      by_contra ho
      have he := PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp ho
      apply hζ.ne_zero hn.ne'
      simpa [lambertLocalBase] using he
    simpa only [Nat.cast_zero, neg_zero, WithZero.exp_zero] using
      laurentSeries_valuation_eq_of_order (lambertLocalBase ζ) 0 ho
  have hp : Valued.v (∏ i : Fin A, f (lambertLocalBase ζ) ^ (s * i.val)) = 1 := by
    simp only [map_prod, map_pow, hb, one_pow, prod_const_one]
  change Valued.v (f (PowerSeries.X : PowerSeries K) ^ h *
    (∏ i : Fin A, f (lambertLocalBase ζ) ^ (s * i.val)) *
    (lambertBorderedLocalSign h A d : LaurentSeries K) *
    f (vandermonde (fun j : Fin (h + d) => lambertLocalBase ζ ^ (b + j.val))).det *
    f (vandermonde (fun j : Fin A => lambertLocalBase ζ ^ j.val)).det * _) ≤ _ at hB
  simp only [map_mul, hx, hp, hs, hv, hw, mul_one] at hB
  have he : WithZero.exp (-(D : ℤ)) =
      WithZero.exp (-(h : ℤ)) * WithZero.exp (-(V : ℤ)) * WithZero.exp (-(W : ℤ)) * WithZero.exp E := by
    rw [← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add]
    congr 1
    dsimp [E, lambertRefinementCyclotomicExponent, V, W, D]
    ring
  rw [he] at hB
  exact le_of_mul_le_mul_left hB (mul_pos (mul_pos WithZero.exp_pos WithZero.exp_pos) WithZero.exp_pos)

/-- Constant interpolation gives the same cyclotomic bound for every coefficient of the numerator-weighted determinant. -/
theorem lambertRefinementDeterminant_coeff_valuation_le {K : Type*} [Field K] [Algebra ℚ K]
    (ζ : K) (h A b d s n i : ℕ) (hAb : A ≤ b) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      ((lambertRefinementDeterminant (RatFunc.X : RatFunc ℚ) h A b (h + d) s).coeff i)) ≤
        WithZero.exp (lambertRefinementCyclotomicExponent h A b d s n) := by
  let : Infinite K := Infinite.of_injective _ (algebraMap ℚ K).injective
  have he := laurentSeries_coeff_valuation_le_of_eval
    ((lambertRefinementDeterminant (RatFunc.X : RatFunc ℚ) h A b (h + d) s).map
      (lambertLocalMap ζ (hζ.ne_zero hn.ne'))) (-(lambertRefinementCyclotomicExponent h A b d s n))
    (fun x => by simpa only [neg_neg] using
      lambertRefinementDeterminant_eval_valuation_le ζ h A b d s n hAb hn hζ x) i
  simpa only [Polynomial.coeff_map, neg_neg] using he

end
end Lambert
