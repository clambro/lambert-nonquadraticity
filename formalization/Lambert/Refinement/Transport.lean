import Lambert.Refinement.Cyclotomic
import Lambert.Refinement.Transpose
import Lambert.Refinement.Symmetry

/-! # Transporting coefficient pole bounds between numerator presentations -/
namespace Lambert
noncomputable section
open Finset PowerSeries Matrix
open scoped Classical WithZero
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The cyclotomic order of the transpose multiplier is the difference of the two pairs of Vandermonde collision counts. -/
def lambertRefinementTransportOrder (h A d n : ℕ) : ℤ :=
  (∑ r ∈ range (h + A), (h + A - (r + 1) * n) : ℕ) +
    (∑ r ∈ range d, (d - (r + 1) * n) : ℕ) -
    (∑ r ∈ range (h + d), (h + d - (r + 1) * n) : ℕ) -
    (∑ r ∈ range A, (A - (r + 1) * n) : ℕ)

private theorem base_valuation (ζ : K) (hz : ζ ≠ 0) :
    Valued.v (lambertLocalMap ζ hz (RatFunc.X : RatFunc ℚ)) = 1 := by
  rw [lambertLocalMap_X]
  have ho : (lambertLocalBase ζ).order = 0 := by
    by_contra ho
    have he := PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp ho
    apply hz
    simpa [lambertLocalBase] using he
  simpa only [Nat.cast_zero, neg_zero, WithZero.exp_zero] using
    laurentSeries_valuation_eq_of_order (lambertLocalBase ζ) 0 ho

private theorem vandermonde_valuation (ζ : K) (L k n : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      (vandermonde (fun j : Fin L => (RatFunc.X : RatFunc ℚ) ^ (k + j.val))).det) =
        WithZero.exp (-((∑ r ∈ range L, (L - (r + 1) * n) : ℕ) : ℤ)) := by
  let g := lambertLocalMap ζ (hζ.ne_zero hn.ne')
  let f := HahnSeries.ofPowerSeries ℤ K
  have he : g (vandermonde (fun j : Fin L => (RatFunc.X : RatFunc ℚ) ^ (k + j.val))).det =
      f (vandermonde (fun j : Fin L => lambertLocalBase ζ ^ (k + j.val))).det := by
    rw [g.map_det, f.map_det]
    congr 1
    ext i j
    simp [g, f, vandermonde_apply, lambertLocalMap_X]
  rw [he]
  exact laurentSeries_valuation_eq_of_order _ _ (lambertTranslatedLocalVandermonde_order ζ L k n hn hζ)

private theorem sign_valuation (ζ : K) (hz : ζ ≠ 0) (t : ℤ) (ht : t ^ 2 = 1) :
    Valued.v (lambertLocalMap ζ hz (t : RatFunc ℚ)) = 1 := by
  rcases sq_eq_one_iff.mp ht with he | he <;> simp [he]

/-- A coefficientwise bound on the transposed presentation transports back with exactly the Vandermonde-order correction. -/
theorem lambertRefinementDeterminant_coeff_valuation_le_of_transpose
    (ζ : K) (h A b d s n i : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (E : ℤ)
    (hE : Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      ((lambertRefinementDeterminant (RatFunc.X : RatFunc ℚ) h d s (h + A) b).coeff i)) ≤
        WithZero.exp E) :
    Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      ((lambertRefinementDeterminant (RatFunc.X : RatFunc ℚ) h A b (h + d) s).coeff i)) ≤
        WithZero.exp (E - lambertRefinementTransportOrder h A d n) := by
  let g := lambertLocalMap ζ (hζ.ne_zero hn.ne')
  let V (L : ℕ) : ℤ := (∑ r ∈ range L, (L - (r + 1) * n) : ℕ)
  have he := congrArg (fun p : Polynomial (RatFunc ℚ) => Valued.v (g (p.coeff i)))
    (lambertRefinementDeterminant_transpose (RatFunc.X : RatFunc ℚ) h A b d s ratFunc_X_pow_injective)
  simp only [Polynomial.coeff_C_mul] at he
  simp only [map_mul] at he
  have hp (L k : ℕ) : Valued.v (g (∏ j : Fin L, (RatFunc.X : RatFunc ℚ) ^ (k * j.val))) = 1 := by
    simp only [map_prod, map_pow, g, base_valuation, one_pow, prod_const_one]
  have hv (L k : ℕ) := vandermonde_valuation ζ L k n hn hζ
  have hv0 (L : ℕ) : Valued.v (g (vandermonde (fun j : Fin L => (RatFunc.X : RatFunc ℚ) ^ j.val)).det) =
      WithZero.exp (-(V L)) := by simpa only [Nat.zero_add] using hv L 0
  have hs := sign_valuation ζ (hζ.ne_zero hn.ne') _ (lambertRefinementTransposeSign_sq h A d)
  have hs₁ := sign_valuation ζ (hζ.ne_zero hn.ne') _ (lambertRefinementBorderedSign_sq h A d)
  have hs₂ := sign_valuation ζ (hζ.ne_zero hn.ne') _ (lambertRefinementBorderedSign_sq h d A)
  rw [hp, hp, hs, hs₁, hs₂, hv, hv, hv0, hv0] at he
  simp only [one_mul] at he
  have hb := mul_le_mul_of_nonneg_left hE
    (show 0 ≤ WithZero.exp (-(V (h + A))) * WithZero.exp (-(V d)) from
      le_of_lt (mul_pos WithZero.exp_pos WithZero.exp_pos))
  rw [← he] at hb
  have ha : WithZero.exp (-(V (h + A))) * WithZero.exp (-(V d)) * WithZero.exp E =
      (WithZero.exp (-(V (h + d))) * WithZero.exp (-(V A))) *
        WithZero.exp (E - lambertRefinementTransportOrder h A d n) := by
    simp only [← WithZero.exp_add]
    congr 1
    dsimp [lambertRefinementTransportOrder, V]
    ring
  rw [ha] at hb
  exact le_of_mul_le_mul_left hb (mul_pos WithZero.exp_pos WithZero.exp_pos)

/-- Exchanging numerator prefix and pole offset transports coefficient bounds without any scalar correction. -/
theorem lambertRefinementDeterminant_coeff_valuation_le_of_swap
    (ζ : K) (h A b d s n i : ℕ) (hA : A ≤ b + d) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (E : ℤ)
    (hE : Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      ((lambertRefinementDeterminant (RatFunc.X : RatFunc ℚ) h b A (h + (b + d - A)) s).coeff i)) ≤
        WithZero.exp E) :
    Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      ((lambertRefinementDeterminant (RatFunc.X : RatFunc ℚ) h A b (h + d) s).coeff i)) ≤
        WithZero.exp E := by
  have he := lambertRefinementDeterminant_prefix_swap (RatFunc.X : RatFunc ℚ) h A b
    (b + (h + d)) s (by omega) (by omega) ratFunc_X_pow_injective
  rw [show b + (h + d) - b = h + d by omega,
    show b + (h + d) - A = h + (b + d - A) by omega] at he
  rwa [he]

end
end Lambert
