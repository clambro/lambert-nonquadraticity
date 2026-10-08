import Lambert.Determinants.Local
import Lambert.Determinants.LocalIdentity
import Lambert.Determinants.RectangularResidues
import Lambert.Determinants.CyclotomicExponent

/-! # Cyclotomic cancellation for equally translated row and pole windows -/
namespace Lambert
noncomputable section
open Finset PowerSeries Matrix
open scoped Classical WithZero

/-- The translated square-window exponent uses the Taylor filtration for small root orders and the shifted residue support for large orders. -/
def lambertTranslatedCyclotomicExponent (h k n : ℕ) : ℕ :=
  if 2*n ≤ h then lambertCyclotomicExponent h n
  else (h-n)+min h (2*(h+k-n))

/-- The local determinant order subtracts the shifted residue rank from h outside the filtration range. -/
def lambertLocalOrder (h k n : ℕ) : ℕ :=
  if 2*n ≤ h then ∑ r ∈ range h, (h-(r+1)*(2*n))
  else h-min h (2*(h+k-n))

private theorem large_vandermonde (h n : ℕ) (hh : h ≤ 2*n) :
    (∑ r ∈ range h, (h-(r+1)*n)) = h-n := by
  cases h with
  | zero => simp
  | succ h =>
    rw [sum_range_succ']
    have hz : (∑ r ∈ range h, (h+1-(r+1+1)*n)) = 0 := by
      apply sum_eq_zero
      intro r _
      have := Nat.mul_le_mul_right n (show 2 ≤ r+1+1 by omega)
      omega
    simp only [hz, zero_add, one_mul]

/-- The translated cyclotomic exponent exactly accounts for regularization, Vandermonde collisions, and determinant cancellation. -/
theorem lambertTranslatedCyclotomicExponent_accounting (h k n : ℕ) (hn : 0 < n) :
    lambertTranslatedCyclotomicExponent h k n + lambertLocalOrder h k n =
      h+∑ r ∈ range h, (h-(r+1)*n) := by
  unfold lambertTranslatedCyclotomicExponent lambertLocalOrder
  split_ifs with hh
  · have he := lambertCyclotomicExponent_accounting h n hn
    have hm : 2*min h n-h = 0 := by omega
    simpa only [lambertLocalDeterminantOrder, hm, Nat.zero_max] using he
  · rw [large_vandermonde h n (by omega)]
    omega

/-- The translated square local matrix attains the order needed for its cyclotomic exponent. -/
theorem lambertCertificateLocalMatrix_order_ge {K : Type*} [Field K] [Algebra ℚ K]
    (ζ x : K) (h k n : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    (lambertLocalOrder h k n : ℕ∞) ≤
      (lambertCertificateLocalMatrix ζ x h k 0 k).det.order := by
  have hm : (lambertCertificateLocalMatrix ζ x h k 0 k).det =
      Matrix.det (fun i j : Fin h => lambertLocalEntry ζ x (k+i.val) (k+j.val)) := by
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    have hj : j.val < h := by have := j.isLt; omega
    simp only [lambertCertificateLocalMatrix, Fin.addCases, dif_pos hj, Fin.val_castLT]
    exact (lambertLocalEntry_symm ζ x (j.val+k) (k+i.val)).trans (by rw [Nat.add_comm j.val k])
  rw [hm]
  unfold lambertLocalOrder
  split_ifs
  · simpa only [Nat.mul_comm (2*n)] using
      lambertLocalEntry_det_order_ge_filtration ζ x h k k n h hn hζ
  · have he := lambertLocalEntry_det_order_ge_residue ζ x h k n hζ
    have hh : h-min h (2*(h+k-n)) = 2*min h (n-k)-h := by omega
    simpa only [hh] using he

/-- Every constant evaluation of a translated square determinant satisfies its cyclotomic pole bound. -/
theorem lambertPoleDeterminant_eval_valuation_le {K : Type*} [Field K] [Algebra ℚ K]
    (ζ : K) (h k n : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (x : K) :
    Valued.v (((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k h k).map
      (lambertLocalMap ζ (hζ.ne_zero hn.ne'))).eval (algebraMap K (LaurentSeries K) x)) ≤
        WithZero.exp (lambertTranslatedCyclotomicExponent h k n : ℤ) := by
  let f := HahnSeries.ofPowerSeries ℤ K
  let V := ∑ r ∈ range h, (h-(r+1)*n)
  let D := lambertLocalOrder h k n
  let E := lambertTranslatedCyclotomicExponent h k n
  have hA := laurentSeries_valuation_le_of_order (lambertCertificateLocalMatrix ζ x h k 0 k).det D
    (lambertCertificateLocalMatrix_order_ge ζ x h k n hn hζ)
  rw [lambertCertificateLocalMatrix_identity ζ x (hζ.ne_zero hn.ne') h k 0 k] at hA
  simp only [Nat.add_zero] at hA
  have hv : Valued.v (f (vandermonde (fun j : Fin h => lambertLocalBase ζ ^ (k+j.val))).det) =
      WithZero.exp (-(V : ℤ)) :=
    laurentSeries_valuation_eq_of_order _ V (lambertTranslatedLocalVandermonde_order ζ h k n hn hζ)
  have hx : Valued.v (f (PowerSeries.X : PowerSeries K)^h) = WithZero.exp (-(h : ℤ)) := by
    simpa only [map_pow] using
      laurentSeries_valuation_eq_of_order ((PowerSeries.X : PowerSeries K)^h) h (order_X_pow h)
  have hs : Valued.v (lambertAugmentedSign h 0 : LaurentSeries K) = 1 := by
    rcases sq_eq_one_iff.mp (lambertAugmentedSign_sq h 0) with hs | hs <;> simp [hs]
  change Valued.v (f PowerSeries.X^h * ((lambertAugmentedSign h 0 : LaurentSeries K) *
    f (vandermonde (fun j : Fin h => lambertLocalBase ζ ^ (k+j.val))).det) * _) ≤ _ at hA
  rw [map_mul, map_mul, map_mul, hx, hs, hv, one_mul] at hA
  have he : (h : ℤ)+V = E+D := by
    exact_mod_cast (lambertTranslatedCyclotomicExponent_accounting h k n hn).symm
  have hb : WithZero.exp (-(D : ℤ)) =
      WithZero.exp (-(h : ℤ))*WithZero.exp (-(V : ℤ))*WithZero.exp (E : ℤ) := by
    rw [← WithZero.exp_add, ← WithZero.exp_add]
    congr 1
    omega
  rw [hb] at hA
  exact le_of_mul_le_mul_left hA (mul_pos WithZero.exp_pos WithZero.exp_pos)

/-- Constant interpolation transfers the translated cyclotomic pole bound to every coefficient. -/
theorem lambertPoleDeterminant_coeff_valuation_le {K : Type*} [Field K] [Algebra ℚ K]
    (ζ : K) (h k n i : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k h k).coeff i)) ≤
        WithZero.exp (lambertTranslatedCyclotomicExponent h k n : ℤ) := by
  let : Infinite K := Infinite.of_injective _ (algebraMap ℚ K).injective
  have he := laurentSeries_coeff_valuation_le_of_eval
    ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k h k).map
      (lambertLocalMap ζ (hζ.ne_zero hn.ne'))) (-(lambertTranslatedCyclotomicExponent h k n : ℤ))
    (fun x => by simpa only [neg_neg] using
      lambertPoleDeterminant_eval_valuation_le ζ h k n hn hζ x) i
  simpa only [Polynomial.coeff_map, neg_neg] using he

/-- Root orders at or beyond the translated window endpoint require no cyclotomic clearing. -/
theorem lambertTranslatedCyclotomicExponent_eq_zero (h k n : ℕ) (hn : 0 < n) (hh : h+k ≤ n) :
    lambertTranslatedCyclotomicExponent h k n = 0 := by
  simp only [lambertTranslatedCyclotomicExponent, if_neg (show ¬2*n ≤ h by omega)]
  omega

end
end Lambert
