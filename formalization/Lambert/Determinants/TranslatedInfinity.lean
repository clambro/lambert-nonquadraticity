import Lambert.Determinants.Determinant
import Lambert.Determinants.InfinityData
import Mathlib.Algebra.Order.Rearrangement

/-!
# Shifted Lambert determinants at infinity

Sorted augmented row weights bound the permutation degrees. Subtracting the
Vandermonde degree gives a signed normalization, with the square case recovered.
-/
namespace Lambert
noncomputable section
open Polynomial Matrix Finset WithZero
open scoped Classical
private abbrev v := RatFunc.inftyValuation ℚ

/-- The signed infinity normalization subtracts the sorted augmented degree from the Vandermonde degree. -/
def lambertTranslatedInfinityExponent (h k d s : ℕ) : ℤ :=
  ∑ j : Fin (h + d), (j.val : ℤ) * (k+j.val) -
    ∑ j : Fin (h + d), ((k : ℤ)+j.val) *
      lambertAugmentedRowWeight h d s (Tuple.sort (lambertAugmentedRowWeight h d s) j)

/-- Sorting the augmented row weights bounds every permutation degree. -/
theorem lambertAugmented_sorted_degree_bound (h k d s : ℕ) (σ : Equiv.Perm (Fin (h + d))) :
    (∑ j : Fin (h + d), (lambertAugmentedRowWeight h d s (σ j) : ℤ) * (k+j.val)) ≤
      ∑ j : Fin (h + d), ((k : ℤ)+j.val) *
        lambertAugmentedRowWeight h d s (Tuple.sort (lambertAugmentedRowWeight h d s) j) := by
  let w := lambertAugmentedRowWeight h d s
  let τ := Tuple.sort w
  have hi : Monotone (fun j : Fin (h + d) => ((k : ℤ)+j.val)) := by
    intro i j hij
    change (k : ℤ)+i.val ≤ (k : ℤ)+j.val
    omega
  have hw : Monotone (fun j => (w (τ j) : ℤ)) := by
    intro i j hij
    exact Int.ofNat_le.mpr (Tuple.monotone_sort w hij)
  have he := (hi.monovary hw).sum_mul_comp_perm_le_sum_mul (σ := σ.trans τ.symm)
  simpa only [Equiv.trans_apply, Equiv.apply_symm_apply, mul_comm] using he

private theorem augmented_entry_bound (z : RatFunc ℚ) (hz : v z ≤ 1) (h k d s : ℕ)
    (i j : Fin (h + d)) :
    v (((lambertAugmentedMatrix (RatFunc.X : RatFunc ℚ) h k d s) i j).eval z) ≤
      exp ((lambertAugmentedRowWeight h d s i : ℤ) * (k+j.val)) := by
  refine Fin.addCases ?_ ?_ i
  · intro r
    simpa only [lambertAugmentedMatrix, lambertAugmentedRowWeight, Fin.addCases_left, Nat.cast_add]
      using lambertPoleEntry_inftyValuation_le z hz (r.val + s) (k+j.val)
  · intro r
    simp only [lambertAugmentedMatrix, Fin.addCases_right]
    rw [eval_C, map_pow, RatFunc.inftyValuation.X, ← exp_nsmul]
    simp only [lambertAugmentedRowWeight, Fin.addCases_right, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, mul_one]
    rw [mul_comm]


private theorem augmented_bound (z : RatFunc ℚ) (hz : v z ≤ 1) (h k d s : ℕ) :
    v (((lambertAugmentedMatrix (RatFunc.X : RatFunc ℚ) h k d s).det).eval z) ≤
      exp (∑ j : Fin (h + d), ((k : ℤ)+j.val) *
        lambertAugmentedRowWeight h d s (Tuple.sort (lambertAugmentedRowWeight h d s) j)) := by
  change v ((Polynomial.evalRingHom z) _) ≤ _
  rw [(Polynomial.evalRingHom z).map_det, Matrix.det_apply']
  apply Valuation.map_sum_le
  intro σ _
  have hp := ratFunc_product_inftyValuation_le univ (fun j : Fin (h + d) =>
    ((lambertAugmentedMatrix (RatFunc.X : RatFunc ℚ) h k d s) (σ j) j).eval z)
    (fun j => (lambertAugmentedRowWeight h d s (σ j) : ℤ) * (k+j.val))
    (fun j _ => augmented_entry_bound z hz h k d s (σ j) j)
  have hs : v (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : RatFunc ℚ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with he | he <;> simp [he]
  rw [map_mul, hs, one_mul]
  exact hp.trans (exp_le_exp.mpr (lambertAugmented_sorted_degree_bound h k d s σ))

/-- The translated geometric Vandermonde has infinity degree equal to the sum of j*(k+j) over its column indices. -/
theorem lambertVandermonde_inftyValuation (h k : ℕ) :
    v ((vandermonde (fun j : Fin h => (RatFunc.X : RatFunc ℚ) ^ (k+j.val))).det) =
      exp (∑ j : Fin h, (j.val : ℤ) * (k+j.val)) := by
  rw [det_vandermonde, map_prod]
  simp_rw [map_prod]
  have he : (∏ i : Fin h, ∏ j ∈ Ioi i, v (RatFunc.X ^ (k+j.val) - RatFunc.X ^ (k+i.val))) =
      ∏ i : Fin h, ∏ j ∈ Ioi i, exp ((k : ℤ)+j.val) := by
    apply prod_congr rfl
    intro i _
    apply prod_congr rfl
    intro j hj
    have hij : i < j := mem_Ioi.mp hj
    exact by simpa only [Nat.cast_add] using lambertPowerDifference_inftyValuation (k+i.val) (k+j.val) (by omega)
  rw [he]
  have hp {ι : Type} (s : Finset ι) (f : ι → ℤ) :
      (∏ i ∈ s, exp (f i)) = exp (∑ i ∈ s, f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => rw [prod_insert hi, sum_insert hi, ih, exp_add]
  rw [show (∏ i : Fin h, ∏ j ∈ Ioi i, exp ((k : ℤ)+j.val)) =
      ∏ i : Fin h, exp (∑ j ∈ Ioi i, ((k : ℤ)+j.val)) from
        prod_congr rfl (fun (i : Fin h) _ => hp (Ioi i) (fun (j : Fin h) => ((k : ℤ)+j.val)))]
  rw [hp]
  congr 1
  have hI (i : Fin h) : Ioi i = univ.filter (fun j : Fin h => i < j) := by ext j; simp
  simp_rw [hI, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← sum_filter]
  have hJ : univ.filter (fun i : Fin h => i < j) = Iio j := by ext i; simp
  rw [hJ, sum_const, nsmul_eq_mul, Fin.card_Iio]

/-- Every bounded specialization of a shifted-window determinant obeys the signed infinity bound. -/
theorem lambertPoleDeterminant_eval_inftyValuation (z : RatFunc ℚ)
    (hz : RatFunc.inftyValuation ℚ z ≤ 1) (h k d s : ℕ) :
    RatFunc.inftyValuation ℚ ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s).eval z) ≤
      exp (-lambertTranslatedInfinityExponent h k d s) := by
  have he := congrArg (fun p : (RatFunc ℚ)[X] => p.eval z)
    (lambertAugmentedMatrix_det_formal h k d s)
  simp only [eval_mul, eval_C] at he
  have hb := augmented_bound z hz h k d s
  rw [he, map_mul, map_mul] at hb
  have hs : v (lambertAugmentedSign h d : RatFunc ℚ) = 1 := by
    have he := congrArg v (show (lambertAugmentedSign h d : RatFunc ℚ) ^ 2 = 1 by
      exact_mod_cast lambertAugmentedSign_sq h d)
    rw [map_pow, map_one] at he
    exact (pow_eq_one_iff_of_nonneg (zero_le) (by decide : (2 : ℕ) ≠ 0)).mp he
  rw [hs, one_mul, lambertVandermonde_inftyValuation] at hb
  have heq : exp (∑ j : Fin (h + d), ((k : ℤ)+j.val) *
        lambertAugmentedRowWeight h d s (Tuple.sort (lambertAugmentedRowWeight h d s) j)) =
      exp (∑ j : Fin (h + d), (j.val : ℤ) * (k+j.val)) * exp (-lambertTranslatedInfinityExponent h k d s) := by
    rw [← exp_add]; congr 1; unfold lambertTranslatedInfinityExponent; ring
  rw [heq] at hb
  exact le_of_mul_le_mul_left hb WithZero.exp_pos

/-- Every coefficient of a shifted-window determinant obeys the signed infinity bound. -/
theorem lambertPoleDeterminant_coeff_inftyValuation (h k d s a : ℕ) :
    RatFunc.inftyValuation ℚ ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s).coeff a) ≤
      exp (-lambertTranslatedInfinityExponent h k d s) := by
  apply ratFunc_coeff_inftyValuation_le_of_eval
  intro a
  apply lambertPoleDeterminant_eval_inftyValuation
  by_cases ha : a = 0
  · simp [ha]
  · rw [RatFunc.inftyValuation.C _ ha]

end
end Lambert
