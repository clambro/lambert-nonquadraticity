import Lambert.Analysis.AtomicMoment
import Lambert.Arithmetic.GeometricMoments
import Lambert.Arithmetic.GeometricDeterminantFormula
import Lambert.Analysis.GeometricProduct

/-!
# Uniform logarithmic bounds for shifted geometric determinants

The Cauchy border quotient bounds the logarithmic error linearly in the rank,
independently of the nonnegative moment shift.
-/
namespace Lambert
noncomputable section
open Matrix Finset MeasureTheory
open scoped Classical

/-- The shifted reciprocal-geometric moment determinant has entries `1/(q^(i+j+s+1)-1)`. -/
def shiftedGeometricMomentDeterminant (q : ℝ) (h s : ℕ) : ℝ :=
  (Matrix.of fun i j : Fin h => (q ^ (i.val + j.val + s + 1) - 1)⁻¹).det

/-- Shifted geometric moment integrals equal the reciprocal power-difference matrix at every rank. -/
theorem shiftedGeometricMomentMatrix_integral (q : ℝ) (hq : 1 < q) (h s : ℕ) :
    (Matrix.of fun i j : Fin h => ∫ t, t ^ (i.val + j.val + s)
      ∂geometricMomentMeasure q⁻¹) =
    (Matrix.of fun i j : Fin h => (q ^ (i.val + j.val + s + 1) - 1)⁻¹) := by
  have hu := inv_pos.mpr (zero_lt_one.trans hq)
  have hu1 := inv_lt_one_of_one_lt₀ hq
  ext i j
  simp only [Matrix.of_apply, geometricMomentMeasure_moment _ hu.le hu1,
    geometricReciprocalMoment_inverse_base _ hu.ne', inv_inv]

/-- Shifted reciprocal-geometric moment determinants are positive for all ranks and nonnegative shifts. -/
theorem shiftedGeometricMomentDeterminant_pos (q : ℝ) (hq : 1 < q) (h s : ℕ) :
    0 < shiftedGeometricMomentDeterminant q h s := by
  induction h with
  | zero => simp [shiftedGeometricMomentDeterminant]
  | succ h ih =>
    have he := shiftedGeometricHankel_det_quotient_product q hq h s
    change shiftedGeometricMomentDeterminant q (h + 1) s /
      shiftedGeometricMomentDeterminant q h s = _ at he
    have hp : 0 < shiftedGeometricMomentDeterminant q (h + 1) s /
        shiftedGeometricMomentDeterminant q h s := by
      rw [he]
      apply mul_pos (inv_pos.mpr (sub_pos.mpr (one_lt_pow₀ hq (by omega))))
      apply prod_pos
      intro i _
      apply mul_pos (pow_pos (zero_lt_one.trans hq) _)
      apply pow_pos
      exact div_pos (sub_pos.mpr (one_lt_pow₀ hq (by have := i.isLt; omega)))
        (sub_pos.mpr (one_lt_pow₀ hq (by omega)))
    exact (div_pos_iff_of_pos_right ih).mp hp

private def logRemainder (q : ℝ) (k : ℕ) : ℝ := Real.log (1 - q⁻¹ ^ k)

private theorem log_difference (q : ℝ) (hq : 1 < q) (k : ℕ) (hk : 0 < k) :
    Real.log (q ^ k - 1) = k * Real.log q + logRemainder q k := by
  have he := geometricDifference_above_eq q (zero_lt_one.trans hq) 0 k (Nat.zero_le _)
  simp only [pow_zero, Nat.sub_zero] at he
  rw [he, Real.log_mul (pow_pos (zero_lt_one.trans hq) k).ne'
    (sub_pos.mpr (pow_lt_one₀ (inv_pos.mpr (zero_lt_one.trans hq)).le
      (inv_lt_one_of_one_lt₀ hq) hk.ne')).ne', Real.log_pow]
  rfl

private theorem sum_remainder_bounds {ι : Type*} [DecidableEq ι]
    (q : ℝ) (hq : 1 < q) (S : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ S, 0 < e i) (hi : Set.InjOn e S) :
    Real.log (geometricProductFloor q⁻¹) ≤ ∑ i ∈ S, logRemainder q (e i) ∧
      (∑ i ∈ S, logRemainder q (e i)) ≤ 0 := by
  have hu := inv_pos.mpr (zero_lt_one.trans hq)
  have hu1 := inv_lt_one_of_one_lt₀ hq
  obtain ⟨hl, hr⟩ := geometricProductFloor_le_prod_of_injOn q⁻¹ hu hu1 S e he hi
  have hp (i : ι) (hi : i ∈ S) : 0 < 1 - q⁻¹ ^ e i :=
    sub_pos.mpr (pow_lt_one₀ hu.le hu1 (he i hi).ne')
  have hlog := Real.log_prod (fun i hi => (hp i hi).ne')
  constructor
  · simpa only [hlog, logRemainder] using
      Real.log_le_log (geometricProductFloor_pos _) hl
  · simpa only [hlog, Real.log_one, logRemainder] using
      Real.log_le_log (prod_pos hp) hr

private theorem sum_indices (n : ℕ) :
    (∑ i : Fin n, (i.val : ℝ)) = (n : ℝ) * (n - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

private theorem log_quotient (q : ℝ) (hq : 1 < q) (n s : ℕ) :
    Real.log (shiftedGeometricMomentDeterminant q (n + 1) s) -
      Real.log (shiftedGeometricMomentDeterminant q n s) =
    -(((n : ℝ) + 1) ^ 2 + s * (n + 1)) * Real.log q +
      2 * (∑ i : Fin n, logRemainder q (n - i.val)) -
      2 * (∑ i : Fin n, logRemainder q (n + i.val + s + 1)) -
      logRemainder q (2 * n + s + 1) := by
  have hd (k : ℕ) (hk : 0 < k) : 0 < q ^ k - 1 := sub_pos.mpr (one_lt_pow₀ hq hk.ne')
  have hf (i : Fin n) : 0 < q ^ (2 * i.val + s + 1) *
      ((q ^ (n - i.val) - 1) / (q ^ (n + i.val + s + 1) - 1)) ^ 2 :=
    mul_pos (pow_pos (zero_lt_one.trans hq) _) (pow_pos
      (div_pos (hd _ (by have := i.isLt; omega)) (hd _ (by omega))) _)
  have he := congrArg Real.log (shiftedGeometricHankel_det_quotient_product q hq n s)
  change Real.log (shiftedGeometricMomentDeterminant q (n + 1) s /
    shiftedGeometricMomentDeterminant q n s) = _ at he
  rw [Real.log_div (shiftedGeometricMomentDeterminant_pos q hq _ _).ne'
    (shiftedGeometricMomentDeterminant_pos q hq _ _).ne',
    Real.log_mul (inv_ne_zero (hd _ (by omega)).ne') (prod_pos (fun i _ => hf i)).ne',
    Real.log_inv, Real.log_prod (fun i _ => (hf i).ne')] at he
  have hterm (i : Fin n) : Real.log ((q ^ (n - i.val) - 1) /
      (q ^ (n + i.val + s + 1) - 1)) =
      (-(2 * (i.val : ℝ) + s + 1)) * Real.log q +
        logRemainder q (n - i.val) - logRemainder q (n + i.val + s + 1) := by
    rw [Real.log_div (hd _ (by have := i.isLt; omega)).ne' (hd _ (by omega)).ne',
      log_difference q hq _ (by have := i.isLt; omega), log_difference q hq _ (by omega),
      Nat.cast_sub i.isLt.le]
    push_cast
    ring
  have hlogfactor (i : Fin n) :
      Real.log (q ^ (2 * i.val + s + 1) *
        ((q ^ (n - i.val) - 1) / (q ^ (n + i.val + s + 1) - 1)) ^ 2) =
      (2 * (i.val : ℝ) + s + 1) * Real.log q + 2 *
        ((-(2 * (i.val : ℝ) + s + 1)) * Real.log q +
        logRemainder q (n - i.val) - logRemainder q (n + i.val + s + 1)) := by
    rw [Real.log_mul (pow_pos (zero_lt_one.trans hq) _).ne'
      (pow_ne_zero 2 (div_ne_zero (hd _ (by have := i.isLt; omega)).ne'
        (hd _ (by omega)).ne')), Real.log_pow, Real.log_pow, hterm]
    push_cast
    rfl
  simp_rw [hlogfactor] at he
  rw [log_difference q hq _ (by omega)] at he
  push_cast at he
  simp only [mul_add, mul_sub, add_mul, neg_mul, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum,
    sum_neg_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at he
  rw [sum_indices] at he
  linear_combination he

/-- The logarithm of a shifted reciprocal-geometric determinant differs from its exact cubic polynomial by a uniform linear error. -/
theorem shiftedGeometricMomentDeterminant_log_bounds (q : ℝ) (hq : 1 < q) (h s : ℕ) :
    let E := (h : ℝ) * (h + 1) * (2 * h + 1) / 6 + s * h * (h + 1) / 2;
    -E * Real.log q + 2 * h * Real.log (geometricProductFloor q⁻¹) ≤
        Real.log (shiftedGeometricMomentDeterminant q h s) ∧
    Real.log (shiftedGeometricMomentDeterminant q h s) ≤
      -E * Real.log q - 3 * h * Real.log (geometricProductFloor q⁻¹) := by
  dsimp only
  induction h with
  | zero => simp [shiftedGeometricMomentDeterminant]
  | succ h ih =>
    have ha := sum_remainder_bounds q hq univ (fun i : Fin h => h - i.val)
      (by intro i _; have := i.isLt; omega)
      (by intro i _ j _ he; apply Fin.ext; dsimp at he; have := i.isLt; have := j.isLt; omega)
    have hb := sum_remainder_bounds q hq univ (fun i : Fin h => h + i.val + s + 1)
      (by intros; omega) (by intro i _ j _ he; apply Fin.ext; dsimp at he; omega)
    have hc := sum_remainder_bounds q hq {2 * h + s + 1} id
      (by intro i hi; simp only [mem_singleton, id_eq] at *; omega) (by intro i _ j _ he; exact he)
    simp only [sum_singleton, id_eq] at hc
    have he := log_quotient q hq h s
    push_cast
    constructor <;> nlinarith [ih.1, ih.2, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]

end
end Lambert
