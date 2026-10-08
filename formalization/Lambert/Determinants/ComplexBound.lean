import Lambert.Determinants.Normalization
import Lambert.Determinants.EntryComplexBound
import Lambert.Analysis.GeometricProduct
import Lambert.Analysis.DeterminantExponentialBound

/-! # Complex growth for translated Lambert pole windows -/
namespace Lambert
noncomputable section
open Polynomial Finset Matrix
open scoped Classical

/-- A geometric Vandermonde is bounded below by its leading power times one product floor per column. -/
theorem lambertVandermonde_geometric_lower (q : ℝ) (hq : 1 < q) (k L : ℕ) :
    geometricProductFloor q⁻¹ ^ L * q ^ (∑ j : Fin L, j.val * (k+j.val)) ≤
      (vandermonde (fun j : Fin L => q ^ (k+j.val))).det := by
  have he : (vandermonde (fun j : Fin L => q ^ (k+j.val))).det =
      ∏ j : Fin L, ∏ i ∈ Iio j, (q ^ (k+j.val) - q ^ (k+i.val)) := by
    rw [det_vandermonde]
    have hi (i : Fin L) : Ioi i = univ.filter (fun j => i < j) := by ext j; simp
    have hj (j : Fin L) : Iio j = univ.filter (fun i => i < j) := by ext i; simp
    simp_rw [hi, hj, prod_filter]
    rw [prod_comm]
  have hb (j : Fin L) : geometricProductFloor q⁻¹ * q ^ (j.val * (k+j.val)) ≤
      ∏ i ∈ Iio j, (q ^ (k+j.val) - q ^ (k+i.val)) := by
    simpa only [Fin.card_Iio, Nat.mul_comm] using
      (geometricDifferenceProduct_above_bounds q hq (Iio j) (fun i : Fin L => k+i.val)
        (fun i _ j _ he => Fin.ext (Nat.add_left_cancel he)) (k+j.val) (fun i hi => by have := mem_Iio.mp hi; omega)).1
  rw [he]
  calc
    _ = ∏ j : Fin L, (geometricProductFloor q⁻¹ * q ^ (j.val * (k+j.val))) := by
      rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow_eq_pow_sum]
    _ ≤ _ := prod_le_prod (fun j _ => mul_nonneg (geometricProductFloor_pos _).le (pow_nonneg (zero_lt_one.trans hq).le _)) (fun j _ => hb j)


/-- The modulus of a translated complex geometric Vandermonde has the same product-floor lower bound as its real radial counterpart. -/
theorem lambertVandermonde_norm_lower (u : ℂ) (hu : 1<‖u‖) (k L : ℕ) :
    geometricProductFloor ‖u‖⁻¹^L * ‖u‖^(∑ j : Fin L, j.val*(k+j.val)) ≤
      ‖(vandermonde (fun j : Fin L => u^(k+j.val))).det‖ := by
  apply (lambertVandermonde_geometric_lower ‖u‖ hu k L).trans
  rw [det_vandermonde, det_vandermonde, norm_prod]
  apply prod_le_prod
  · intro i _
    exact prod_nonneg (fun j hj => sub_nonneg.mpr ((pow_right_strictMono₀ hu).monotone (by
      have := mem_Ioi.mp hj; omega)))
  · intro i _
    rw [norm_prod]
    apply prod_le_prod
    · intro j hj
      exact sub_nonneg.mpr ((pow_right_strictMono₀ hu).monotone (by have := mem_Ioi.mp hj; omega))
    · intro j _
      simpa only [norm_pow] using norm_sub_norm_le (u^(k+j.val)) (u^(k+i.val))

/-- At any complex argument, the normalized Lambert determinant has an explicit subcubic growth bound for proportional windows and shifts. -/
theorem lambertAugmented_normalized_norm_le_exp_of_one_lt_norm (u : ℂ) (hq : 1 < ‖u‖)
    (z : ℂ) (h k d s : ℕ) :
    ‖(C (u ^ lambertTranslatedInfinityExponent h k d s) *
      lambertPoleDeterminant u h k (h+d) s).eval z‖ ≤
      Real.exp (((h + d : ℕ) : ℝ) ^ 2 + (h + d : ℕ) *
        (1 + ‖z‖ + (h + s + k + (h + d) : ℕ) * (‖u‖ - 1)⁻¹) -
          (h + d : ℕ) * Real.log (geometricProductFloor ‖u‖⁻¹)) := by
  let q := ‖u‖
  let L := h + d
  let C : ℝ := 1 + ‖z‖ + (h + s + k + L : ℕ) * (q - 1)⁻¹
  let W : ℤ := ∑ j : Fin L, ((k : ℤ)+j.val) *
    lambertAugmentedRowWeight h d s (Tuple.sort (lambertAugmentedRowWeight h d s) j)
  let V : ℝ := ‖(vandermonde (fun j : Fin L => u ^ (k+j.val))).det‖
  let S : ℕ := ∑ j : Fin L, j.val * (k+j.val)
  have hq0 := zero_lt_one.trans hq
  have hG := geometricProductFloor_pos q⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpow (k : ℕ) : q ^ k = Real.exp ((k : ℝ) * Real.log q) := by
    rw [Real.exp_nat_mul, Real.exp_log hq0]
  have hentry (i j : Fin L) :
      ‖((lambertAugmentedMatrix u h k d s) i j).eval z‖ ≤
        Real.exp (C + (lambertAugmentedRowWeight h d s i : ℝ) * (k+j.val) * Real.log q) := by
    refine Fin.addCases ?_ ?_ i
    · intro r
      simp only [lambertAugmentedMatrix, lambertAugmentedRowWeight, Fin.addCases_left]
      have hb := lambertPoleEntry_norm_le_of_one_lt_norm u hq z (r.val + s) (k+j.val)
      have hr := r.isLt
      have hj := j.isLt
      have hm : ‖z‖ + ((r.val + s + (k+j.val) : ℕ) : ℝ) * (q - 1)⁻¹ ≤ C := by
        have hh : ((r.val + s + (k+j.val) : ℕ) : ℝ) ≤ (h + s + k + L : ℕ) := by exact_mod_cast (by omega : r.val + s + (k+j.val) ≤ h + s + k + L)
        dsimp [C]
        nlinarith [mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (q - 1)⁻¹)]
      apply hb.trans
      calc
        _ ≤ q ^ ((r.val + s) * (k+j.val)) * Real.exp C := mul_le_mul_of_nonneg_left
          (hm.trans (by linarith [Real.add_one_le_exp C])) (by positivity)
        _ = _ := by
          rw [hpow, ← Real.exp_add]
          congr 1
          push_cast
          ring
    · intro r
      simp only [lambertAugmentedMatrix, lambertAugmentedRowWeight, Fin.addCases_right,
        eval_C, norm_pow]
      have he : q ^ ((k+j.val) * r.val) = Real.exp ((r.val : ℝ) * (k+j.val) * Real.log q) := by
        rw [hpow]
        congr 1
        push_cast
        ring
      rw [he]
      exact Real.exp_le_exp.mpr (le_add_of_nonneg_left hC)
  have hb := norm_det_le_exp_of_permutation_bound L
    ((lambertAugmentedMatrix u h k d s).map (Polynomial.eval z))
    (fun i j => (lambertAugmentedRowWeight h d s i : ℝ) * (k+j.val) * Real.log q)
    C ((W : ℝ) * Real.log q) hentry (fun σ => by
      have he := lambertAugmented_sorted_degree_bound h k d s σ
      have hr : (∑ j : Fin L, (lambertAugmentedRowWeight h d s (σ j) : ℝ) * (k+j.val)) ≤ W := by
        dsimp [W]
        exact_mod_cast he
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right hr (Real.log_pos hq).le)
  have hinj : Function.Injective (fun j : Fin L => u ^ (k+j.val)) := by
    intro i j he
    apply Fin.ext
    apply Nat.add_left_cancel (n := k)
    apply (pow_right_strictMono₀ hq).injective
    simpa only [norm_pow] using congrArg norm he
  have hid := congrArg (fun p : ℂ[X] => p.eval z) (lambertAugmentedMatrix_det u h k d s hinj)
  rw [eval_mul, eval_C] at hid
  have hmap : ((lambertAugmentedMatrix u h k d s).map (Polynomial.eval z)).det =
      ((lambertAugmentedMatrix u h k d s).det).eval z :=
    ((Polynomial.evalRingHom z).map_det _).symm
  rw [hmap] at hb
  rw [hid, norm_mul, norm_mul] at hb
  have hsign : ‖(lambertAugmentedSign h d : ℂ)‖ = 1 := by
    have he := congrArg (fun t : ℤ => ‖(t : ℂ)‖) (lambertAugmentedSign_sq h d)
    simp only [Int.cast_pow, norm_pow, Int.cast_one, norm_one] at he
    nlinarith [norm_nonneg (lambertAugmentedSign h d : ℂ)]
  rw [hsign, one_mul] at hb
  have hl : Real.exp ((L : ℝ) * Real.log (geometricProductFloor q⁻¹) + S * Real.log q) ≤ V := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hG, Real.exp_nat_mul, Real.exp_log hq0]
    exact lambertVandermonde_norm_lower u hq k L
  have hn := mul_le_mul_of_nonneg_right hl (norm_nonneg ((lambertPoleDeterminant u h k L s).eval z))
  have hraw := hn.trans hb
  have hd : ‖(lambertPoleDeterminant u h k L s).eval z‖ ≤
      Real.exp ((L : ℝ)^2 + L*C + (W : ℝ)*Real.log q -
        ((L : ℝ)*Real.log (geometricProductFloor q⁻¹) + S*Real.log q)) := by
    rw [Real.exp_sub]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    exact by simpa only [mul_comm] using hraw
  rw [eval_mul, eval_C, norm_mul, norm_zpow]
  apply (mul_le_mul_of_nonneg_left hd (zpow_pos hq0 _).le).trans_eq
  have hzpow : q ^ lambertTranslatedInfinityExponent h k d s =
      Real.exp ((lambertTranslatedInfinityExponent h k d s : ℝ) * Real.log q) := by
    rw [← Real.log_zpow, Real.exp_log (zpow_pos hq0 _)]
  rw [hzpow, ← Real.exp_add]
  congr 1
  have he : (lambertTranslatedInfinityExponent h k d s : ℝ) = (S : ℝ) - W := by
    unfold lambertTranslatedInfinityExponent
    dsimp [S, W, L]
    push_cast
    rfl
  rw [he]
  dsimp [C, L, q]
  ring

/-- At every complex base outside the unit disk, the normalized two-sided determinant has a uniform subcubic bound. -/
theorem lambertNormalizedDeterminant_norm_le_exp_of_one_lt_norm (u : ℂ) (hu : 1<‖u‖)
    (z : ℂ) (h k : ℕ) :
    ‖(lambertNormalizedDeterminant u h k).eval z‖ ≤
      Real.exp ((h : ℝ)^2+h*(1+‖z‖+(2*h+2*k : ℕ)*(‖u‖-1)⁻¹)-
        h*Real.log (geometricProductFloor ‖u‖⁻¹)) := by
  have he := lambertAugmented_normalized_norm_le_exp_of_one_lt_norm u hu z h k 0 k
  simp only [Nat.add_zero] at he
  unfold lambertNormalizedDeterminant
  convert he using 1
  congr 1
  push_cast
  ring

end
end Lambert
