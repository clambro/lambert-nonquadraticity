import Lambert.Arithmetic.BivariateProductFormula
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.Analysis.Polynomial.MahlerMeasure

/-! # Finite and infinite height contributions of split polynomials -/
namespace Lambert
noncomputable section
open Polynomial NumberField Finset

/-- A monic linear polynomial has Gauss norm equal to the maximum of one and the absolute value of its root. -/
theorem gaussNorm_X_sub_C_one {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (x : K) :
    (X-C x).gaussNorm v 1=max (v x) 1 := by
  have h0 := (X-C x).le_gaussNorm v (by norm_num : (0 : ℝ)≤1) 0
  have h1 := (X-C x).le_gaussNorm v (by norm_num : (0 : ℝ)≤1) 1
  simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg_eq_map, one_pow, mul_one] at h0
  simp only [coeff_sub, coeff_X_one, coeff_C_succ, sub_zero, map_one, one_pow, mul_one] at h1
  apply le_antisymm _ (max_le h0 h1)
  obtain ⟨i,hi⟩ := (X-C x).exists_eq_gaussNorm v 1
  rw [hi]
  rcases i with _|i
  · simp [coeff_sub, coeff_X_zero, coeff_C_zero]
  rcases i with _|i
  · simp
  · simp [coeff_X, Nat.add_eq_zero_iff]

/-- A primitive integer polynomial has Gauss norm one at every finite place of a number field. -/
theorem primitive_integer_gaussNorm_eq_one {K : Type*} [Field K] [NumberField K]
    (p : ℤ[X]) (hp : p.IsPrimitive) (v : FinitePlace K) :
    (p.map (Int.castRingHom K)).gaussNorm v.val 1=1 := by
  let pO := p.map (Int.castRingHom (𝓞 K))
  have htop : pO.contentIdeal=⊤ := by
    dsimp only [pO]
    rw [contentIdeal_map_eq_map_contentIdeal,
      (isPrimitive_iff_contentIdeal_eq_top p).mp hp, Ideal.map_top]
  have hvint (z : ℤ) : v (z : K)≤1 := by
    have he := FinitePlace.norm_le_one K v.maximalIdeal (z : 𝓞 K)
    rw [FinitePlace.norm_embedding_eq] at he
    simpa only [RingOfIntegers.coe_eq_algebraMap, map_intCast] using he
  apply le_antisymm
  · obtain ⟨i,hi⟩ := (p.map (Int.castRingHom K)).exists_eq_gaussNorm v.val 1
    rw [hi]
    simpa only [one_pow, mul_one, coeff_map, Int.coe_castRingHom, FinitePlace.coe_apply] using hvint (p.coeff i)
  · by_contra! hv
    have hle : pO.contentIdeal≤v.maximalIdeal.asIdeal := by
      rw [contentIdeal_def, Ideal.span_le]
      intro z hz
      obtain ⟨i,hi,rfl⟩ := mem_coeffs_iff.mp hz
      apply (FinitePlace.norm_lt_one_iff_mem K v.maximalIdeal _).mp
      rw [FinitePlace.norm_embedding_eq]
      have he := (p.map (Int.castRingHom K)).le_gaussNorm v.val (by norm_num : (0 : ℝ)≤1) i
      have hlt := he.trans_lt hv
      simpa only [pO, coeff_map, Int.coe_castRingHom, one_pow, mul_one,
        RingOfIntegers.coe_eq_algebraMap, map_intCast, FinitePlace.coe_apply] using hlt
    rw [htop] at hle
    exact v.maximalIdeal.isPrime.ne_top (top_le_iff.mp hle)

private theorem gaussNorm_prod_linear {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (rs : Multiset K) :
    (rs.map (fun x => X-C x)).prod.gaussNorm v 1=(rs.map (fun x => max (v x) 1)).prod := by
  induction rs using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    simpa only [C_1, map_one] using (gaussNorm_C v 1 (1 : K))
  | @cons x rs ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, gaussNorm_mul hv (by norm_num : (0 : ℝ)<1),
      gaussNorm_X_sub_C_one, ih]

/-- A split primitive integer polynomial has the exact finite-place product identity dictated by its leading coefficient. -/
theorem primitive_split_finitePlace_product {K : Type*} [Field K] [NumberField K]
    (p : ℤ[X]) (hp : p.IsPrimitive) (hs : (p.map (Int.castRingHom K)).Splits)
    (v : FinitePlace K) :
    v (p.leadingCoeff : K)*((p.map (Int.castRingHom K)).roots.map (fun x => max (v x) 1)).prod=1 := by
  have he := primitive_integer_gaussNorm_eq_one p hp v
  conv_lhs at he => rw [hs.eq_prod_roots]
  rw [gaussNorm_mul v.add_le (by norm_num : (0 : ℝ)<1), gaussNorm_C,
    gaussNorm_prod_linear v.val v.add_le] at he
  simpa only [leadingCoeff_map_of_injective (f := Int.castRingHom K) Int.cast_injective,
    FinitePlace.coe_apply, Int.coe_castRingHom] using he

private theorem multiset_max_hasFiniteMulSupport {K : Type*} [Field K] [NumberField K]
    (rs : Multiset K) :
    (fun v : FinitePlace K => (rs.map (fun x => max (v x) 1)).prod).HasFiniteMulSupport := by
  induction rs using Multiset.induction_on with
  | empty => simpa only [Multiset.map_zero, Multiset.prod_zero] using
      (Function.hasFiniteMulSupport_one : (fun _ : FinitePlace K => (1 : ℝ)).HasFiniteMulSupport)
  | @cons x rs ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (finitePlace_max_hasFiniteMulSupport x).mul ih

private theorem finprod_multiset_max {K : Type*} [Field K] [NumberField K] (rs : Multiset K) :
    (∏ᶠ v : FinitePlace K, (rs.map (fun x => max (v x) 1)).prod) =
      (rs.map finitePlaceDenominator).prod := by
  induction rs using Multiset.induction_on with
  | empty => simp
  | @cons x rs ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [finprod_mul_distrib (finitePlace_max_hasFiniteMulSupport x)]
    · rw [ih]; rfl
    · exact multiset_max_hasFiniteMulSupport rs

/-- The product of the finite denominator contributions of all roots of a split primitive polynomial equals the absolute norm of its leading coefficient. -/
theorem primitive_split_denominator_product {K : Type*} [Field K] [NumberField K]
    (p : ℤ[X]) (hp : p.IsPrimitive) (hs : (p.map (Int.castRingHom K)).Splits) :
    ((p.map (Int.castRingHom K)).roots.map finitePlaceDenominator).prod =
      |(p.leadingCoeff : ℝ)| ^ Module.finrank ℚ K := by
  have ha : (p.leadingCoeff : K)≠0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hp.ne_zero
  have he : (∏ᶠ v : FinitePlace K, v (p.leadingCoeff : K))*
      (∏ᶠ v : FinitePlace K, ((p.map (Int.castRingHom K)).roots.map (fun x => max (v x) 1)).prod)=1 := by
    rw [← finprod_mul_distrib (FinitePlace.hasFiniteMulSupport ha)]
    · simp only [primitive_split_finitePlace_product p hp hs, finprod_one]
    · exact multiset_max_hasFiniteMulSupport _
  rw [finprod_multiset_max, FinitePlace.prod_eq_inv_abs_norm ha, Rat.cast_inv, Rat.cast_abs] at he
  have hn : Algebra.norm ℚ (p.leadingCoeff : K)=(p.leadingCoeff : ℚ)^Module.finrank ℚ K := by
    rw [← map_intCast (algebraMap ℚ K), Algebra.norm_algebraMap]
  rw [hn, Rat.cast_pow, Rat.cast_intCast, abs_pow] at he
  have haR : (p.leadingCoeff : ℝ)≠0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hp.ne_zero
  exact ((inv_mul_eq_one₀ (pow_ne_zero _ (abs_ne_zero.mpr haR))).mp he).symm

/-- At any complex embedding, the Mahler measure of a split integer polynomial is its leading-coefficient contribution plus the logarithmic contributions of its roots. -/
theorem split_integer_logMahler_eq {K : Type} [Field K] [NumberField K]
    (p : ℤ[X]) (hs : (p.map (Int.castRingHom K)).Splits) (σ : K →+* ℂ) :
    (p.map (Int.castRingHom ℂ)).logMahlerMeasure = Real.log |(p.leadingCoeff : ℝ)|+
      ((p.map (Int.castRingHom K)).roots.map (fun x => Real.log (max ‖σ x‖ 1))).sum := by
  have hc : σ.comp (Int.castRingHom K)=Int.castRingHom ℂ := Subsingleton.elim _ _
  have hm : (p.map (Int.castRingHom K)).map σ=p.map (Int.castRingHom ℂ) := by rw [Polynomial.map_map,hc]
  rw [← hm, logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots,
    leadingCoeff_map_of_injective σ.injective, leadingCoeff_map_of_injective (f := Int.castRingHom K) Int.cast_injective,
    hs.roots_map_of_injective σ.injective, Multiset.map_map]
  simp only [Int.coe_castRingHom, map_intCast, Complex.norm_intCast]
  congr 1
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro x _
  simpa only [Function.comp_apply, max_comm] using Real.posLog_eq_log_max_one (norm_nonneg (σ x))

private theorem sum_multiset_embeddings {K : Type} [Field K] [NumberField K]
    (rs : Multiset K) (f : (K →+* ℂ) → K → ℝ) :
    (rs.map (fun x => ∑ σ : K →+* ℂ, f σ x)).sum =
      ∑ σ : K →+* ℂ, (rs.map (f σ)).sum := by
  induction rs using Multiset.induction_on with
  | empty => simp
  | @cons x rs ih => simp only [Multiset.map_cons, Multiset.sum_cons, ih, sum_add_distrib]

/-- For a primitive integer polynomial that splits in a number field, the sum of its root heights is the field degree times its logarithmic Mahler measure. -/
theorem primitive_split_sum_logHeight {K : Type} [Field K] [NumberField K]
    (p : ℤ[X]) (hp : p.IsPrimitive) (hs : (p.map (Int.castRingHom K)).Splits) :
    ((p.map (Int.castRingHom K)).roots.map Height.logHeight₁).sum =
      (Module.finrank ℚ K : ℝ)*(p.map (Int.castRingHom ℂ)).logMahlerMeasure := by
  classical
  let rs := (p.map (Int.castRingHom K)).roots
  have hfinite : (rs.map (fun x => Real.log (finitePlaceDenominator x))).sum =
      (Module.finrank ℚ K : ℝ)*Real.log |(p.leadingCoeff : ℝ)| := by
    have he := congrArg Real.log (primitive_split_denominator_product p hp hs)
    rw [Real.log_pow, Real.log_multiset_prod] at he
    · simpa only [Multiset.map_map, Function.comp_apply, rs] using he
    · intro a ha
      obtain ⟨x,_,rfl⟩ := Multiset.mem_map.mp ha
      exact (lt_of_lt_of_le zero_lt_one (one_le_finitePlaceDenominator x)).ne'
  have harch := Finset.sum_congr (s₁ := (univ : Finset (K →+* ℂ))) rfl
    (fun σ _ => split_integer_logMahler_eq p hs σ)
  simp only [sum_const, nsmul_eq_mul, sum_add_distrib] at harch
  have hcard : Fintype.card (K →+* ℂ)=Module.finrank ℚ K := by
    rw [Fintype.card_congr (RingHom.equivRatAlgHom K ℂ), AlgHom.card]
  rw [Finset.card_univ, hcard] at harch
  change (rs.map Height.logHeight₁).sum=_
  have he : (rs.map Height.logHeight₁).sum =
      (rs.map (fun x => Real.log (finitePlaceDenominator x))).sum+
        (rs.map (fun x => ∑ σ : K →+* ℂ, Real.log (max ‖σ x‖ 1))).sum := by
    simp only [numberField_logHeight_eq_embeddings, Multiset.sum_map_add]
  rw [he,hfinite,sum_multiset_embeddings]
  exact harch.symm

end
end Lambert
