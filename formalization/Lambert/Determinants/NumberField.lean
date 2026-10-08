import Lambert.Determinants.AlgebraicGrowth
import Lambert.Arithmetic.BivariateProductFormula

/-! # Number-field exclusion from the two-sided Lambert certificates -/
namespace Lambert
noncomputable section
open Polynomial Finset Filter Topology NumberField

/-- Every number field containing a real base q>1 and its Lambert value satisfies 202140 log q ≤ (42963+428220/π²) h(q). -/
theorem lambertValue_numberField_height_lower_bound
    {K : Type} [Field K] [NumberField K] (σ₀ : K →+* ℂ) (q x : K) (r : ℝ) (hr : 1 < r)
    (hq : σ₀ q = (r : ℂ)) (hx : σ₀ x = (lambertValue r : ℂ)) :
    202140*Real.log r ≤ (42963+428220/Real.pi^2)*Height.logHeight₁ q := by
  classical
  let C : ℝ := 42963+428220/Real.pi^2
  have hC : 0 < C := by dsimp [C]; positivity
  by_contra! hm
  let s : Finset (K →+* ℂ) := univ.erase σ₀
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_mul_lt (sub_pos.mpr hm) ((s.card : ℝ)*C)
  let R : (K →+* ℂ) → ℝ := fun σ => max ‖σ q‖ 1 * Real.exp δ
  have hR (σ : K →+* ℂ) : 1 < R σ := by
    have he : 1 < Real.exp δ := Real.one_lt_exp_iff.mpr hδ
    exact he.trans_le (le_mul_of_one_le_left (Real.exp_pos _).le (le_max_right _ _))
  have hRq (σ : K →+* ℂ) : ‖σ q‖ ≤ R σ :=
    (le_max_left _ _).trans (le_mul_of_one_le_right (le_trans zero_le_one (le_max_right _ _))
      (Real.one_le_exp hδ.le))
  have hlogR (σ : K →+* ℂ) : Real.log (R σ) = Real.log (max ‖σ q‖ 1)+δ := by
    dsimp only [R]
    rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
      (Real.exp_ne_zero _), Real.log_exp]
  let P := fun N => lambertCertificateIntegerPolynomial (60*N) (3*N)
  let D := fun N => (lambertCertificateClearingPolynomial (60*N) (3*N)).natDegree
  let y := fun N => ((P N).map (eval₂RingHom (Int.castRingHom K) q)).eval x
  have hy (N : ℕ) : y N ≠ 0 := by
    intro hz
    have hz' := congrArg σ₀ hz
    simp only [y, integerBivariate_eval_hom, hq, hx, map_zero] at hz'
    exact lambertCertificateIntegerPolynomial_real_ne_zero r hr _ _ hz'
  let g : ℕ → ℝ := fun N =>
    (D N : ℝ)*Real.log (finitePlaceDenominator q) +
      (60*(N : ℝ))*Real.log (finitePlaceDenominator x) +
      Real.log ‖((P N).map (eval₂RingHom (Int.castRingHom ℂ) (r : ℂ))).eval (lambertValue r : ℂ)‖ +
      ∑ σ ∈ s, lambertCircleLogBound (60*N) (3*N) (R σ) ‖σ x‖
  have hg (N : ℕ) : 0 ≤ g N := by
    have hl := integerBivariate_log_product_nonneg (P N) q x (D N) (60*N)
      (lambertCertificateIntegerPolynomial_natDegree_le _ _)
      (lambertCertificateIntegerPolynomial_coeff_natDegree_le _ _) (hy N)
    have hsum : (∑ σ : K →+* ℂ, Real.log ‖((P N).map
        (eval₂RingHom (Int.castRingHom ℂ) (σ q))).eval (σ x)‖) ≤
        Real.log ‖((P N).map (eval₂RingHom (Int.castRingHom ℂ) (r : ℂ))).eval (lambertValue r : ℂ)‖ +
          ∑ σ ∈ s, lambertCircleLogBound (60*N) (3*N) (R σ) ‖σ x‖ := by
      rw [← sum_erase_add _ _ (mem_univ σ₀), hq, hx, add_comm]
      apply add_le_add le_rfl
      apply sum_le_sum
      intro σ hσ
      have hn : 0 < ‖((P N).map (eval₂RingHom (Int.castRingHom ℂ) (σ q))).eval (σ x)‖ := by
        rw [← integerBivariate_eval_hom]
        exact norm_pos_iff.mpr ((_root_.map_ne_zero σ).mpr (hy N))
      exact (Real.log_le_iff_le_exp hn).mpr
        (lambertCircleLogBound_disk (R σ) (hR σ) (σ q) (σ x) (hRq σ) _ _)
    dsimp [g]
    push_cast at hl
    linarith
  have hi : Tendsto (fun N : ℕ => (1 : ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun N : ℕ => 60*(N : ℝ)/(N : ℝ)^3) atTop (𝓝 0) := by
    convert (hi.pow 2).const_mul 60 using 1
    · funext N; by_cases hn : (N : ℝ)=0
      · simp [hn]
      · field_simp
    · norm_num
  have hlim := ((((lambertMain_clearingDegree_tendsto).mul_const
    (Real.log (finitePlaceDenominator q))).add (hh.mul_const (Real.log (finitePlaceDenominator x)))).add
    (lambertMain_algebraic_log_tendsto r hr)).add
    (tendsto_finsetSum s (fun σ _ => lambertCircleLogBound_tendsto (R σ) ‖σ x‖))
  simp only [zero_mul, add_zero] at hlim
  have heq : C*Real.log (finitePlaceDenominator q)+(C-202140)*Real.log r+
      ∑ σ ∈ s, C*Real.log (R σ) =
      C*Height.logHeight₁ q-202140*Real.log r+(s.card : ℝ)*C*δ := by
    rw [numberField_logHeight_eq_embeddings, ← sum_erase_add _ _ (mem_univ σ₀), hq]
    have hn : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hr)]
    simp only [hn, max_eq_left hr.le, hlogR, mul_add, sum_add_distrib, sum_const, nsmul_eq_mul]
    rw [← mul_sum]
    dsimp [s]
    ring
  have hlim' : Tendsto (fun N : ℕ => g N/(N : ℝ)^3) atTop
      (𝓝 (C*Height.logHeight₁ q-202140*Real.log r+(s.card : ℝ)*C*δ)) := by
    rw [← heq]
    convert hlim using 1
    funext N
    dsimp [g, D, P, C]
    simp only [add_div, sum_div]
    ring
  have hnonneg := ge_of_tendsto hlim' (Filter.Eventually.of_forall
    (fun N => div_nonneg (hg N) (by positivity : (0 : ℝ) ≤ (N : ℝ)^3)))
  linarith
end
end Lambert
