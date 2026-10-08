import Lambert.Refinement.Growth
import Lambert.Arithmetic.PolynomialDegreeCriterion

/-! # Degree exclusion from the certified six-presentation Lambert profile -/
namespace Lambert
noncomputable section
open Polynomial Filter Topology

private theorem cast_eval (p : ℤ[X]) (x : ℝ) :
    p.eval₂ (Int.castRingHom ℂ) (x : ℂ) = (p.eval₂ (Int.castRingHom ℝ) x : ℝ) := by
  have he := hom_eval₂ p (Int.castRingHom ℝ) Complex.ofRealHom x
  have hc : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by ext; simp
  rw [hc] at he
  exact he.symm

/-- A positive degree-weighted certified numerator-profile margin excludes algebraic degrees up to the specified natural number for the Lambert value. -/
theorem lambertValue_algebraic_degree_gt_of_refinement_margin
    (a b : ℤ) (hb : 0 < b) (hab : b < a) (e : ℕ)
    (hmargin : e * lambertRefinementArithmeticConstant * Real.log a <
      ((371952500/3))*Real.log ((a : ℝ)/b))
    (halg : IsAlgebraic ℚ (lambertValue ((a : ℝ)/b) : ℂ)) :
    e < (minpoly ℚ (lambertValue ((a : ℝ)/b) : ℂ)).natDegree := by
  by_cases he : e=0
  · subst e
    exact minpoly.natDegree_pos halg.isIntegral
  have he : 0 < e := Nat.pos_of_ne_zero he
  let P := fun N => lambertRefinementSpecializedIntegerPolynomial N a b
  let x := lambertValue ((a : ℝ)/b)
  let B : ℝ := lambertRefinementArithmeticConstant*Real.log a
  let A : ℝ := B - ((371952500/3))*Real.log ((a : ℝ)/b)
  have hp (N : ℕ) : 0 < (P N).eval₂ (Int.castRingHom ℝ) x :=
    lambertRefinementSpecializedIntegerPolynomial_eval_pos _ a b hb hab
  have hn (N : ℕ) : (P N).eval₂ (Int.castRingHom ℂ) (x : ℂ) ≠ 0 := by
    rw [cast_eval]
    exact_mod_cast (hp N).ne'
  have hnorm (N : ℕ) : ‖(P N).eval₂ (Int.castRingHom ℂ) (x : ℂ)‖ =
      (P N).eval₂ (Int.castRingHom ℝ) x := by
    rw [cast_eval, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hp N)]
  apply algebraic_degree_gt_of_cubic_bounds P (fun N => 500*N)
    (fun N => lambertRefinementSpecializedIntegerPolynomial_natDegree_le _ a b)
    (by
      have hi : Tendsto (fun n : ℕ => (1 : ℝ)/n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      convert (hi.pow 2).const_mul 500 using 1
      · funext n; push_cast; by_cases hn : (n : ℝ) = 0
        · simp [hn]
        · field_simp
      · norm_num)
    (x : ℂ) hn A B
    (by
      have ha : (1 : ℝ) ≤ a := by exact_mod_cast (show (1 : ℤ) ≤ a by omega)
      dsimp [B]
      exact mul_nonneg (by unfold lambertRefinementArithmeticConstant; positivity) (Real.log_nonneg ha))
    (lambertRefinementSmallLogBound a b)
    (by intro N; rw [hnorm]; exact lambertRefinementSmallLogBound_bound a b hb hab N)
    (lambertRefinementSmallLogBound_tendsto a b hb hab)
    (lambertRefinementCertifiedComplexLogBound a b)
    (lambertRefinementCertifiedComplexLogBound_bound a b hb hab)
    (lambertRefinementCertifiedComplexLogBound_tendsto a b) e ?_ halg
  have heR : ((e - 1 : ℕ) : ℝ) = (e : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [heR]
  have hx : A + ((e : ℝ)-1)*B =
      (e * lambertRefinementArithmeticConstant * Real.log a -
        ((371952500/3))*Real.log ((a : ℝ)/b)) := by dsimp [A, B]; ring
  rw [hx]
  exact sub_neg.mpr hmargin

/-- Under the degree-weighted certified numerator-profile margin, no nonzero rational polynomial of the indicated degree or less vanishes at the Lambert value. -/
theorem lambertValue_no_polynomial_relation_of_refinement_margin
    (a b : ℤ) (hb : 0 < b) (hab : b < a) (e : ℕ)
    (hmargin : e * lambertRefinementArithmeticConstant * Real.log a <
      ((371952500/3))*Real.log ((a : ℝ)/b))
    (p : ℚ[X]) (hp : p.natDegree ≤ e)
    (hroot : p.eval₂ (Rat.castHom ℝ) (lambertValue ((a : ℝ)/b)) = 0) : p = 0 := by
  by_contra hp0
  let x := lambertValue ((a : ℝ)/b)
  have hx : p.eval₂ (Rat.castHom ℂ) (x : ℂ) = 0 := by
    have hr := hom_eval₂ p (Rat.castHom ℝ) Complex.ofRealHom x
    have hc : Complex.ofRealHom.comp (Rat.castHom ℝ) = Rat.castHom ℂ := by ext; simp
    rw [hc, hroot, map_zero] at hr
    exact hr.symm
  have halg : IsAlgebraic ℚ (x : ℂ) := ⟨p, hp0, hx⟩
  have hd := lambertValue_algebraic_degree_gt_of_refinement_margin a b hb hab e hmargin halg
  have hle : (minpoly ℚ (x : ℂ)).natDegree ≤ p.natDegree :=
    natDegree_le_of_dvd (minpoly.dvd ℚ (x : ℂ) hx) hp0
  exact (not_lt_of_ge (hle.trans hp)) hd

/-- The certified degree-weighted logarithmic region excludes every nonzero rational polynomial relation of the prescribed degree or less for a rational-base Lambert value. -/
theorem lambertValue_no_polynomial_relation_of_refinement_region
    (a b : ℤ) (hb : 0 < b) (hab : b < a) (e : ℕ)
    (hregion : Real.log b / Real.log a <
      1 - e * lambertRefinementArithmeticConstant / ((371952500/3)))
    (p : ℚ[X]) (hp : p.natDegree ≤ e)
    (hroot : p.eval₂ (Rat.castHom ℝ) (lambertValue ((a : ℝ)/b)) = 0) : p = 0 := by
  have ha1 : (1 : ℝ) < a := by exact_mod_cast (show (1 : ℤ) < a by omega)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hr := (div_lt_iff₀ (Real.log_pos ha1)).mp hregion
  apply lambertValue_no_polynomial_relation_of_refinement_margin a b hb hab e ?_ p hp hroot
  rw [Real.log_div (zero_lt_one.trans ha1).ne' hbR.ne']
  have hid : (1 - (e : ℝ) * lambertRefinementArithmeticConstant / ((371952500/3))) *
      Real.log a = Real.log a - (1/(371952500/3)) *
        ((e : ℝ) * lambertRefinementArithmeticConstant * Real.log a) := by ring
  rw [hid] at hr
  linarith




/-- The explicit decimal cutoff excludes rational polynomial relations through every degree allowed by its degree-weighted region. -/
theorem lambertValue_no_polynomial_relation_of_certified_region
    (a b : ℤ) (hb : 0<b) (hab : b<a) (e : ℕ)
    (hregion : Real.log b/Real.log a < 1-e*(426710/1000000 : ℝ))
    (p : ℚ[X]) (hp : p.natDegree≤e)
    (hroot : p.eval₂ (Rat.castHom ℝ) (lambertValue ((a : ℝ)/b))=0) : p=0 := by
  apply lambertValue_no_polynomial_relation_of_refinement_region a b hb hab e _ p hp hroot
  have he := mul_le_mul_of_nonneg_left lambertRefinement_cutoff.le (Nat.cast_nonneg e : (0 : ℝ)≤e)
  rw [← mul_div_assoc] at he
  linarith

end
end Lambert
