import Lambert.Refinement.RationalRefinement

/-! # Irrationality from the six-presentation Lambert profile -/
namespace Lambert
open Polynomial

/-- The exact numerator-profile region gives irrational rational-base Lambert values. -/
theorem lambertValue_irrational_of_refinement_region
    (a b : ℤ) (hb : 0 < b) (hab : b < a)
    (hregion : Real.log b / Real.log a <
      1 - lambertRefinementArithmeticConstant / (371952500/3)) :
    Irrational (lambertValue ((a : ℝ)/b)) := by
  rintro ⟨r, hr⟩
  have hp := lambertValue_no_polynomial_relation_of_refinement_region a b hb hab 1
    (by simpa using hregion) (X-C r) (by compute_degree) (by simp [← hr])
  have hc := congrArg (fun p : ℚ[X] => p.coeff 1) hp
  simp at hc

/-- The logarithmic cutoff 0.573290 gives irrational rational-base Lambert values. -/
theorem lambertValue_irrational_of_certified_region
    (a b : ℤ) (hb : 0 < b) (hab : b < a)
    (hregion : Real.log b / Real.log a < (573290/1000000 : ℝ)) :
    Irrational (lambertValue ((a : ℝ)/b)) := by
  rintro ⟨r, hr⟩
  have hp := lambertValue_no_polynomial_relation_of_certified_region a b hb hab 1
    (by norm_num at hregion ⊢; exact hregion) (X-C r) (by compute_degree) (by simp [← hr])
  have hc := congrArg (fun p : ℚ[X] => p.coeff 1) hp
  simp at hc

end Lambert
