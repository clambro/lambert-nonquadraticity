import Lambert.Results.MainTheorem

/-! # Relative nonquadraticity at Pisot and Salem bases -/
namespace Lambert
noncomputable section
open Polynomial IntermediateField

/-- Every real algebraic integer greater than one whose other embeddings lie in the closed unit disk has no quadratic Lambert relation over its generated field. This includes Pisot and Salem bases. -/
theorem lambertValue_no_quadratic_relation_of_conjugates
    (q : ℝ) (hq : 1 < q) (hint : IsIntegral ℤ q)
    (hconj : ∀ σ : ℚ⟮q⟯ →+* ℂ,
      σ ≠ Complex.ofRealHom.comp (ℚ⟮q⟯).subtype → ‖σ (AdjoinSimple.gen ℚ q)‖ ≤ 1)
    (p : (ℚ⟮q⟯)[X]) (hp : p.natDegree ≤ 2)
    (hroot : p.eval₂ (ℚ⟮q⟯).subtype (lambertValue q)=0) : p=0 := by
  have hqalg : IsIntegral ℚ q := hint.tower_top
  let : FiniteDimensional ℚ ℚ⟮q⟯ := adjoin.finiteDimensional hqalg
  let : NumberField ℚ⟮q⟯ := {}
  let qK : ℚ⟮q⟯ := AdjoinSimple.gen ℚ q
  have hi : IsIntegral ℤ qK :=
    (isIntegral_algHom_iff ((ℚ⟮q⟯).val.restrictScalars ℤ) (ℚ⟮q⟯).val.injective).mp hint
  have hnorm : ‖(Complex.ofRealHom.comp (ℚ⟮q⟯).subtype) qK‖=q := by
    change ‖(q : ℂ)‖=q
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hq)]
  have hh := numberField_logHeight_eq_log_of_conjugates qK hi
    (Complex.ofRealHom.comp (ℚ⟮q⟯).subtype) (by rw [hnorm]; exact hq.le) hconj
  rw [hnorm] at hh
  apply lambertValue_no_relation_of_numberField_height ℚ⟮q⟯ qK hq
    2 ?_ p hp hroot
  rw [hh]
  exact mul_lt_mul_of_pos_right lambert_main_degree_two_margin (Real.log_pos hq)

/-- Every linear relation among one, the Lambert value, and its square over a Pisot or Salem base field has zero coefficients. -/
theorem lambertValue_quadratic_coefficients_eq_zero_of_conjugates
    (q : ℝ) (hq : 1 < q) (hint : IsIntegral ℤ q)
    (hconj : ∀ σ : ℚ⟮q⟯ →+* ℂ,
      σ ≠ Complex.ofRealHom.comp (ℚ⟮q⟯).subtype → ‖σ (AdjoinSimple.gen ℚ q)‖ ≤ 1)
    (a b c : ℚ⟮q⟯)
    (he : (a : ℝ)*lambertValue q^2+(b : ℝ)*lambertValue q+c=0) :
    a=0 ∧ b=0 ∧ c=0 := by
  have hp := lambertValue_no_quadratic_relation_of_conjugates q hq hint hconj
    (C a*X^2+C b*X+C c) (by compute_degree) (by simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]; exact he)
  have h0 := congrArg (fun p : (ℚ⟮q⟯)[X] => p.coeff 0) hp
  have h1 := congrArg (fun p : (ℚ⟮q⟯)[X] => p.coeff 1) hp
  have h2 := congrArg (fun p : (ℚ⟮q⟯)[X] => p.coeff 2) hp
  simpa using And.intro h2 (And.intro h1 h0)
end
end Lambert
