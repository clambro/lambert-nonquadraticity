import Lambert.Arithmetic.BivariateProductFormula

/-! # Height bounds from integrality and conjugate control -/
namespace Lambert
noncomputable section
open NumberField Finset

/-- Algebraic integers have finite-place denominator product one. -/
theorem finitePlaceDenominator_eq_one_of_isIntegral {K : Type*} [Field K] [NumberField K]
    (x : K) (hx : IsIntegral ℤ x) : finitePlaceDenominator x=1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro v
  have he := FinitePlace.norm_le_one K v.maximalIdeal (⟨x, hx⟩ : 𝓞 K)
  have hv : v x ≤ 1 := by
    rw [FinitePlace.norm_embedding_eq] at he
    exact he
  exact max_eq_right hv

/-- Sums of real-valued functions of complex embeddings multiply by the extension degree on elements of the base number field. -/
theorem numberField_sum_embeddings_extension {K L : Type} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] (x : K) (f : ℂ → ℝ) :
    (∑ σ : L →+* ℂ, f (σ (algebraMap K L x))) =
      (Module.finrank K L : ℝ) * ∑ σ : K →+* ℂ, f (σ x) := by
  classical
  let : FiniteDimensional K L := FiniteDimensional.right ℚ K L
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom L ℂ)
    (fun σ => f (σ (algebraMap K L x))) (fun σ => f (σ (algebraMap K L x)))
    (fun _ => rfl)]
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ)
    (fun σ => f (σ x)) (fun σ => f (σ x)) (fun _ => rfl)]
  rw [Fintype.sum_equiv algHomEquivSigma (fun σ : L →ₐ[ℚ] ℂ => _) (fun σ => f (σ.1 x)),
    ← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    let : Algebra K ℂ := σ.toRingHom.toAlgebra
    simp_rw [Finset.sum_const, Finset.card_univ, ← AlgHom.card K L ℂ, nsmul_eq_mul]
  · intro σ
    simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.domRestrict, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']

/-- An algebraic integer with a single embedding outside the unit disk has height equal to the logarithm of that embedding's modulus. -/
theorem numberField_logHeight_eq_log_of_conjugates {K : Type*} [Field K] [NumberField K]
    (x : K) (hx : IsIntegral ℤ x) (σ₀ : K →+* ℂ) (hσ₀ : 1 ≤ ‖σ₀ x‖)
    (hother : ∀ σ : K →+* ℂ, σ ≠ σ₀ → ‖σ x‖ ≤ 1) :
    Height.logHeight₁ x=Real.log ‖σ₀ x‖ := by
  classical
  rw [numberField_logHeight_eq_embeddings, finitePlaceDenominator_eq_one_of_isIntegral x hx,
    Real.log_one, zero_add]
  rw [sum_eq_single σ₀]
  · rw [max_eq_left hσ₀]
  · intro σ _ hσ
    rw [max_eq_right (hother σ hσ), Real.log_one]
  · simp
end
end Lambert
