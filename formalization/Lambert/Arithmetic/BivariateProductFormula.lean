import Lambert.Arithmetic.BivariateFinitePlace
import Mathlib.NumberTheory.Height.NumberField

/-! # Product-formula lower bounds for bivariate integer certificates -/
namespace Lambert
noncomputable section
open Polynomial Finset NumberField
open scoped BigOperators

/-- Integer bivariate polynomial evaluation commutes with field embeddings. -/
theorem integerBivariate_eval_hom {K L : Type*} [Field K] [Field L]
    (σ : K →+* L) (p : (ℤ[X])[X]) (q x : K) :
    σ ((p.map (eval₂RingHom (Int.castRingHom K) q)).eval x) =
      (p.map (eval₂RingHom (Int.castRingHom L) (σ q))).eval (σ x) := by
  simp only [eval_map]
  rw [hom_eval₂]
  congr 1
  ext a <;> simp

/-- The complex embedding product, multiplied by all finite places, equals one for a nonzero number-field element. -/
theorem numberField_embedding_product_formula {K : Type*} [Field K] [NumberField K]
    (x : K) (hx : x ≠ 0) :
    (∏ σ : K →+* ℂ, ‖σ x‖) * (∏ᶠ v : FinitePlace K, v x) = 1 := by
  have he : (∏ σ : K →+* ℂ, ‖σ x‖) = |(Algebra.norm ℚ x : ℝ)| := by
    have hn := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
    rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖)
      (fun φ => ‖φ x‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at hn
    simpa only [eq_ratCast, Complex.norm_ratCast, Rat.cast_abs] using hn.symm
  rw [he, FinitePlace.prod_eq_inv_abs_norm hx]
  rw [Rat.cast_inv, Rat.cast_abs]
  exact mul_inv_cancel₀ (abs_ne_zero.mpr (by
    exact_mod_cast ((Algebra.norm_ne_zero_iff (R := ℚ)).mpr hx : Algebra.norm ℚ x ≠ 0)))

/-- The logarithmic height of a number-field element is the finite denominator cost plus the sum over complex embeddings. -/
theorem numberField_logHeight_eq_embeddings {K : Type*} [Field K] [NumberField K] (q : K) :
    Height.logHeight₁ q = Real.log (finitePlaceDenominator q) +
      ∑ σ : K →+* ℂ, Real.log (max ‖σ q‖ 1) := by
  classical
  have he : (∑ σ : K →+* ℂ, Real.log (max ‖σ q‖ 1)) =
      ∑ v : InfinitePlace K, v.mult * Real.log (max (v q) 1) := by
    rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk
      (fun σ : K →+* ℂ => Real.log (max ‖σ q‖ 1))]
    apply sum_congr rfl
    intro v hv
    have hh (σ : K →+* ℂ) (hσ : σ ∈ ({σ | InfinitePlace.mk σ=v} : Finset _)) :
        Real.log (max ‖σ q‖ 1) = Real.log (max (v q) 1) := by
      rw [← (mem_filter.mp hσ).2, InfinitePlace.apply]
    simp_rw [sum_congr rfl hh, sum_const, nsmul_eq_mul, InfinitePlace.card_filter_mk_eq]
  rw [he, NumberField.logHeight₁_eq, finitePlaceDenominator,
    Real.log_finprod (fun _ => lt_of_lt_of_le zero_lt_one (le_max_right _ _))]
  simp only [Real.posLog_eq_log_max_one (apply_nonneg _ _), max_comm]
  ring

/-- A nonzero integer bivariate evaluation has nonnegative total logarithmic norm after the exact separate denominator costs are added. -/
theorem integerBivariate_log_product_nonneg {K : Type*} [Field K] [NumberField K]
    (p : (ℤ[X])[X]) (q x : K) (D h : ℕ) (hh : p.natDegree ≤ h)
    (hD : ∀ i, (p.coeff i).natDegree ≤ D)
    (hn : ((p.map (eval₂RingHom (Int.castRingHom K) q)).eval x) ≠ 0) :
    0 ≤ (D : ℝ)*Real.log (finitePlaceDenominator q) +
      h*Real.log (finitePlaceDenominator x) +
      ∑ σ : K →+* ℂ, Real.log ‖(p.map (eval₂RingHom (Int.castRingHom ℂ) (σ q))).eval (σ x)‖ := by
  let y := (p.map (eval₂RingHom (Int.castRingHom K) q)).eval x
  have hq := lt_of_lt_of_le zero_lt_one (one_le_finitePlaceDenominator q)
  have hx := lt_of_lt_of_le zero_lt_one (one_le_finitePlaceDenominator x)
  have hy (σ : K →+* ℂ) : 0 < ‖σ y‖ := norm_pos_iff.mpr ((_root_.map_ne_zero σ).mpr hn)
  have hp : 1 ≤ (∏ σ : K →+* ℂ, ‖σ y‖) *
      (finitePlaceDenominator q ^ D * finitePlaceDenominator x ^ h) := by
    rw [← numberField_embedding_product_formula y hn]
    exact mul_le_mul_of_nonneg_left (integerBivariate_finitePlace_product_bound p q x D h hh hD hn)
      (prod_nonneg (fun _ _ => norm_nonneg _))
  have hl := Real.log_nonneg hp
  rw [Real.log_mul (prod_pos (fun σ _ => hy σ)).ne'
      (mul_pos (pow_pos hq _) (pow_pos hx _)).ne', Real.log_prod (fun σ _ => (hy σ).ne'),
    Real.log_mul (pow_pos hq _).ne' (pow_pos hx _).ne', Real.log_pow, Real.log_pow] at hl
  simp only [y, integerBivariate_eval_hom] at hl
  linarith
end
end Lambert
