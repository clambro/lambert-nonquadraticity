import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Lambert.Refinement.Normalization
import Lambert.Determinants.Specialization

/-!
# Specialization of the signed normalized determinant
-/
namespace Lambert
noncomputable section
open Polynomial

/-- Signed normalization commutes with embeddings of coefficient fields. -/
theorem lambertRefinementNormalizedDeterminant_map {K F : Type*} [Field K] [Field F]
    (f : K →+* F) (q : K) (N : ℕ) :
    (lambertRefinementNormalizedDeterminant q N).map f = lambertRefinementNormalizedDeterminant (f q) N := by
  simp only [lambertRefinementNormalizedDeterminant, Polynomial.map_mul, Polynomial.map_C,
    map_zpow₀, lambertPoleDeterminant_map]

/-- At a base with distinct powers, normalized coefficients specialize to the actual determinant. -/
theorem lambertRefinementNormalizedDeterminant_coeff_specialize_of_pow_injective
    {K : Type} [Field K] [CharZero K] (q : K)
    (hq : Function.Injective (fun n : ℕ => q^n)) (N i : ℕ) :
    RatFunc.eval (Rat.castHom K) q
      ((lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N).coeff i) =
      (lambertRefinementNormalizedDeterminant q N).coeff i := by
  have hq0 : q ≠ 0 := by
    intro hz
    have he := hq (show q^1=q^2 by simp [hz])
    omega
  have hp := ratFunc_X_zpow_regular₂ (Rat.castHom K) q hq0
    (lambertTranslatedInfinityExponent (500*N) (27*N) (16*N) (41*N))
  have hf := lambertPoleDeterminant_coeff_regular q hq (500*N) (27*N) (16*N) (41*N) i
  simp only [show 500*N+16*N=516*N by omega] at hf
  rw [lambertRefinementNormalizedDeterminant_coeff, lambertRefinementNormalizedDeterminant_coeff,
    RatFunc.eval_mul (Rat.castHom K) q hp hf, ratFunc_X_zpow_eval₂ _ q hq0]
  congr 1
  simpa only [show 500*N+16*N=516*N by omega] using
    lambertPoleDeterminant_coeff_specialize_of_pow_injective q hq (500*N) (27*N) (16*N) (41*N) i

/-- Specialization of normalized coefficients at a rational base greater than one gives the actual determinant. -/
theorem lambertRefinementNormalizedDeterminant_coeff_specialize (q : ℚ) (hq : 1 < q) (N i : ℕ) :
    RatFunc.eval (RingHom.id ℚ) q
      ((lambertRefinementNormalizedDeterminant (RatFunc.X : RatFunc ℚ) N).coeff i) =
      (lambertRefinementNormalizedDeterminant q N).coeff i := by
  have hf : Rat.castHom ℚ = RingHom.id ℚ := Subsingleton.elim _ _
  simpa only [hf] using
    lambertRefinementNormalizedDeterminant_coeff_specialize_of_pow_injective q
      (pow_right_strictMono₀ hq).injective N i

end
end Lambert
