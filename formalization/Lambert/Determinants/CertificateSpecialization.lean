import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Lambert.Determinants.Normalization
import Lambert.Determinants.Specialization

/-!
# Specialization of the signed normalized determinant
-/
namespace Lambert
noncomputable section
open Polynomial

/-- Signed normalization commutes with embeddings of coefficient fields. -/
theorem lambertNormalizedDeterminant_map {K F : Type*} [Field K] [Field F]
    (f : K →+* F) (q : K) (h k : ℕ) :
    (lambertNormalizedDeterminant q h k).map f = lambertNormalizedDeterminant (f q) h k := by
  simp only [lambertNormalizedDeterminant, Polynomial.map_mul, Polynomial.map_C,
    map_zpow₀, lambertPoleDeterminant_map]

/-- At a base with distinct powers, normalized coefficients specialize to the actual determinant. -/
theorem lambertNormalizedDeterminant_coeff_specialize_of_pow_injective
    {K : Type} [Field K] [CharZero K] (q : K)
    (hq : Function.Injective (fun n : ℕ => q^n)) (h k i : ℕ) :
    RatFunc.eval (Rat.castHom K) q
      ((lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k).coeff i) =
      (lambertNormalizedDeterminant q h k).coeff i := by
  have hq0 : q ≠ 0 := by
    intro hz
    have he := hq (show q^1=q^2 by simp [hz])
    omega
  have hp := ratFunc_X_zpow_regular₂ (Rat.castHom K) q hq0
    (lambertTranslatedInfinityExponent h k 0 k)
  have hf := lambertPoleDeterminant_coeff_regular q hq h k 0 k i
  simp only [Nat.add_zero] at hf
  rw [lambertNormalizedDeterminant_coeff, lambertNormalizedDeterminant_coeff,
    RatFunc.eval_mul (Rat.castHom K) q hp hf, ratFunc_X_zpow_eval₂ _ q hq0]
  congr 1
  simpa only [Nat.add_zero] using
    lambertPoleDeterminant_coeff_specialize_of_pow_injective q hq h k 0 k i

/-- Normalized coefficients are regular at every nonzero base with distinct powers. -/
theorem lambertNormalizedDeterminant_coeff_regular
    {K : Type} [Field K] [CharZero K] (q : K)
    (hq : Function.Injective (fun n : ℕ => q^n)) (h k i : ℕ) :
    (lambertNormalizedDeterminant (RatFunc.X : RatFunc ℚ) h k).coeff i ∈
      ratFuncRegularAt₂ (Rat.castHom K) q := by
  have hq0 : q ≠ 0 := by
    intro hz
    have he := hq (show q^1=q^2 by simp [hz])
    omega
  rw [lambertNormalizedDeterminant_coeff]
  exact (ratFuncRegularAt₂ (Rat.castHom K) q).mul_mem
    (ratFunc_X_zpow_regular₂ _ q hq0 _)
    (by simpa using lambertPoleDeterminant_coeff_regular q hq h k 0 k i)

end
end Lambert
