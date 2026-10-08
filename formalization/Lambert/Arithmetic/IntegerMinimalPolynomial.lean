import Mathlib.Tactic

/-! # Integer representatives of rational minimal polynomials -/
namespace Lambert
noncomputable section
open Polynomial

/-- Every algebraic complex number has an integer polynomial of its exact algebraic degree that remains irreducible over the rationals and vanishes at that number. -/
theorem exists_integer_minimal_polynomial (α : ℂ) (hα : IsAlgebraic ℚ α) :
    ∃ f : ℤ[X], Irreducible (f.map (Int.castRingHom ℚ)) ∧
      f.natDegree = (minpoly ℚ α).natDegree ∧ f.eval₂ (Int.castRingHom ℂ) α = 0 := by
  let f := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ α)
  obtain ⟨b, hb, he⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (minpoly ℚ α)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hm : f.map (Int.castRingHom ℚ) = C (b : ℚ) * minpoly ℚ α := by
    rw [C_mul']
    rw [← IsScalarTower.algebraMap_smul ℚ b, algebraMap_int_eq] at he
    exact he
  have hirr : Irreducible (f.map (Int.castRingHom ℚ)) := by
    rw [hm]
    exact (irreducible_isUnit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hbQ))).mpr
      (minpoly.irreducible hα.isIntegral)
  refine ⟨f, hirr, ?_, ?_⟩
  · rw [← natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective) f,
      hm, natDegree_C_mul hbQ]
  · exact IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ)
      (minpoly ℚ α) (minpoly.aeval ℚ α)

end
end Lambert
