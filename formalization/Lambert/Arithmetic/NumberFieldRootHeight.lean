import Lambert.Arithmetic.NumberFieldHeightExtension

/-! # Heights of conjugate algebraic numbers -/
namespace Lambert
noncomputable section
open Polynomial NumberField

/-- Roots of the same irreducible rational polynomial have equal logarithmic heights after normalization by the ambient field degree. -/
theorem numberField_logHeight_conjugate {K L : Type} [Field K] [Field L]
    [NumberField K] [NumberField L] (p : ℚ[X]) (hp : Irreducible p)
    (x : K) (y : L) (hx : p.eval₂ (algebraMap ℚ K) x=0)
    (hy : p.eval₂ (algebraMap ℚ L) y=0) :
    (Module.finrank ℚ L : ℝ)*Height.logHeight₁ x =
      (Module.finrank ℚ K : ℝ)*Height.logHeight₁ y := by
  let : Fact (Irreducible p) := ⟨hp⟩
  let A := AdjoinRoot p
  have hd : Module.finrank ℚ A=p.natDegree := by
    exact (AdjoinRoot.powerBasis hp.ne_zero).finrank
  have hroot (F : Type) [Field F] [NumberField F] (z : F)
      (hz : p.eval₂ (algebraMap ℚ F) z=0) :
      (p.natDegree : ℝ)*Height.logHeight₁ z =
        (Module.finrank ℚ F : ℝ)*Height.logHeight₁ (AdjoinRoot.root p) := by
    let φ : A →ₐ[ℚ] F := AdjoinRoot.liftAlgHom p (Algebra.ofId ℚ F) z hz
    let : Algebra A F := φ.toRingHom.toAlgebra
    have he := numberField_logHeight_extension (K := A) (L := F) (AdjoinRoot.root p)
    have hgen : algebraMap A F (AdjoinRoot.root p)=z := AdjoinRoot.liftAlgHom_root _ _ _ _
    rw [hgen] at he
    have ht := Module.finrank_mul_finrank ℚ A F
    rw [hd] at ht
    have htR : (p.natDegree : ℝ)*(Module.finrank A F : ℝ)=Module.finrank ℚ F := by exact_mod_cast ht
    rw [he, ← mul_assoc, htR]
  have hk := hroot K x hx
  have hl := hroot L y hy
  have hdpos : (0 : ℝ)<p.natDegree := by exact_mod_cast hp.natDegree_pos
  nlinarith [hk,hl]

/-- Conjugate roots inside one number field have the same unnormalized logarithmic height. -/
theorem numberField_logHeight_eq_of_irreducible_roots {K : Type} [Field K] [NumberField K]
    (p : ℚ[X]) (hp : Irreducible p) (x y : K)
    (hx : p.eval₂ (algebraMap ℚ K) x=0) (hy : p.eval₂ (algebraMap ℚ K) y=0) :
    Height.logHeight₁ x=Height.logHeight₁ y := by
  have he := numberField_logHeight_conjugate p hp x y hx hy
  exact mul_left_cancel₀ (by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne') he

end
end Lambert
