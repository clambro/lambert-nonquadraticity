import Lambert.Arithmetic.NumberFieldPolynomialHeight
import Lambert.Arithmetic.NumberFieldRootHeight

/-!
# Heights and Mahler measure

The height–Mahler identity uses the unnormalized number-field height, so the
ambient field degree is retained explicitly. Compare Bombieri–Gubler,
*Heights in Diophantine Geometry* (2006), Proposition 1.6.6.
-/
namespace Lambert
noncomputable section
open Polynomial NumberField

/-- A root of a primitive irreducible integer polynomial has height determined by its Mahler measure and the exact ambient field-degree factor. -/
theorem numberField_logHeight_eq_mahler {K : Type} [Field K] [NumberField K]
    (x : K) (p : ℤ[X]) (hp : p.IsPrimitive)
    (hirr : Irreducible (p.map (Int.castRingHom ℚ)))
    (hroot : p.eval₂ (Int.castRingHom K) x=0) :
    (p.natDegree : ℝ)*Height.logHeight₁ x =
      (Module.finrank ℚ K : ℝ)*(p.map (Int.castRingHom ℂ)).logMahlerMeasure := by
  classical
  let E := (p.map (Int.castRingHom K)).SplittingField
  let : NumberField E := NumberField.of_module_finite K E
  have hc : (algebraMap K E).comp (Int.castRingHom K)=Int.castRingHom E := Subsingleton.elim _ _
  have hs : (p.map (Int.castRingHom E)).Splits := by
    have he := SplittingField.splits (p.map (Int.castRingHom K))
    rwa [Polynomial.map_map,hc] at he
  have hxe : p.eval₂ (Int.castRingHom E) (algebraMap K E x)=0 := by
    have he := congrArg (algebraMap K E) hroot
    rwa [map_zero, hom_eval₂, hc] at he
  have hq (z : E) (hz : p.eval₂ (Int.castRingHom E) z=0) :
      (p.map (Int.castRingHom ℚ)).eval₂ (algebraMap ℚ E) z=0 := by
    rw [eval₂_map]
    have he : (algebraMap ℚ E).comp (Int.castRingHom ℚ)=Int.castRingHom E := Subsingleton.elim _ _
    rwa [he]
  have hall : ∀ z ∈ (p.map (Int.castRingHom E)).roots,
      Height.logHeight₁ z=Height.logHeight₁ (algebraMap K E x) := by
    intro z hz
    apply numberField_logHeight_eq_of_irreducible_roots _ hirr z _ (hq z ?_) (hq _ hxe)
    simpa only [IsRoot, eval_map] using isRoot_of_mem_roots hz
  have hsum := primitive_split_sum_logHeight p hp hs
  have heq : ((p.map (Int.castRingHom E)).roots.map Height.logHeight₁).sum =
      (p.natDegree : ℝ)*Height.logHeight₁ (algebraMap K E x) := by
    rw [Multiset.map_congr rfl hall]
    simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
      ← hs.natDegree_eq_card_roots,
      natDegree_map_eq_of_injective (f := Int.castRingHom E) Int.cast_injective]
  rw [heq, numberField_logHeight_extension] at hsum
  have ht : (Module.finrank ℚ K : ℝ)*(Module.finrank K E : ℝ)=Module.finrank ℚ E := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K E
  rw [← ht] at hsum
  apply mul_left_cancel₀ (show (Module.finrank K E : ℝ)≠0 by
    exact_mod_cast (Module.finrank_pos (R := K) (M := E)).ne')
  calc
    _ = (p.natDegree : ℝ)*((Module.finrank K E : ℝ)*Height.logHeight₁ x) := by ring
    _ = ((Module.finrank ℚ K : ℝ)*(Module.finrank K E : ℝ))*
        (p.map (Int.castRingHom ℂ)).logMahlerMeasure := hsum
    _ = _ := by ring

end
end Lambert
