import Lambert.Results.RadicalBase

/-! # Integer-base nonquadraticity from the main radical criterion -/
namespace Lambert
noncomputable section
open Polynomial IntermediateField

/-- Integer-base nonquadraticity is a specialization of the main algebraic criterion. -/
theorem lambertValue_integer_no_quadratic_relation
    (q : ℤ) (hq : 2 ≤ q) (p : ℚ[X]) (hp : p.natDegree ≤ 2)
    (hroot : p.eval₂ (Rat.castHom ℝ) (lambertValue (q : ℝ)) = 0) : p = 0 := by
  let K := ℚ⟮(q : ℝ)⟯
  let pK : K[X] := p.map (algebraMap ℚ K)
  have hqR : 1 < (q : ℝ) := by exact_mod_cast (show (1 : ℤ) < q by omega)
  have hpow : (q : ℝ)^1 = (q.toNat : ℝ) := by
    rw [pow_one]
    exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ q)).symm
  have heval : pK.eval₂ K.subtype (lambertValue (q : ℝ)) = 0 := by
    have hc : K.subtype.comp (algebraMap ℚ K) = Rat.castHom ℝ := Subsingleton.elim _ _
    simpa only [pK, eval₂_map, hc] using hroot
  have hz := lambertValue_no_relation_of_radical_margin (q : ℝ) hqR 1 q.toNat
    (by norm_num) hpow 2 (by simpa using lambert_main_degree_two_margin)
    pK (by simpa [pK] using hp) heval
  exact (Polynomial.map_injective (f := algebraMap ℚ K) (algebraMap ℚ K).injective)
    (by simpa only [pK, Polynomial.map_zero] using hz)

/-- The Erdős-Borwein constant has no nonzero rational relation of degree at most two. -/
theorem erdosBorwein_no_quadratic_relation
    (p : ℚ[X]) (hp : p.natDegree ≤ 2)
    (hroot : p.eval₂ (Rat.castHom ℝ) (lambertValue 2) = 0) : p = 0 :=
  lambertValue_integer_no_quadratic_relation 2 (by norm_num) p hp (by simpa using hroot)

end
end Lambert
