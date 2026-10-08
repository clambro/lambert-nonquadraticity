import Lambert.Refinement.IntegerScale
import Lambert.Refinement.Decay
import Lambert.Arithmetic.HomogeneousCyclotomicReal

/-!
# Real evaluation of the exact Lambert integer polynomials
-/
namespace Lambert
noncomputable section
open Polynomial Finset

/-- The exact shifted-window integer scale is positive at positive ordered integer coordinates. -/
theorem lambertRefinementIntegerScale_pos (N : ℕ) (a b : ℤ) (hb : 0 < b) (hab : b < a) :
    0 < (lambertRefinementIntegerScale N a b : ℝ) := by
  simp only [lambertRefinementIntegerScale, Int.cast_mul, Int.cast_pow, Int.cast_prod]
  apply mul_pos (pow_pos (by exact_mod_cast hb.trans hab) _)
  exact prod_pos (fun n _ => pow_pos (homogeneousCyclotomicValue_pos n a b hb hab) _)

/-- Mapping the constructed integer polynomial to the reals gives precisely the
shifted-window determinant multiplied by its prescribed integer scale. -/
theorem lambertRefinementSpecializedIntegerPolynomial_map_real (N : ℕ) (a b : ℤ)
    (hb : b ≠ 0) (hq : (1 : ℚ) < (a : ℚ) / b) :
    (lambertRefinementSpecializedIntegerPolynomial N a b).map (Int.castRingHom ℝ) =
      C (lambertRefinementIntegerScale N a b : ℝ) *
        lambertRefinementNormalizedDeterminant ((a : ℝ) / b) N := by
  simpa only [Polynomial.map_mul, Polynomial.map_C, lambertRefinementNormalizedDeterminant_map,
    Polynomial.map_map, RingHom.eq_intCast', map_intCast, Polynomial.map_intCast, map_div₀]
    using congrArg (Polynomial.map (Rat.castHom ℝ))
      (lambertRefinementSpecializedIntegerPolynomial_map N a b hb hq)

/-- The integer polynomial has a strictly positive value at the actual Lambert series. -/
theorem lambertRefinementSpecializedIntegerPolynomial_eval_pos (N : ℕ) (a b : ℤ)
    (hb : 0 < b) (hab : b < a) :
    0 < (lambertRefinementSpecializedIntegerPolynomial N a b).eval₂
      (Int.castRingHom ℝ) (lambertValue ((a : ℝ) / b)) := by
  have hb0 := ne_of_gt hb
  have hqr : (1 : ℚ) < (a : ℚ) / b := (one_lt_div (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)
  have hq : (1 : ℝ) < (a : ℝ) / b := (one_lt_div (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)
  rw [eval₂_eq_eval_map, lambertRefinementSpecializedIntegerPolynomial_map_real N a b hb0 hqr,
    eval_mul, eval_C]
  exact mul_pos (lambertRefinementIntegerScale_pos N a b hb hab)
    (lambertRefinementNormalizedDeterminant_eval_pos _ hq N)



end
end Lambert
