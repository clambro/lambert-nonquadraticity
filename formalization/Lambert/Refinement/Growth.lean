import Lambert.Refinement.Scale
import Lambert.Refinement.IntegerComplex

/-! # Cubic bounds for the six-presentation integer certificates -/
namespace Lambert
noncomputable section
open Polynomial Filter Topology

/-- The distinguished Lambert value has logarithmic majorant equal to the scale majorant plus the exact determinant logarithm. -/
def lambertRefinementSmallLogBound (a b : ℤ) (N : ℕ) : ℝ :=
  lambertRefinementScaleMajorant a b N+
    Real.log ((lambertRefinementNormalizedDeterminant ((a : ℝ)/b) N).eval (lambertValue ((a : ℝ)/b)))

/-- The distinguished integer-certificate logarithm is bounded by the scale majorant minus its determinant decay. -/
theorem lambertRefinementSmallLogBound_bound (a b : ℤ) (hb : 0<b) (hab : b<a) (N : ℕ) :
    Real.log ((lambertRefinementSpecializedIntegerPolynomial N a b).eval₂
      (Int.castRingHom ℝ) (lambertValue ((a : ℝ)/b))) ≤ lambertRefinementSmallLogBound a b N := by
  have hq : (1 : ℝ)<(a : ℝ)/b := (one_lt_div (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)
  have hqQ : (1 : ℚ)<(a : ℚ)/b := (one_lt_div (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)
  rw [eval₂_eq_eval_map, lambertRefinementSpecializedIntegerPolynomial_map_real N a b hb.ne' hqQ,
    eval_mul, eval_C, Real.log_mul (lambertRefinementIntegerScale_pos N a b hb hab).ne'
      (lambertRefinementNormalizedDeterminant_eval_pos _ hq N).ne']
  have he := lambertRefinementScaleMajorant_bound a b hb hab N
  dsimp [lambertRefinementSmallLogBound]
  linarith

/-- The distinguished logarithmic bound has cubic coefficient equal to arithmetic growth minus 371952500/3 times log of the base. -/
theorem lambertRefinementSmallLogBound_tendsto (a b : ℤ)
    (hb : 0<b) (hab : b<a) :
    Tendsto (fun N : ℕ => lambertRefinementSmallLogBound a b N/(N : ℝ)^3) atTop
      (𝓝 (lambertRefinementArithmeticConstant*Real.log a-(371952500/3)*Real.log ((a : ℝ)/b))) := by
  have hq : (1 : ℝ)<(a : ℝ)/b := (one_lt_div (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)
  have he := (lambertRefinementScaleMajorant_tendsto a b).add
    (lambertRefinementFamily_determinant_log_tendsto _ hq)
  convert he using 1
  · funext N
    rw [lambertRefinementSmallLogBound, add_div]
  · congr 1
    ring

/-- The complex certificate bound is the arithmetic scale majorant plus a quadratic window cost. -/
def lambertRefinementCertifiedComplexLogBound (a b : ℤ) (N : ℕ) (z : ℂ) : ℝ :=
  lambertRefinementScaleMajorant a b N+
    (516*(N : ℝ))^2+516*N*(1+‖z‖+1084*N*(((a : ℝ)/b)-1)⁻¹)-
      516*N*Real.log (geometricProductFloor (((a : ℝ)/b)⁻¹))

/-- The exponential of the certified complex majorant controls the integer polynomial at every complex argument. -/
theorem lambertRefinementCertifiedComplexLogBound_bound (a b : ℤ) (hb : 0<b) (hab : b<a)
    (N : ℕ) (z : ℂ) :
    ‖(lambertRefinementSpecializedIntegerPolynomial N a b).eval₂ (Int.castRingHom ℂ) z‖ ≤
      Real.exp (lambertRefinementCertifiedComplexLogBound a b N z) := by
  apply (lambertRefinementComplexLogBound_bound N a b hb hab z).trans
  apply Real.exp_le_exp.mpr
  have he := lambertRefinementScaleMajorant_bound a b hb hab N
  dsimp [lambertRefinementComplexLogBound, lambertRefinementCertifiedComplexLogBound]
  linarith

/-- The complex logarithmic majorant has the advertised arithmetic cubic coefficient at every fixed argument. -/
theorem lambertRefinementCertifiedComplexLogBound_tendsto
    (a b : ℤ) (z : ℂ) :
    Tendsto (fun N : ℕ => lambertRefinementCertifiedComplexLogBound a b N z/(N : ℝ)^3) atTop
      (𝓝 (lambertRefinementArithmeticConstant*Real.log a)) := by
  have hi : Tendsto (fun N : ℕ => (1 : ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have he := (lambertRefinementScaleMajorant_tendsto a b).add
    ((hi.const_mul (266256+559344*(((a : ℝ)/b)-1)⁻¹)).add
      ((hi.pow 2).const_mul (516*(1+‖z‖-Real.log (geometricProductFloor (((a : ℝ)/b)⁻¹))))))
  simp only [mul_zero,zero_pow (by decide : 2≠0),add_zero] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  dsimp [lambertRefinementCertifiedComplexLogBound]
  field_simp
  ring

end
end Lambert
