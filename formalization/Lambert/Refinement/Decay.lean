import Lambert.Determinants.Decay
import Lambert.Refinement.Normalization

/-! # Real decay for the six-presentation Lambert family -/
namespace Lambert
noncomputable section
open Polynomial Finset Filter Topology

/-- The signed normalized determinant is strictly positive at the actual Lambert value. -/
theorem lambertRefinementNormalizedDeterminant_eval_pos (q : ℝ) (hq : 1 < q) (N : ℕ) :
    0 < (lambertRefinementNormalizedDeterminant q N).eval (lambertValue q) := by
  rw [lambertRefinementNormalizedDeterminant, eval_mul, eval_C]
  exact mul_pos (zpow_pos (zero_lt_one.trans hq) _)
    (lambertPoleDeterminant_eval_pos q hq (500*N) (27*N) (516*N) (41*N))

/-- Normalization shifts the exact logarithmic estimate by B log q and retains the uniform linear error. -/
theorem lambertRefinementNormalizedDeterminant_log_bounds (q : ℝ) (hq : 1 < q) (N : ℕ) :
    let K := (500*N : ℝ) * (500*N + 1) * (1000*N + 1) / 6 +
      41*N * (500*N) * (500*N + 1) / 2 +
      500*N * (516*N*(27*N)+516*N*(516*N-1)/2);
    ((lambertTranslatedInfinityExponent (500*N) (27*N) (16*N) (41*N) : ℝ) - K) * Real.log q +
        1000 * N * Real.log (geometricProductFloor q⁻¹) ≤
      Real.log ((lambertRefinementNormalizedDeterminant q N).eval (lambertValue q)) ∧
    Real.log ((lambertRefinementNormalizedDeterminant q N).eval (lambertValue q)) ≤
      ((lambertTranslatedInfinityExponent (500*N) (27*N) (16*N) (41*N) : ℝ) - K) * Real.log q -
        2000 * N * Real.log (geometricProductFloor q⁻¹) := by
  dsimp only
  rw [lambertRefinementNormalizedDeterminant, eval_mul, eval_C,
    Real.log_mul (zpow_ne_zero _ (zero_lt_one.trans hq).ne')
      (lambertPoleDeterminant_eval_pos q hq (500*N) (27*N) (516*N) (41*N)).ne', Real.log_zpow]
  have he := lambertPoleDeterminant_log_bounds q hq (500*N) (27*N) (516*N) (41*N)
  dsimp only at he
  push_cast at he
  constructor <;> nlinarith [he.1, he.2]


/-- The selected rectangular normalized determinant has cubic logarithmic coefficient -(371952500/3) log q. -/
theorem lambertRefinementFamily_determinant_log_tendsto (q : ℝ) (hq : 1 < q) :
    Tendsto (fun N : ℕ => Real.log ((lambertRefinementNormalizedDeterminant q N).eval
      (lambertValue q)) / (N : ℝ) ^ 3) atTop (𝓝 (-((371952500/3)) * Real.log q)) := by
  let G := Real.log (geometricProductFloor q⁻¹)
  have hi : Tendsto (fun N : ℕ => (1 : ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hl := (tendsto_const_nhds (x := -(371952500/3)*Real.log q)).add
    ((hi.pow 2).const_mul (-(250/3)*Real.log q+1000*G))
  have hu := (tendsto_const_nhds (x := -(371952500/3)*Real.log q)).add
    ((hi.pow 2).const_mul (-(250/3)*Real.log q-2000*G))
  simp only [zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] at hl hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have hb := (lambertRefinementNormalizedDeterminant_log_bounds q hq N).1
    rw [lambertRefinementFamily_infinity_exponent] at hb
    push_cast at hb
    apply (le_div_iff₀ (pow_pos hn 3)).mpr
    have he : (-(371952500/3)*Real.log q+((1 : ℝ)/N)^2*(-(250/3)*Real.log q+1000*G))*(N : ℝ)^3 =
        (-((371952500/3)*(N : ℝ)^3+(250/3)*N))*Real.log q+1000*N*G := by field_simp; ring
    rw [mul_comm (-(250/3)*Real.log q+1000*G), he]
    dsimp [G]
    nlinarith [hb]
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have hb := (lambertRefinementNormalizedDeterminant_log_bounds q hq N).2
    rw [lambertRefinementFamily_infinity_exponent] at hb
    push_cast at hb
    apply (div_le_iff₀ (pow_pos hn 3)).mpr
    have he : (-(371952500/3)*Real.log q+((1 : ℝ)/N)^2*(-(250/3)*Real.log q-2000*G))*(N : ℝ)^3 =
        (-((371952500/3)*(N : ℝ)^3+(250/3)*N))*Real.log q-2000*N*G := by field_simp; ring
    rw [mul_comm (-(250/3)*Real.log q-2000*G), he]
    dsimp [G]
    nlinarith [hb]

end
end Lambert
