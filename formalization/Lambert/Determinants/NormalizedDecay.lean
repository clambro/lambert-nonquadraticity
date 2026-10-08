import Lambert.Determinants.Decay
import Lambert.Determinants.Exponents

/-! # Real decay of signed normalized Lambert determinants -/
namespace Lambert
noncomputable section
open Polynomial Finset Filter Topology

/-- The signed normalized determinant is strictly positive at the actual Lambert value. -/
theorem lambertNormalizedDeterminant_eval_pos (q : ℝ) (hq : 1 < q) (h k : ℕ) :
    0 < (lambertNormalizedDeterminant q h k).eval (lambertValue q) := by
  rw [lambertNormalizedDeterminant, eval_mul, eval_C]
  exact mul_pos (zpow_pos (zero_lt_one.trans hq) _)
    (lambertPoleDeterminant_eval_pos q hq h k h k)

/-- Normalization shifts the exact logarithmic estimate by B log q and retains the uniform linear error. -/
theorem lambertNormalizedDeterminant_log_bounds (q : ℝ) (hq : 1 < q) (h k : ℕ) :
    let K := (h : ℝ) * (h + 1) * (2 * h + 1) / 6 + k * h * (h + 1) / 2 +
      h * (h*k+h*(h-1)/2);
    ((lambertTranslatedInfinityExponent h k 0 k : ℝ) - K) * Real.log q +
        2 * h * Real.log (geometricProductFloor q⁻¹) ≤
      Real.log ((lambertNormalizedDeterminant q h k).eval (lambertValue q)) ∧
    Real.log ((lambertNormalizedDeterminant q h k).eval (lambertValue q)) ≤
      ((lambertTranslatedInfinityExponent h k 0 k : ℝ) - K) * Real.log q -
        4 * h * Real.log (geometricProductFloor q⁻¹) := by
  dsimp only
  rw [lambertNormalizedDeterminant, eval_mul, eval_C,
    Real.log_mul (zpow_ne_zero _ (zero_lt_one.trans hq).ne')
      (lambertPoleDeterminant_eval_pos q hq h k h k).ne', Real.log_zpow]
  have he := lambertPoleDeterminant_log_bounds q hq h k h k
  dsimp only at he
  constructor <;> nlinarith [he.1, he.2]


/-- For q>1, the main normalized determinant has cubic logarithmic coefficient -(202140) log q. -/
theorem lambertMain_determinant_log_tendsto (q : ℝ) (hq : 1 < q) :
    Tendsto (fun N : ℕ => Real.log ((lambertNormalizedDeterminant q (60 * N) (3 * N)).eval
      (lambertValue q)) / (N : ℝ) ^ 3) atTop (𝓝 (-(202140) * Real.log q)) := by
  let G := Real.log (geometricProductFloor q⁻¹)
  have hi : Tendsto (fun N : ℕ => (1 : ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hl := (tendsto_const_nhds (x := -202140*Real.log q)).add
    ((hi.pow 2).const_mul (-10*Real.log q+120*G))
  have hu := (tendsto_const_nhds (x := -202140*Real.log q)).add
    ((hi.pow 2).const_mul (-10*Real.log q-240*G))
  simp only [zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] at hl hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have hb := (lambertNormalizedDeterminant_log_bounds q hq (60*N) (3*N)).1
    rw [lambertMain_infinity] at hb
    push_cast at hb
    apply (le_div_iff₀ (pow_pos hn 3)).mpr
    have he : (-202140*Real.log q+((1 : ℝ)/N)^2*(-10*Real.log q+120*G))*(N : ℝ)^3 =
        (-(202140*(N : ℝ)^3+10*N))*Real.log q+120*N*G := by field_simp; ring
    rw [mul_comm (-10*Real.log q+120*G), he]
    dsimp [G]
    nlinarith [hb]
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have hb := (lambertNormalizedDeterminant_log_bounds q hq (60*N) (3*N)).2
    rw [lambertMain_infinity] at hb
    push_cast at hb
    apply (div_le_iff₀ (pow_pos hn 3)).mpr
    have he : (-202140*Real.log q+((1 : ℝ)/N)^2*(-10*Real.log q-240*G))*(N : ℝ)^3 =
        (-(202140*(N : ℝ)^3+10*N))*Real.log q-240*N*G := by field_simp; ring
    rw [mul_comm (-10*Real.log q-240*G), he]
    dsimp [G]
    nlinarith [hb]

end
end Lambert
