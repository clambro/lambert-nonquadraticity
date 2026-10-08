import Lambert.Refinement.Normalization

/-! # Cubic limits of the selected endpoint normalization -/
namespace Lambert
noncomputable section
open Filter Topology

/-- The quadratic zero-place construction differs from its exact cubic-and-quadratic expression by less than one rounding unit. -/
theorem lambertRefinementZeroExponent_bounds (N : ℕ) :
    141020912*N^3+593682*N^2 ≤ 24*lambertRefinementZeroExponent N ∧
    24*lambertRefinementZeroExponent N ≤ 141020912*N^3+593682*N^2+23 := by
  have hl := Nat.lt_mul_div_succ (141020912*N^3+593682*N^2+23) (by decide : 0<24)
  have hu := Nat.mul_div_le (141020912*N^3+593682*N^2+23) 24
  unfold lambertRefinementZeroExponent
  omega

/-- The selected zero-place exponent has cubic coefficient 17627614/3. -/
theorem lambertRefinementZeroExponent_tendsto :
    Tendsto (fun N : ℕ => (lambertRefinementZeroExponent N : ℝ)/(N : ℝ)^3)
      atTop (𝓝 (17627614/3)) := by
  have hi : Tendsto (fun N : ℕ => (1 : ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hl := (tendsto_const_nhds (x := (17627614/3 : ℝ))).add (hi.const_mul (98947/4))
  have hu := hl.add ((hi.pow 3).const_mul (23/24))
  simp only [mul_zero, add_zero, zero_pow (by decide : 3≠0)] at hl hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hb : 141020912*(N : ℝ)^3+593682*N^2 ≤ 24*lambertRefinementZeroExponent N :=
      by exact_mod_cast (lambertRefinementZeroExponent_bounds N).1
    apply (le_div_iff₀ (pow_pos hn 3)).mpr
    have he : ((17627614/3 : ℝ)+(98947/4)*(1/N))*(N : ℝ)^3 =
        (141020912*(N : ℝ)^3+593682*N^2)/24 := by field_simp; ring
    rw [he]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hb : 24*(lambertRefinementZeroExponent N : ℝ) ≤ 141020912*(N : ℝ)^3+593682*N^2+23 :=
      by exact_mod_cast (lambertRefinementZeroExponent_bounds N).2
    apply (div_le_iff₀ (pow_pos hn 3)).mpr
    have he : ((17627614/3 : ℝ)+(98947/4)*(1/N)+(23/24)*(1/N)^3)*(N : ℝ)^3 =
        (141020912*(N : ℝ)^3+593682*N^2+23)/24 := by field_simp; ring
    rw [he]
    linarith

/-- The selected clearing power preserves the signed endpoint difference exactly. -/
theorem lambertRefinementClearingZeroExponent_cast (N : ℕ) :
    (lambertRefinementClearingZeroExponent N : ℤ) =
      lambertRefinementZeroExponent N+3662500*(N : ℤ)^3-6250*N^2 := by
  have hb : -(3662500 : ℤ)*N^3+6250*N^2 ≤ 0 := by
    by_cases hN : N=0
    · simp [hN]
    · have hn : (1 : ℤ) ≤ N := by omega
      have he := mul_nonneg (sq_nonneg (N : ℤ)) (show (0 : ℤ) ≤ N-1 by omega)
      nlinarith [sq_nonneg (N : ℤ)]
  rw [lambertRefinementClearingZeroExponent, lambertRefinementFamily_infinity_exponent,
    Int.toNat_of_nonneg (by have := Nat.cast_nonneg (α := ℤ) (lambertRefinementZeroExponent N); omega)]
  ring

/-- The signed-normalized clearing power at zero has cubic coefficient 28615114/3. -/
theorem lambertRefinementClearingZeroExponent_tendsto :
    Tendsto (fun N : ℕ => (lambertRefinementClearingZeroExponent N : ℝ)/(N : ℝ)^3)
      atTop (𝓝 (28615114/3)) := by
  have hi : Tendsto (fun N : ℕ => (1 : ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have he := (lambertRefinementZeroExponent_tendsto.add_const 3662500).sub (hi.const_mul 6250)
  norm_num at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
  have hb : (lambertRefinementClearingZeroExponent N : ℝ)=
      lambertRefinementZeroExponent N+3662500*(N : ℝ)^3-6250*N^2 :=
    by exact_mod_cast lambertRefinementClearingZeroExponent_cast N
  rw [hb]
  field_simp

end
end Lambert
