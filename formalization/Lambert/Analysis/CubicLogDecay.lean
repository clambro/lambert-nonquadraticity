import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Vanishing from a negative cubic logarithmic bound

A strictly negative normalized logarithmic upper bound forces positive sequences
to zero. Polynomially smaller terms may be retained in the bounding function.
-/
namespace Lambert
open Filter Topology

/-- A positive sequence tends to zero when a logarithmic upper bound has a
strictly negative cubic limit. -/
theorem tendsto_zero_of_cubic_log_upper (f g : ℕ → ℝ) (hf : ∀ n, 0 < f n)
    (hfg : ∀ n, Real.log (f n) ≤ g n) {L : ℝ} (hL : L < 0)
    (hg : Tendsto (fun n : ℕ => g n / (n : ℝ) ^ 3) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have he := Real.tendsto_exp_atBot.comp (hpow.const_mul_atTop_of_neg (show L / 2 < 0 by linarith))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
  · exact Filter.Eventually.of_forall (fun n => (hf n).le)
  · filter_upwards [hg.eventually (eventually_lt_nhds (show L < L / 2 by linarith)),
      eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hb : g n ≤ L / 2 * (n : ℝ) ^ 3 :=
      ((div_lt_iff₀ (pow_pos hn0 3)).mp hn).le
    rw [← Real.exp_log (hf n)]
    exact Real.exp_le_exp.mpr ((hfg n).trans hb)

end Lambert
