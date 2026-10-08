import Mathlib.Analysis.SpecificLimits.Basic

/-! # Dilation of cubic sequence limits -/
namespace Lambert
open Filter Topology

/-- An integral dilation multiplies a cubic sequence limit by the cube of the dilation factor. -/
theorem tendsto_cubic_dilation (f : ℕ → ℝ) {c : ℝ}
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ) ^ 3) atTop (𝓝 c))
    (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => f (k * n) / (n : ℝ) ^ 3) atTop (𝓝 (c * k ^ 3)) := by
  have ht : Tendsto (fun n : ℕ => k * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hk) tendsto_id
  have he := (hf.comp ht).mul_const ((k : ℝ) ^ 3)
  apply he.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  change f (k * n) / ((k * n : ℕ) : ℝ) ^ 3 * (k : ℝ) ^ 3 = f (k * n) / (n : ℝ) ^ 3
  push_cast
  field_simp

end Lambert
