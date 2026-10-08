import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Summation of quadratic asymptotics

A quadratic asymptotic for a sequence gives a cubic asymptotic for its partial sums.
-/
namespace Lambert
open Finset Filter Topology Asymptotics

private theorem sum_squares (N : ℕ) :
    (∑ k ∈ range N, (k : ℝ) ^ 2) = (N : ℝ) * (N - 1) * (2 * N - 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Partial sums of the squares of the natural numbers have cubic mean `1/3`. -/
theorem sum_squares_cubic_tendsto :
    Tendsto (fun N : ℕ => (∑ k ∈ range N, (k : ℝ) ^ 2) / (N : ℝ) ^ 3)
      atTop (𝓝 (1 / 3 : ℝ)) := by
  have hi : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have he := (((tendsto_const_nhds (x := (1 : ℝ))).sub hi).mul
    ((tendsto_const_nhds (x := (2 : ℝ))).sub hi)).div_const 6
  norm_num at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < N by omega))
  rw [sum_squares]
  field_simp

/-- A sequence with quadratic normalized limit `c` has partial sums with cubic normalized limit `c/3`. -/
theorem quadratic_summatory_tendsto (S : ℕ → ℝ) {c : ℝ}
    (h : Tendsto (fun N : ℕ => S N / (N : ℝ) ^ 2) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => (∑ k ∈ range N, S k) / (N : ℝ) ^ 3)
      atTop (𝓝 (c / 3)) := by
  have he : (fun N : ℕ => S N - c * (N : ℝ) ^ 2) =o[atTop]
      (fun N : ℕ => (N : ℝ) ^ 2) := by
    apply (isLittleO_iff_tendsto' (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < N by omega))
      intro hz
      exact (pow_ne_zero 2 hn hz).elim)).mpr
    have ht := h.sub_const c
    simp only [sub_self] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < N by omega))
    field_simp
  have htop : Tendsto (fun N : ℕ => ∑ k ∈ range N, (k : ℝ) ^ 2) atTop atTop := by
    have ht := sum_squares_cubic_tendsto.pos_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 3)
      ((tendsto_pow_atTop (by decide : 3 ≠ 0)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < N by omega))
    exact div_mul_cancel₀ _ (pow_ne_zero 3 hn)
  have hs := he.sum_range (fun N => sq_nonneg (N : ℝ)) htop
  have hz := hs.tendsto_div_nhds_zero
  have ht := hz.mul sum_squares_cubic_tendsto
  simp only [zero_mul] at ht
  have hmain := sum_squares_cubic_tendsto.const_mul c
  have hout := ht.add hmain
  simp only [zero_add] at hout
  rw [show c * (1 / 3) = c / 3 by ring] at hout
  apply hout.congr'
  filter_upwards [htop.eventually_ne_atTop 0] with N hN
  rw [div_mul_div_cancel₀ hN, sum_sub_distrib, ← mul_sum]
  ring

end Lambert
