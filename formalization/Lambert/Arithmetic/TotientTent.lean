import Lambert.Arithmetic.TotientMeanValues

/-!
# Uniform bounds and limits for arithmetic tent sums

Truncation at `h/m` expresses each tent sum through two ordinary mean values.
A summable quadratic bound in `m` justifies later moving-window limits.
-/
namespace Lambert
noncomputable section
open Finset Filter Topology

/-- An arithmetic tent sum weights the positive part of `h-mn` by `w(n)`. -/
def arithmeticTent (w : ℕ → ℝ) (h m : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 (h / m), w n * ((h : ℝ) - m * n)

/-- A positive integer divisor has the expected normalized quotient limit. -/
theorem tendsto_nat_div_cast_ratio (m : ℕ) (hm : 0 < m) :
    Tendsto (fun h : ℕ => ((h / m : ℕ) : ℝ) / h) atTop (𝓝 ((m : ℝ)⁻¹)) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hinv : Tendsto (fun h : ℕ => (1 : ℝ) / h) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun h : ℕ => (m : ℝ)⁻¹ - 1 / h) (h := fun _ : ℕ => (m : ℝ)⁻¹)
    (by simpa using tendsto_const_nhds.sub hinv) tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have hh0 : 0 < (h : ℝ) := by exact_mod_cast hh
    have he : h < (h / m + 1) * m := by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ h hm
    have her : (h : ℝ) < (((h / m : ℕ) : ℝ) + 1) * m := by exact_mod_cast he
    apply (le_div_iff₀ hh0).mpr
    field_simp
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have hh0 : 0 < (h : ℝ) := by exact_mod_cast hh
    have he : ((h / m : ℕ) : ℝ) * m ≤ h := by exact_mod_cast Nat.div_mul_le_self h m
    apply (div_le_iff₀ hh0).mpr
    simpa only [div_eq_mul_inv, mul_comm] using
      (le_div_iff₀ (show (0 : ℝ) < m by positivity)).mpr he

/-- A tent sum is the difference of its zeroth and first truncated moments. -/
theorem arithmeticTent_eq_moments (w : ℕ → ℝ) (h m : ℕ) :
    arithmeticTent w h m =
      h * (∑ n ∈ Icc 1 (h / m), w n) - m * (∑ n ∈ Icc 1 (h / m), (n : ℝ) * w n) := by
  simp only [arithmeticTent, mul_sub, sum_sub_distrib, mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intros <;> ring

/-- Classical totient mean values give the cubic limit for each fixed positive tent slope. -/
theorem totientTent_tendsto (m : ℕ) (hm : 0 < m) :
    Tendsto (fun h : ℕ => arithmeticTent (fun n => (Nat.totient n : ℝ)) h m / (h : ℝ) ^ 3)
      atTop (𝓝 (1 / (Real.pi ^ 2 * (m : ℝ) ^ 2))) := by
  have ht : Tendsto (fun h : ℕ => h / m) atTop atTop := le_of_eq (map_div_atTop_eq_nat m hm)
  have hr := tendsto_nat_div_cast_ratio m hm
  have hz := (totient_summatory_tendsto.comp ht).mul (hr.pow 2)
  have hf := ((totient_weighted_summatory_tendsto.comp ht).mul (hr.pow 3)).const_mul (m : ℝ)
  have he := hz.sub hf
  have hlim : 3 / Real.pi ^ 2 * ((m : ℝ)⁻¹) ^ 2 -
      (m : ℝ) * (2 / Real.pi ^ 2 * ((m : ℝ)⁻¹) ^ 3) =
      1 / (Real.pi ^ 2 * (m : ℝ) ^ 2) := by
    field_simp
    ring
  rw [hlim] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop m] with h hh
  have hN : (h / m : ℕ) ≠ 0 := Nat.ne_of_gt (Nat.div_pos hh hm)
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hm.trans_le hh))
  have hN0 : ((h / m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN
  dsimp only [Function.comp_apply]
  rw [arithmeticTent_eq_moments]
  field_simp

/-- Nonnegative weights bounded by their index give a quadratic cutoff bound. -/
theorem arithmeticTent_nonneg_le (w : ℕ → ℝ) (hw : ∀ n, 0 < n → 0 ≤ w n ∧ w n ≤ n)
    (h m : ℕ) (hm : 0 < m) :
    0 ≤ arithmeticTent w h m ∧ arithmeticTent w h m ≤ (h : ℝ) * ((h / m : ℕ) : ℝ) ^ 2 := by
  have hb (n : ℕ) (hn : n ∈ Icc 1 (h / m)) : 0 ≤ (h : ℝ) - m * n := by
    have he : m * n ≤ h := by
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).mp (mem_Icc.mp hn).2
    exact sub_nonneg.mpr (by exact_mod_cast he)
  constructor
  · exact sum_nonneg (fun n hn => mul_nonneg (hw n (mem_Icc.mp hn).1).1 (hb n hn))
  · calc
      arithmeticTent w h m ≤ ∑ _n ∈ Icc 1 (h / m), (((h / m : ℕ) : ℝ) * h) := by
        apply sum_le_sum
        intro n hn
        apply mul_le_mul ((hw n (mem_Icc.mp hn).1).2.trans (by exact_mod_cast (mem_Icc.mp hn).2))
          (sub_le_self _ (by positivity)) (hb n hn) (by positivity)
      _ = (h : ℝ) * ((h / m : ℕ) : ℝ) ^ 2 := by
        simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

/-- Normalized tent sums admit a summable bound in the positive slope,
uniformly in the moving cutoff. -/
theorem arithmeticTent_normalized_le (w : ℕ → ℝ) (hw : ∀ n, 0 < n → 0 ≤ w n ∧ w n ≤ n)
    (h m : ℕ) (hm : 0 < m) :
    ‖arithmeticTent w h m / (h : ℝ) ^ 3‖ ≤ 1 / (m : ℝ) ^ 2 := by
  obtain ⟨hn, hb⟩ := arithmeticTent_nonneg_le w hw h m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn (by positivity))]
  by_cases hh : h = 0
  · subst h
    simp
  have hh0 : 0 < (h : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hh
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have he : ((h / m : ℕ) : ℝ) * m ≤ h := by exact_mod_cast Nat.div_mul_le_self h m
  have he2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((h / m : ℕ) : ℝ) * m) he 2
  apply (div_le_iff₀ (pow_pos hh0 3)).mpr
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ (pow_pos hm0 2)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg (m : ℝ)),
    mul_le_mul_of_nonneg_left he2 hh0.le]

/-- Truncating a positive-part tent at `h/m` is equivalent to summing over the original window. -/
theorem arithmeticTent_eq_window (w : ℕ → ℝ) (h m : ℕ) (hm : 0 < m) :
    arithmeticTent w h m = ∑ n ∈ Ico 1 h, w n * ((h - m * n : ℕ) : ℝ) := by
  calc
    arithmeticTent w h m = ∑ n ∈ Icc 1 (h / m), w n * ((h - m * n : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro n hn
      have he : m * n ≤ h := by
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).mp (mem_Icc.mp hn).2
      rw [Nat.cast_sub he, Nat.cast_mul]
    _ = ∑ n ∈ Icc 1 h, w n * ((h - m * n : ℕ) : ℝ) := by
      apply sum_subset (Icc_subset_Icc_right (Nat.div_le_self h m))
      intro n hn hnN
      have he : h < m * n := by
        have : ¬n ≤ h / m := by simpa only [mem_Icc, (mem_Icc.mp hn).1, true_and] using hnN
        have he := (Nat.le_div_iff_mul_le hm).not.mp this
        simpa only [Nat.mul_comm, not_le] using he
      simp [Nat.sub_eq_zero_of_le he.le]
    _ = ∑ n ∈ Ico 1 h, w n * ((h - m * n : ℕ) : ℝ) := by
      symm
      apply sum_subset (show Ico 1 h ⊆ Icc 1 h from
        fun n hn => mem_Icc.mpr ⟨(mem_Ico.mp hn).1, (mem_Ico.mp hn).2.le⟩)
      intro n hn hnI
      have he : n = h := by simp only [mem_Icc, mem_Ico] at *; omega
      subst n
      have he : h ≤ m * h := Nat.le_mul_of_pos_left h hm
      simp [Nat.sub_eq_zero_of_le he]

end
end Lambert
