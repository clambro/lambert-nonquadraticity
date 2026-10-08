import Lambert.Refinement.Baseline
import Lambert.Arithmetic.TotientAffineInterval
import Lambert.Analysis.CubicDilation

/-! # Weighted limits of the uncorrected Lambert filtration profile -/
namespace Lambert
noncomputable section
open Finset Filter Topology

private theorem supported_sum (f : ℕ → ℝ) (L U : ℕ) (hLU : L≤U)
    (hf : ∀ n, L≤n → f n=0) :
    (∑ n ∈ Icc 1 U, f n)=∑ n ∈ Ico 1 L, f n := by
  symm
  apply sum_subset
  · intro n hn
    obtain ⟨hl,hu⟩ := mem_Ico.mp hn
    exact mem_Icc.mpr ⟨hl, by omega⟩
  · intro n hn hnot
    apply hf
    simp only [mem_Icc, mem_Ico] at hn hnot
    omega

/-- The weighted filtration baseline is a square-window sum plus a constant prefix and two elementary tent corrections. -/
theorem lambertRefinementBaseline_weighted_sum (w : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 (543*N), w n*lambertRefinementBaseline N n) =
      500*N*(∑ n ∈ Icc 1 (543*N), w n)+
      (∑ n ∈ Ico 1 (516*N), w n*lambertCyclotomicExponent (516*N) n)-
      2*arithmeticTent w (516*N) 1+arithmeticTent w (516*N) 2 := by
  simp_rw [lambertRefinementBaseline_eq_square, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  have hs := supported_sum (fun n => w n*(lambertCyclotomicExponent (516*N) n : ℝ))
    (516*N) (543*N) (by omega) (fun n hn => by rw [lambertCyclotomicExponent_eq_zero_of_le _ _ hn]; simp)
  have ht (m : ℕ) (hm : 0<m) :
      (∑ n ∈ Icc 1 (543*N), w n*((516*N-m*n : ℕ) : ℝ)) = arithmeticTent w (516*N) m := by
    rw [arithmeticTent_eq_window _ _ _ hm]
    apply supported_sum _ _ _ (by omega)
    intro n hn
    have he := Nat.le_mul_of_pos_left n hm
    simp [Nat.sub_eq_zero_of_le (show 516*N≤m*n by omega)]
  simp_rw [mul_add, sum_add_distrib]
  rw [hs]
  have h1 := ht 1 (by omega)
  simp only [one_mul] at h1
  have h2 := ht 2 (by omega)
  have hm : (∑ n ∈ Icc 1 (543*N), w n*(2*((516*N-n : ℕ) : ℝ))) =
      2*(∑ n ∈ Icc 1 (543*N), w n*((516*N-n : ℕ) : ℝ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    ring
  rw [hm,h1,h2]
  simp only [← sum_mul, mul_comm]

/-- The total unweighted baseline pole exponent is subcubic. -/
theorem lambertRefinementBaseline_sum_tendsto :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 (543*N), (lambertRefinementBaseline N n : ℝ))/(N : ℝ)^3)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (1 : ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hs := tendsto_cubic_dilation _ lambertCyclotomicExponent_sum_tendsto_zero 516 (by omega)
  have ht (m : ℕ) (hm : 0<m) := tendsto_cubic_dilation _ (arithmeticTent_one_tendsto m hm) 516 (by omega)
  have he := (((hi.const_mul 271500).add hs).sub ((ht 1 (by omega)).const_mul 2)).add (ht 2 (by omega))
  norm_num at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  rw [show (∑ n ∈ Icc 1 (543*N), (lambertRefinementBaseline N n : ℝ)) =
      ∑ n ∈ Icc 1 (543*N), (1 : ℝ)*lambertRefinementBaseline N n by simp,
    lambertRefinementBaseline_weighted_sum]
  simp only [one_mul, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- Classical totient means give the filtration baseline cubic coefficient 17173512+442273500/π². -/
theorem lambertRefinementBaseline_totient_tendsto :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 (543*N),
      (Nat.totient n : ℝ)*lambertRefinementBaseline N n)/(N : ℝ)^3)
      atTop (𝓝 (17173512+442273500/Real.pi^2)) := by
  have hp := totient_scaled_prefix_tendsto 543 (by norm_num)
  have hs := tendsto_cubic_dilation _ (lambertCyclotomicExponent_totient_tendsto) 516 (by omega)
  have ht (m : ℕ) (hm : 0<m) := tendsto_cubic_dilation _ (totientTent_tendsto m hm) 516 (by omega)
  have he := ((((hp.const_mul 500).add hs).sub ((ht 1 (by omega)).const_mul 2)).add (ht 2 (by omega)))
  convert he using 1
  · funext N
    rw [lambertRefinementBaseline_weighted_sum]
    have hf : ⌊(543 : ℝ)*N⌋₊=543*N := by exact_mod_cast (Nat.floor_natCast (543*N) (R := ℝ))
    rw [hf]
    by_cases hn : (N : ℝ)=0
    · simp [hn]
    · field_simp
  · norm_num
    ring

end
end Lambert
