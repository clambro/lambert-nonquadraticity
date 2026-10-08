import Lambert.Determinants.CyclotomicExponent
import Lambert.Determinants.ZeroOrderMinimum
import Lambert.Arithmetic.TentDominated

/-!
# Cubic growth of square-window pole exponents

The positive-part formula separates into arithmetic tents. A reciprocal-square
majorant controls the moving odd-slope sum uniformly, using only classical totient means.
-/
namespace Lambert
noncomputable section
open Finset Filter Topology

/-- The weighted square-window cyclotomic exponent is a combination of arithmetic tents. -/
theorem lambertCyclotomicExponent_weighted_sum (w : ℕ → ℝ) (h : ℕ) :
    (∑ n ∈ Ico 1 h, w n * lambertCyclotomicExponent h n) =
      3 * arithmeticTent w h 1 - arithmeticTent w h 2 +
        ∑ k ∈ range h, arithmeticTent w h (2 * k + 3) := by
  have hc (n : ℕ) : (lambertCyclotomicExponent h n : ℝ) =
      3 * ((h - n : ℕ) : ℝ) - ((h - 2 * n : ℕ) : ℝ) +
        ∑ k ∈ range h, ((h - (2 * k + 3) * n : ℕ) : ℝ) := by
    have he : h - 2 * n ≤ 3 * (h - n) := by omega
    simp only [lambertCyclotomicExponent, Nat.cast_add, Nat.cast_sub he,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
  simp_rw [hc, mul_add, mul_sub, mul_sum]
  rw [sum_add_distrib, sum_sub_distrib, sum_comm]
  rw [arithmeticTent_eq_window w h 1 (by omega), arithmeticTent_eq_window w h 2 (by omega)]
  have hk (k : ℕ) := arithmeticTent_eq_window w h (2 * k + 3) (by omega)
  simp_rw [hk]
  simp only [one_mul]
  congr 1
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  ring

/-- The normalized total cyclotomic exponent vanishes at cubic scale. -/
theorem lambertCyclotomicExponent_sum_tendsto_zero :
    Tendsto (fun h : ℕ => (∑ n ∈ Ico 1 h, (lambertCyclotomicExponent h n : ℝ)) /
      (h : ℝ) ^ 3) atTop (𝓝 0) := by
  have ho := odd_arithmeticTent_tendsto (fun _ => 1)
    (fun n hn => ⟨by norm_num, by exact_mod_cast hn⟩) (fun _ => 0) arithmeticTent_one_tendsto
  have he := (((arithmeticTent_one_tendsto 1 (by omega)).const_mul 3).sub
    (arithmeticTent_one_tendsto 2 (by omega))).add ho
  simp only [tsum_zero, mul_zero, sub_zero, add_zero] at he
  convert he using 1
  funext h
  rw [show (∑ n ∈ Ico 1 h, (lambertCyclotomicExponent h n : ℝ)) =
    ∑ n ∈ Ico 1 h, (1 : ℝ) * lambertCyclotomicExponent h n by simp only [one_mul],
    lambertCyclotomicExponent_weighted_sum, add_div, sub_div, mul_div_assoc]

/-- The totient-weighted square-window exponent has cubic coefficient `1/8+7/(4π²)`. -/
theorem lambertCyclotomicExponent_totient_tendsto :
    Tendsto (fun h : ℕ => (∑ n ∈ Ico 1 h,
      (Nat.totient n : ℝ) * lambertCyclotomicExponent h n) / (h : ℝ) ^ 3)
      atTop (𝓝 (1 / 8 + 7 / (4 * Real.pi ^ 2))) := by
  have ho := odd_arithmeticTent_tendsto (fun n => (Nat.totient n : ℝ))
    (fun n _ => ⟨by positivity, by exact_mod_cast Nat.totient_le n⟩)
    (fun m => 1 / (Real.pi ^ 2 * (m : ℝ) ^ 2)) (totientTent_tendsto)
  have hs : (∑' k : ℕ, 1 / (Real.pi ^ 2 * (2 * k + 3 : ℕ) ^ 2)) =
      (Real.pi ^ 2 / 8 - 1) / Real.pi ^ 2 := by
    have he : (fun k : ℕ => (1 : ℝ) / (Real.pi ^ 2 * (2 * k + 3 : ℕ) ^ 2)) =
        fun k => ((1 : ℝ) / (2 * k + 3 : ℕ) ^ 2) / Real.pi ^ 2 := by
      funext k
      ring
    rw [he, tsum_div_const, tsum_odd_reciprocal_squares]
  rw [hs] at ho
  have he := (((totientTent_tendsto 1 (by omega)).const_mul 3).sub
    (totientTent_tendsto 2 (by omega))).add ho
  have hc : 3 * (1 / (Real.pi ^ 2 * (1 : ℕ) ^ 2)) -
      1 / (Real.pi ^ 2 * (2 : ℕ) ^ 2) + (Real.pi ^ 2 / 8 - 1) / Real.pi ^ 2 =
      (1 : ℝ) / 8 + 7 / (4 * Real.pi ^ 2) := by
    have hp := Real.pi_ne_zero
    field_simp
    ring
  rw [hc] at he
  convert he using 1
  funext h
  rw [lambertCyclotomicExponent_weighted_sum, add_div, sub_div, mul_div_assoc]

end
end Lambert
