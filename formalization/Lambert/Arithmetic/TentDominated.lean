import Lambert.Arithmetic.TotientTent
import Lambert.Arithmetic.OddReciprocalSquares

/-!
# Moving sums of arithmetic tents

The uniform reciprocal-square bound permits dominated convergence over all odd
slopes. The finite window equals the infinite sum because its remaining tents vanish.
-/
namespace Lambert
noncomputable section
open Finset Filter Topology

/-- A tent vanishes once its positive slope reaches the window length. -/
theorem arithmeticTent_eq_zero_of_le (w : ℕ → ℝ) (h m : ℕ) (hm : 0 < m) (hh : h ≤ m) :
    arithmeticTent w h m = 0 := by
  rw [arithmeticTent_eq_window w h m hm]
  apply sum_eq_zero
  intro n hn
  have he : h ≤ m * n := hh.trans (Nat.le_mul_of_pos_right m (mem_Ico.mp hn).1)
  simp [Nat.sub_eq_zero_of_le he]

/-- Moving finite sums over odd tent slopes converge to the sum of the fixed-slope limits. -/
theorem odd_arithmeticTent_tendsto (w : ℕ → ℝ)
    (hw : ∀ n, 0 < n → 0 ≤ w n ∧ w n ≤ n) (g : ℕ → ℝ)
    (hg : ∀ m, 0 < m → Tendsto (fun h : ℕ => arithmeticTent w h m / (h : ℝ) ^ 3)
      atTop (𝓝 (g m))) :
    Tendsto (fun h : ℕ => (∑ k ∈ range h, arithmeticTent w h (2 * k + 3)) / (h : ℝ) ^ 3)
      atTop (𝓝 (∑' k : ℕ, g (2 * k + 3))) := by
  have he := tendsto_tsum_of_dominated_convergence summable_odd_reciprocal_squares
    (fun k => hg (2 * k + 3) (by omega))
    (Filter.Eventually.of_forall (fun h k => arithmeticTent_normalized_le w hw h (2 * k + 3) (by omega)))
  apply he.congr'
  apply Filter.Eventually.of_forall
  intro h
  dsimp only
  rw [sum_div]
  exact tsum_eq_sum (fun k hk => by
    rw [arithmeticTent_eq_zero_of_le w h (2 * k + 3) (by omega)
      (by simp only [mem_range] at hk; omega), zero_div])

/-- Constant weights give a tent bound of order at most the square of the window length. -/
theorem arithmeticTent_one_le (h m : ℕ) (hm : 0 < m) :
    0 ≤ arithmeticTent (fun _ => 1) h m ∧ arithmeticTent (fun _ => 1) h m ≤ (h : ℝ) ^ 2 := by
  constructor
  · exact (arithmeticTent_nonneg_le _ (fun n hn => ⟨by norm_num, by exact_mod_cast hn⟩) h m hm).1
  · calc
      arithmeticTent (fun _ => 1) h m ≤ ∑ _n ∈ Icc 1 (h / m), (h : ℝ) := by
        apply sum_le_sum
        intro n _
        dsimp
        rw [one_mul]
        exact sub_le_self _ (by positivity)
      _ = ((h / m : ℕ) : ℝ) * h := by
        simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      _ ≤ (h : ℝ) ^ 2 := by
        have he : ((h / m : ℕ) : ℝ) ≤ h := by exact_mod_cast Nat.div_le_self h m
        nlinarith

/-- The normalized cubic contribution of constant-weight tents vanishes at every fixed positive slope. -/
theorem arithmeticTent_one_tendsto (m : ℕ) (hm : 0 < m) :
    Tendsto (fun h : ℕ => arithmeticTent (fun _ => 1) h m / (h : ℝ) ^ 3) atTop (𝓝 0) := by
  have hi : Tendsto (fun h : ℕ => (1 : ℝ) / h) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hi
  · exact Filter.Eventually.of_forall (fun h => div_nonneg (arithmeticTent_one_le h m hm).1 (by positivity))
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
    apply (div_le_iff₀ (pow_pos hh0 3)).mpr
    have he : (1 : ℝ) / h * (h : ℝ) ^ 3 = (h : ℝ) ^ 2 := by field_simp
    rw [he]
    exact (arithmeticTent_one_le h m hm).2

end
end Lambert
