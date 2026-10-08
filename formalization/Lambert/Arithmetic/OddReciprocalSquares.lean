import Mathlib.NumberTheory.ZetaValues

/-!
# Reciprocal squares along the odd integers

The odd tail starting at three follows by separating the even terms in the
formal Basel sum and removing the first odd term.
-/
namespace Lambert
open scoped Topology

/-- Reciprocal squares at odd integers starting with three are summable. -/
theorem summable_odd_reciprocal_squares :
    Summable (fun k : ℕ => (1 : ℝ) / (2 * k + 3 : ℕ) ^ 2) :=
  hasSum_zeta_two.summable.comp_injective (fun _ _ h => by omega)

/-- The reciprocal-square sum over odd integers at least three is `π²/8-1`. -/
theorem tsum_odd_reciprocal_squares :
    (∑' k : ℕ, (1 : ℝ) / (2 * k + 3 : ℕ) ^ 2) = Real.pi ^ 2 / 8 - 1 := by
  have he : Summable (fun k : ℕ => (1 : ℝ) / (2 * k : ℕ) ^ 2) :=
    hasSum_zeta_two.summable.comp_injective (fun _ _ h => by omega)
  have ho : Summable (fun k : ℕ => (1 : ℝ) / (2 * k + 1 : ℕ) ^ 2) :=
    hasSum_zeta_two.summable.comp_injective (fun _ _ h => by omega)
  have hev : (∑' k : ℕ, (1 : ℝ) / (2 * k : ℕ) ^ 2) = Real.pi ^ 2 / 24 := by
    have hh : (fun k : ℕ => (1 : ℝ) / (2 * k : ℕ) ^ 2) =
        fun k : ℕ => ((1 : ℝ) / k ^ 2) / 4 := by
      funext k
      push_cast
      ring
    rw [hh, tsum_div_const, hasSum_zeta_two.tsum_eq]
    ring
  have hsplit := tsum_even_add_odd (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) he ho
  rw [hasSum_zeta_two.tsum_eq, hev] at hsplit
  have htail := ho.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.mul_zero, Nat.zero_add, Nat.cast_one,
    one_pow, div_one] at htail
  have hshift : (fun k : ℕ => (1 : ℝ) / (2 * (k + 1) + 1 : ℕ) ^ 2) =
      fun k : ℕ => (1 : ℝ) / (2 * k + 3 : ℕ) ^ 2 := by
    funext k
    congr 2
  rw [hshift] at htail
  linarith

end Lambert
