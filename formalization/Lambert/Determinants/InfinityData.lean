import Lambert.Arithmetic.RatFuncInfinity
import Lambert.Determinants.MomentData
import Mathlib.Data.Fin.Tuple.Sort

/-! # Entry bounds and signed exponents for Lambert infinity normalization -/
namespace Lambert
noncomputable section
open Polynomial Matrix Finset WithZero
open scoped Classical
private abbrev v := RatFunc.inftyValuation ℚ

/-- A difference of distinct formal base powers has infinity valuation given by the larger exponent. -/
theorem lambertPowerDifference_inftyValuation (i j : ℕ) (hij : i < j) :
    v ((RatFunc.X : RatFunc ℚ) ^ j - RatFunc.X ^ i) = exp (j : ℤ) := by
  have he (n : ℕ) : v ((RatFunc.X : RatFunc ℚ) ^ n) = exp (n : ℤ) := by
    rw [map_pow, RatFunc.inftyValuation.X, ← WithZero.exp_nsmul]
    simp
  rw [Valuation.map_sub_eq_of_lt_left v (by rw [he, he]; exact WithZero.exp_lt_exp.mpr (by exact_mod_cast hij)), he]

/-- A Lambert reciprocal entry has infinity valuation at most one. -/
theorem lambertReciprocal_inftyValuation_le_one (n : ℕ) :
    v (1 / ((RatFunc.X : RatFunc ℚ) ^ (n + 1) - 1)) ≤ 1 := by
  have he := lambertPowerDifference_inftyValuation 0 (n + 1) (Nat.succ_pos n)
  simp only [pow_zero] at he
  rw [one_div, map_inv₀, he, ← WithZero.exp_neg, ← WithZero.exp_zero]
  exact WithZero.exp_le_exp.mpr (by omega)

/-- A Lambert entry evaluated in the valuation unit ball has infinity growth bounded by its row-column product. -/
theorem lambertPoleEntry_inftyValuation_le (z : RatFunc ℚ) (hz : v z ≤ 1) (i j : ℕ) :
    v ((lambertPoleEntry (RatFunc.X : RatFunc ℚ) i j).eval z) ≤ exp ((i : ℤ) * j) := by
  induction i with
  | zero =>
    simp only [lambertPoleEntry_zero, eval_sub, eval_X, eval_C, Nat.cast_zero, zero_mul, exp_zero]
    apply Valuation.map_sub_le v hz
    exact Valuation.map_sum_le _ (fun n _ => lambertReciprocal_inftyValuation_le_one n)
  | succ i ih =>
    rw [lambertPoleEntry_succ, eval_sub, eval_mul, eval_C, eval_C]
    apply Valuation.map_sub_le
    · rw [map_mul, map_pow, RatFunc.inftyValuation.X]
      have he : exp (1 : ℤ) ^ j = exp (j : ℤ) := by rw [← exp_nsmul]; simp
      rw [he]
      calc
        _ ≤ exp (j : ℤ) * exp ((i : ℤ) * j) := mul_le_mul' le_rfl ih
        _ = _ := by rw [← exp_add]; congr 1; push_cast; ring
    · exact (lambertReciprocal_inftyValuation_le_one i).trans (by
        rw [← exp_zero]
        exact exp_le_exp.mpr (by positivity))

/-- Augmented row weights combine shifted moment degrees with the extra polynomial degrees. -/
def lambertAugmentedRowWeight (h d s : ℕ) : Fin (h + d) → ℕ :=
  Fin.addCases (fun r => r.val + s) (fun r => r.val)

/-- The signed infinity normalization subtracts the sorted augmented degree from the Vandermonde degree. -/
def lambertInfinityExponent (h d s : ℕ) : ℤ :=
  ∑ j : Fin (h + d), (j.val : ℤ) * j.val -
    ∑ j : Fin (h + d), (j.val : ℤ) *
      lambertAugmentedRowWeight h d s (Tuple.sort (lambertAugmentedRowWeight h d s) j)

/-- Disjoint polynomial and shifted row ranges give the exact signed infinity exponent. -/
theorem lambertInfinityExponent_of_le (h d s : ℕ) (hds : d ≤ s) :
    lambertInfinityExponent h d s =
      -((s : ℤ) - d) * ∑ r : Fin h, ((d : ℤ) + r.val) := by
  let e : Fin (h + d) ≃ Fin (d + h) := finCongr (Nat.add_comm h d)
  let σ : Equiv.Perm (Fin (h + d)) := e.trans finAddFlip
  have hw (j : Fin (h + d)) : lambertAugmentedRowWeight h d s (σ j) =
      if j.val < d then j.val else j.val - d + s := by
    obtain ⟨k, rfl⟩ := e.symm.surjective j
    refine Fin.addCases ?_ ?_ k
    · intro r
      simp [σ, e, lambertAugmentedRowWeight, r.isLt]
    · intro r
      simp [σ, e, lambertAugmentedRowWeight, show ¬r.val + d < d by omega]
  have hm : Monotone (lambertAugmentedRowWeight h d s ∘ σ) := by
    intro i j hij
    change lambertAugmentedRowWeight h d s (σ i) ≤ lambertAugmentedRowWeight h d s (σ j)
    rw [hw, hw]
    have hh : i.val ≤ j.val := hij
    split <;> split <;> omega
  have hs := Tuple.comp_sort_eq_comp_iff_monotone.mpr hm
  unfold lambertInfinityExponent
  have he (j : Fin (h + d)) := congrFun hs j
  simp only [Function.comp_apply] at he
  simp_rw [← he]
  rw [← sum_sub_distrib, ← Equiv.sum_comp e.symm, Fin.sum_univ_add]
  have hf : (∑ j : Fin d, (((e.symm (Fin.castAdd h j)).val : ℤ) *
      (e.symm (Fin.castAdd h j)).val -
      ((e.symm (Fin.castAdd h j)).val : ℤ) *
        lambertAugmentedRowWeight h d s (σ (e.symm (Fin.castAdd h j))))) = 0 := by
    apply sum_eq_zero
    intro j _
    simp [σ, e, lambertAugmentedRowWeight]
  rw [hf, zero_add, mul_sum]
  apply sum_congr rfl
  intro j _
  simp [σ, e, lambertAugmentedRowWeight]
  ring


end
end Lambert
