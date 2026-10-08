import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Counting collisions of geometric nodes

Pairs whose positive index difference is divisible by a fixed order can be
counted either by quotients or by finite positive-part sums.
-/

namespace Lambert

open Finset
open scoped Classical

/-- The number of earlier indices congruent to a given index modulo `n`
is its quotient by `n`. -/
theorem geometricCollisionCount_row (h n : ℕ) (j : Fin h) :
    (∑ i : Fin h, if i < j ∧ n ∣ j.val - i.val then 1 else 0) = j.val / n := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div j.val n, sum_boole]
  apply card_bij (fun i _ => j.val - i.val)
  · intro i hi
    have hi' : i < j ∧ n ∣ j.val - i.val := (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, Nat.sub_le _ _⟩, hi'.2⟩
  · intro i hi k hk he
    have hi' := (mem_filter.mp hi).2
    have hk' := (mem_filter.mp hk).2
    apply Fin.ext
    have hi0 : i.val < j.val := hi'.1
    have hk0 : k.val < j.val := hk'.1
    omega
  · intro k hk
    rcases mem_filter.mp hk with ⟨hk, hd⟩
    rcases mem_Ioc.mp hk with ⟨hk0, hkj⟩
    refine ⟨⟨j.val - k, by omega⟩, ?_, by simp; omega⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    constructor
    · show j.val - k < j.val
      omega
    · simpa [Nat.sub_sub_self hkj] using hd

/-- The quotient sum counts the same pairs as the finite deficit sum. -/
theorem sum_range_div_eq_sum_deficits (h n : ℕ) (hn : 0 < n) :
    ∑ i ∈ range h, i / n = ∑ k ∈ range h, (h - (k + 1) * n) := by
  have hrow (i : ℕ) (hi : i < h) :
      i / n = ∑ k ∈ range h, if (k + 1) * n ≤ i then 1 else 0 := by
    rw [sum_boole]
    have he : (range h).filter (fun k => (k + 1) * n ≤ i) = range (i / n) := by
      ext k
      simp only [mem_filter, mem_range]
      rw [← Nat.le_div_iff_mul_le hn]
      have hid : i / n ≤ i := Nat.div_le_self _ _
      omega
    simp only [he, card_range, Nat.cast_id]
  calc
    _ = ∑ i ∈ range h, ∑ k ∈ range h, if (k + 1) * n ≤ i then 1 else 0 :=
      sum_congr rfl (fun i hi => hrow i (mem_range.mp hi))
    _ = ∑ k ∈ range h, ∑ i ∈ range h, if (k + 1) * n ≤ i then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro k _
      rw [sum_boole]
      have he : (range h).filter (fun i => (k + 1) * n ≤ i) = Ico ((k + 1) * n) h := by
        ext i
        simp only [mem_filter, mem_range, mem_Ico]
        omega
      simp only [he, Nat.card_Ico, Nat.cast_id]

/-- The geometric collision pair count is the sum of index quotients. -/
theorem geometricCollisionCount_eq_sum_div (h n : ℕ) :
    (∑ i : Fin h, ∑ j ∈ Ioi i, if n ∣ j.val - i.val then 1 else 0) =
      ∑ j ∈ range h, j / n := by
  have hi (i : Fin h) : Ioi i = univ.filter (fun j => i < j) := by ext j; simp
  simp_rw [hi, sum_filter]
  rw [sum_comm]
  have he (j : Fin h) :
      (∑ i : Fin h, if i < j then (if n ∣ j.val - i.val then 1 else 0) else 0) = j.val / n := by
    convert geometricCollisionCount_row h n j using 1
    apply sum_congr rfl
    intro i _
    split_ifs <;> simp_all
  simp_rw [he]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => j / n) h

/-- Geometric collisions are counted by a finite positive-part sum. -/
theorem geometricCollisionCount_eq_sum_deficits (h n : ℕ) (hn : 0 < n) :
    (∑ i : Fin h, ∑ j ∈ Ioi i, if n ∣ j.val - i.val then 1 else 0) =
      ∑ k ∈ range h, (h - (k + 1) * n) := by
  rw [geometricCollisionCount_eq_sum_div, sum_range_div_eq_sum_deficits h n hn]

end Lambert
