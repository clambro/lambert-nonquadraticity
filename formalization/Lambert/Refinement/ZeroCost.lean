import Lambert.Determinants.ZeroCost

/-! # Quadratic zero-endpoint bounds for the selected rectangular family -/
namespace Lambert
noncomputable section
open Finset
open scoped Classical

/-- The selected rectangular family's zero-endpoint cost combines its rank, moment shift, and 516N pole weights. -/
def lambertRefinementZeroCost (N r j : ℕ) : ℤ :=
  2 * (j : ℤ) * (500 * N - 1 - r) + 41 * N * j +
    lambertZeroWeightOrder (27 * N) (516 * N) j

/-- Three quadratic pieces lower-bound eight times the capacity-constrained endpoint cost. -/
def lambertRefinementZeroQuadratic (N r : ℕ) : ℤ :=
  if r < 27 * N then 8 * (525 * (N : ℤ) - 1 - 2 * r) * r
  else if r < 341 * N then
    ((r : ℤ) + 27 * N - 1) ^ 2 +
      2 * (996 * N - 1 - 4 * r) * (r + 27 * N - 1) + 4 * (27 * N) * (27 * N - 1)
  else 4 * (27 * (N : ℤ)) * (27 * N - 1) - (996 * N - 1 - 4 * r) ^ 2

private theorem cost_before (N r j : ℕ) (hj : j ≤ 27 * N) :
    lambertRefinementZeroCost N r j = (525 * (N : ℤ) - 1 - 2 * r) * j := by
  have he := lambertSelectionCost_before (500*N) (27*N) (516*N) (41*N) r j hj
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at he
  simpa only [lambertSelectionCost, lambertRefinementZeroCost, Nat.cast_mul, Nat.cast_ofNat] using
    he.trans (by ring)

private theorem cost_inside (N r j : ℕ) (hl : 27 * N ≤ j) (hu : j ≤ 543 * N) :
    2 * lambertRefinementZeroCost N r j =
      (j : ℤ) ^ 2 + (996 * N - 1 - 4 * r) * j + (27 * N) * (27 * N - 1) := by
  have he := lambertSelectionCost_inside (500*N) (27*N) (516*N) (41*N) r j hl (by omega)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at he
  simpa only [lambertSelectionCost, lambertRefinementZeroCost, Nat.cast_mul, Nat.cast_ofNat] using
    he.trans (by ring)

private theorem cost_after (N r j : ℕ) (hj : 543 * N ≤ j) :
    2 * lambertRefinementZeroCost N r j =
      2 * (j : ℤ) * (1041 * N - 1 - 2 * r) - (516 * N) * (570 * N - 1) := by
  have he := lambertSelectionCost_after (500*N) (27*N) (516*N) (41*N) r j (by omega)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at he
  simpa only [lambertSelectionCost, lambertRefinementZeroCost, Nat.cast_mul, Nat.cast_ofNat] using
    he.trans (by ring)

private theorem cost_tail_mono (N r j : ℕ) (hr : r < 500 * N) (hj : 543 * N ≤ j) :
    lambertRefinementZeroCost N r (543 * N) ≤ lambertRefinementZeroCost N r j := by
  have he := lambertSelectionCost_tail_mono (500*N) (27*N) (516*N) (41*N) r j hr (by omega)
  simpa only [lambertSelectionCost, lambertRefinementZeroCost, show 27*N+516*N=543*N by omega,
    Nat.cast_mul, Nat.cast_ofNat] using he

private theorem cost_bound_inside (N r j : ℕ) (hr : r < 500 * N)
    (hj : lambertSlotNode (27 * N) r ≤ j) (hu : j ≤ 543 * N) :
    lambertRefinementZeroQuadratic N r ≤ 8 * lambertRefinementZeroCost N r j := by
  have hr' : (r : ℤ) < 500 * N := by exact_mod_cast hr
  by_cases hk : r < 27 * N
  · rw [lambertRefinementZeroQuadratic, if_pos hk]
    rw [lambertSlotNode_of_lt _ _ hk] at hj
    have hk' : (r : ℤ) < 27 * N := by exact_mod_cast hk
    have hj' : (r : ℤ) ≤ j := by exact_mod_cast hj
    by_cases hjk : j ≤ 27 * N
    · rw [cost_before N r j hjk]
      have hp := mul_nonneg (show (0 : ℤ) ≤ j - r by omega)
        (show (0 : ℤ) ≤ 525 * N - 1 - 2 * r by omega)
      nlinarith
    · have ha := cost_inside N r j (by omega) hu
      have hb := cost_inside N r (27 * N) le_rfl (by omega)
      rw [cost_before N r (27 * N) le_rfl] at hb
      have hjk' : (27 : ℤ) * N ≤ j := by exact_mod_cast (show 27 * N ≤ j by omega)
      push_cast at hb
      have hp := mul_nonneg (show (0 : ℤ) ≤ j - 27 * N by omega)
        (show (0 : ℤ) ≤ j + 27 * N + (996 * N - 1 - 4 * r) by omega)
      have hp' := mul_nonneg (show (0 : ℤ) ≤ 27 * N - r by omega)
        (show (0 : ℤ) ≤ 525 * N - 1 - 2 * r by omega)
      nlinarith
  · have hk' : 27 * N ≤ r := by omega
    rw [lambertSlotNode_of_le _ _ hk'] at hj
    have hl : 27 * N ≤ j := by omega
    have ha := cost_inside N r j hl hu
    have hc : (r : ℤ) + 27 * N - 1 ≤ 2 * j := by omega
    rw [lambertRefinementZeroQuadratic, if_neg hk]
    by_cases hm : r < 341 * N
    · rw [if_pos hm]
      have hm' : (r : ℤ) < 341 * N := by exact_mod_cast hm
      have hp := mul_nonneg (show (0 : ℤ) ≤ 2 * j - (r + 27 * N - 1) by omega)
        (show (0 : ℤ) ≤ 2 * j + (r + 27 * N - 1) + 2 * (996 * N - 1 - 4 * r) by omega)
      nlinarith
    · rw [if_neg hm]
      nlinarith [sq_nonneg (2 * (j : ℤ) + (996 * N - 1 - 4 * r))]

/-- The three-piece quadratic bound holds at every node permitted by the compressed capacity constraint. -/
theorem lambertRefinementZeroQuadratic_le_cost (N r j : ℕ) (hr : r < 500 * N)
    (hj : lambertSlotNode (27 * N) r ≤ j) :
    lambertRefinementZeroQuadratic N r ≤ 8 * lambertRefinementZeroCost N r j := by
  by_cases hu : j ≤ 543 * N
  · exact cost_bound_inside N r j hr hj hu
  · have hl : lambertSlotNode (27 * N) r ≤ 543 * N := by
      unfold lambertSlotNode
      split_ifs <;> omega
    exact (cost_bound_inside N r (543 * N) hr hl le_rfl).trans
      (mul_le_mul_of_nonneg_left (cost_tail_mono N r j hr (by omega)) (by norm_num))

/-- The three-piece quadratic endpoint bound has an explicit cubic sum with all lower-order terms retained. -/
theorem lambertRefinementZeroQuadratic_sum (N : ℕ) :
    3 * (∑ r ∈ range (500 * N), lambertRefinementZeroQuadratic N r) =
      -141020912 * (N : ℤ) ^ 3 - 593682 * N ^ 2 + 110 * N := by
  let P := lambertRefinementZeroQuadratic N
  have he : (∑ r ∈ range (500 * N), P r) =
      (∑ r ∈ Ico 0 (27 * N), P r) + (∑ r ∈ Ico (27 * N) (341 * N), P r) +
        (∑ r ∈ Ico (341 * N) (500 * N), P r) := by
    rw [sum_Ico_consecutive P (by omega : 0 ≤ 27 * N) (by omega),
      sum_Ico_consecutive P (by omega : 0 ≤ 341 * N) (by omega), Nat.Ico_zero_eq_range]
  have h₀ : (∑ r ∈ Ico 0 (27 * N), P r) =
      ∑ r ∈ Ico 0 (27 * N), ((-16 : ℤ) * r ^ 2 + (4200 * N - 8) * r + 0) := by
    apply sum_congr rfl
    intro r hr
    dsimp [P, lambertRefinementZeroQuadratic]
    rw [if_pos (mem_Ico.mp hr).2]
    ring
  have h₁ : (∑ r ∈ Ico (27 * N) (341 * N), P r) =
      ∑ r ∈ Ico (27 * N) (341 * N), ((-7 : ℤ) * r ^ 2 + (1830 * N + 4) * r +
        (27 * N - 1) * (2127 * N - 3)) := by
    apply sum_congr rfl
    intro r hr
    dsimp [P, lambertRefinementZeroQuadratic]
    rw [if_neg (by have := (mem_Ico.mp hr).1; omega), if_pos (mem_Ico.mp hr).2]
    ring
  have h₂ : (∑ r ∈ Ico (341 * N) (500 * N), P r) =
      ∑ r ∈ Ico (341 * N) (500 * N), ((-16 : ℤ) * r ^ 2 + (7968 * N - 8) * r +
        (4 * (27 * N) * (27 * N - 1) - (996 * N - 1) ^ 2)) := by
    apply sum_congr rfl
    intro r hr
    dsimp [P, lambertRefinementZeroQuadratic]
    have hl := (mem_Ico.mp hr).1
    rw [if_neg (by omega), if_neg (by omega)]
    ring
  have q₀ := six_mul_sum_quadratic_Ico (-16 : ℤ) (4200 * N - 8) 0
    0 (27 * N) (by omega)
  have q₁ := six_mul_sum_quadratic_Ico (-7 : ℤ) (1830 * N + 4)
    ((27 * N - 1) * (2127 * N - 3)) (27 * N) (341 * N) (by omega)
  have q₂ := six_mul_sum_quadratic_Ico (-16 : ℤ) (7968 * N - 8)
    (4 * (27 * N) * (27 * N - 1) - (996 * N - 1) ^ 2) (341 * N) (500 * N) (by omega)
  have hs : 6 * (∑ r ∈ range (500 * N), P r) =
      -282041824 * (N : ℤ) ^ 3 - 1187364 * N ^ 2 + 220 * N := by
    rw [he, h₀, h₁, h₂]
    push_cast at q₀ q₁ q₂
    linear_combination q₀ + q₁ + q₂
  change 3 * (∑ r ∈ range (500 * N), P r) = _
  nlinarith

/-- A nonnegative integer ceiling suffices for the unnormalized rectangular family's zero-pole exponent. -/
def lambertRefinementZeroExponent (N : ℕ) : ℕ :=
  (141020912 * N ^ 3 + 593682 * N ^ 2 + 23) / 24

/-- The integer zero-pole exponent dominates the negative sum of the quadratic endpoint bounds. -/
theorem lambertRefinementZeroExponent_bound (N : ℕ) :
    -(8 * (lambertRefinementZeroExponent N : ℤ)) ≤
      ∑ r ∈ range (500 * N), lambertRefinementZeroQuadratic N r := by
  have hs := lambertRefinementZeroQuadratic_sum N
  have he : 141020912 * N ^ 3 + 593682 * N ^ 2 ≤ 24 * lambertRefinementZeroExponent N := by
    unfold lambertRefinementZeroExponent
    omega
  have he' : 141020912 * (N : ℤ) ^ 3 + 593682 * N ^ 2 ≤ 24 * lambertRefinementZeroExponent N := by
    exact_mod_cast he
  nlinarith

end
end Lambert
