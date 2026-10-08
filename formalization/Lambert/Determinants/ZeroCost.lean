import Lambert.Determinants.ZeroWeights
import Lambert.Determinants.ZeroOrderMinimum
import Lambert.Arithmetic.SlotSelectionCost

/-! # Capacity constraints and endpoint costs for translated Lambert windows -/
namespace Lambert
noncomputable section
open Finset
open scoped Classical

/-- A compressed slot has capacity one before the pole window and capacity two thereafter. -/
def lambertSlotNode (k r : ℕ) : ℕ :=
  if r < k then r else k+(r-k)/2

/-- Compressed-slot node indices are nondecreasing. -/
theorem lambertSlotNode_mono (k : ℕ) : Monotone (lambertSlotNode k) := by
  intro r s hrs
  unfold lambertSlotNode
  split_ifs <;> omega

/-- Before the pole window each compressed slot has its own node. -/
theorem lambertSlotNode_of_lt (k r : ℕ) (hr : r < k) :
    lambertSlotNode k r = r := by simp [lambertSlotNode, hr]

/-- After the single-capacity prefix the compressed node is the integer half of the slot plus the window offset. -/
theorem lambertSlotNode_of_le (k r : ℕ) (hr : k ≤ r) :
    lambertSlotNode k r = (r+k)/2 := by
  unfold lambertSlotNode
  rw [if_neg (by omega)]
  omega

/-- The translated endpoint cost includes both Vandermonde row degrees and the shifted moment weight. -/
def lambertZeroCost (h k s r j : ℕ) : ℤ :=
  2*j*((h : ℤ)-1-r) + s*j + lambertZeroWeightOrder k h j

private theorem linear_sum (h : ℕ) :
    2*(∑ v ∈ range h, (v : ℤ)) = (h : ℤ)*(h-1) := by
  induction h with
  | zero => simp
  | succ h ih => rw [sum_range_succ]; push_cast; nlinarith

/-- Before every pole, the translated weight has the linear order (1-h)j. -/
theorem lambertZeroWeightOrder_before (k h j : ℕ) (hj : j ≤ k) :
    lambertZeroWeightOrder k h j = (1-(h : ℤ))*j := by
  unfold lambertZeroWeightOrder
  have he : (∑ v : Fin h, min (k+v.val) j) = h*j := by
    have hx : ∀ v : Fin h, min (k+v.val) j = j := fun v => min_eq_right (by omega)
    simp only [hx, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  rw [he]
  push_cast
  ring

/-- After every pole, the translated weight has twice the order 2j-h(2k+h-1). -/
theorem lambertZeroWeightOrder_after (k h j : ℕ) (hj : k+h ≤ j) :
    2*lambertZeroWeightOrder k h j = 2*j-(h : ℤ)*(2*k+h-1) := by
  have he : (∑ v : Fin h, min (k+v.val) j) = h*k+∑ v ∈ range h, v := by
    have hx : ∀ v : Fin h, min (k+v.val) j = k+v.val := fun v => min_eq_left (by have := v.isLt; omega)
    simp only [hx]
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      Fin.sum_univ_eq_sum_range (fun v : ℕ => v) h]
  unfold lambertZeroWeightOrder
  rw [he]
  push_cast
  have hs := linear_sum h
  nlinarith

/-- Inside a translated pole window, the weight order is an explicit quadratic in its node index. -/
theorem lambertZeroWeightOrder_inside (k h j : ℕ) (hk : k ≤ j) (hj : j ≤ k+h) :
    2*lambertZeroWeightOrder k h j =
      (j : ℤ)^2+(3-2*(k+h))*j+k*((k : ℤ)-1) := by
  have he : (∑ v : Fin h, min (k+v.val) j) =
      (j-k)*k + (∑ v ∈ range (j-k), v) + (h-(j-k))*j := by
    rw [Fin.sum_univ_eq_sum_range (fun v : ℕ => min (k+v) j) h]
    conv_lhs => rw [show h = (j-k)+(h-(j-k)) by omega, sum_range_add]
    have ha : (∑ v ∈ range (j-k), min (k+v) j) =
        (j-k)*k+∑ v ∈ range (j-k), v := by
      have hx : (∑ v ∈ range (j-k), min (k+v) j) = ∑ v ∈ range (j-k), (k+v) := by
        apply sum_congr rfl
        intro v hv
        have := mem_range.mp hv
        exact min_eq_left (by omega)
      rw [hx, sum_add_distrib, sum_const, card_range, smul_eq_mul]
    rw [ha]
    congr 1
    have hx : (∑ v ∈ range (h-(j-k)), min (k+(j-k+v)) j) =
        ∑ v ∈ range (h-(j-k)), j := by
      apply sum_congr rfl
      intro v _
      exact min_eq_right (by omega)
    rw [hx, sum_const, card_range, smul_eq_mul]
  unfold lambertZeroWeightOrder
  rw [he]
  push_cast
  rw [Nat.cast_sub hk, Nat.cast_sub (show j-k ≤ h by omega), Nat.cast_sub hk]
  have hs := linear_sum (j-k)
  rw [Nat.cast_sub hk] at hs
  nlinarith

/-- The endpoint cost for an arbitrary rank, pole interval, and moment shift. -/
def lambertSelectionCost (h k L s r j : ℕ) : ℤ :=
  2*(j : ℤ)*(h-1-r)+s*j+lambertZeroWeightOrder k L j

/-- The cost is linear before the pole interval. -/
theorem lambertSelectionCost_before (h k L s r j : ℕ) (hj : j ≤ k) :
    lambertSelectionCost h k L s r j = (2*(h : ℤ)-1-2*r+s-L)*j := by
  rw [lambertSelectionCost, lambertZeroWeightOrder_before k L j hj]
  ring

/-- The cost is quadratic inside the pole interval. -/
theorem lambertSelectionCost_inside (h k L s r j : ℕ) (hl : k ≤ j) (hu : j ≤ k+L) :
    2*lambertSelectionCost h k L s r j =
      (j : ℤ)^2+(4*h-1-4*r+2*s-2*(k+L))*j+k*((k : ℤ)-1) := by
  have he := lambertZeroWeightOrder_inside k L j hl hu
  unfold lambertSelectionCost
  nlinarith

/-- The cost is affine after the pole interval. -/
theorem lambertSelectionCost_after (h k L s r j : ℕ) (hj : k+L ≤ j) :
    2*lambertSelectionCost h k L s r j =
      2*(j : ℤ)*(2*h-1-2*r+s)-(L : ℤ)*(2*k+L-1) := by
  have he := lambertZeroWeightOrder_after k L j hj
  unfold lambertSelectionCost
  nlinarith

/-- Beyond the final pole, the cost increases for every row below the rank. -/
theorem lambertSelectionCost_tail_mono (h k L s r j : ℕ) (hr : r < h) (hj : k+L ≤ j) :
    lambertSelectionCost h k L s r (k+L) ≤ lambertSelectionCost h k L s r j := by
  have ha := lambertSelectionCost_after h k L s r (k+L) le_rfl
  have hb := lambertSelectionCost_after h k L s r j hj
  have hp := mul_nonneg (show (0 : ℤ) ≤ (j : ℤ)-(k+L) by omega)
    (show (0 : ℤ) ≤ 2*h-1-2*(r : ℤ)+s by omega)
  push_cast at ha
  nlinarith

/-- The simultaneous shift s=k turns the interior cost into the quadratic cost at translated rank and position, plus k(k-1). -/
theorem lambertZeroCost_inside (h k r j : ℕ) (hk : k ≤ j) (hj : j ≤ k+h) :
    2*lambertZeroCost h k k r j =
      lambertZeroPoleCost (h+2*k) (r+k) j + k*((k : ℤ)-1) := by
  have he := lambertZeroWeightOrder_inside k h j hk hj
  unfold lambertZeroCost lambertZeroPoleCost
  nlinarith

/-- The capacity-constrained minimizing node uses the single-node prefix and the translated quadratic minimum. -/
def lambertZeroNode (h k r : ℕ) : ℕ :=
  if r < k then r else (lambertZeroOptimalNode (h+2*k) (r+k)).toNat

/-- Every constrained minimizing node lies no later than the translated pole window. -/
theorem lambertZeroNode_bounds (h k r : ℕ) (hr : r < h) :
    lambertZeroNode h k r ≤ k+h := by
  unfold lambertZeroNode lambertZeroOptimalNode
  split_ifs <;> omega

private theorem cost_before (h k r j : ℕ) (hj : j ≤ k) :
    lambertZeroCost h k k r j = (h+k-1-2*(r : ℤ))*j := by
  have he := lambertSelectionCost_before h k h k r j hj
  simpa only [lambertSelectionCost, lambertZeroCost] using he.trans (by ring)

private theorem cost_tail (h k r j : ℕ) (hj : k+h ≤ j) :
    2*lambertZeroCost h k k r j =
      2*j*(2*h+k-1-2*(r : ℤ))-(h : ℤ)*(2*k+h-1) := by
  have he := lambertSelectionCost_after h k h k r j hj
  simpa only [lambertSelectionCost, lambertZeroCost] using he.trans (by ring)

private theorem cost_tail_mono (h k r j : ℕ) (hr : r < h) (hj : k+h ≤ j) :
    lambertZeroCost h k k r (k+h) ≤ lambertZeroCost h k k r j := by
  exact lambertSelectionCost_tail_mono h k h k r j hr hj

private theorem cost_min_inside (h k r j : ℕ) (hr : r < h)
    (hj : lambertSlotNode k r ≤ j) (hjk : j ≤ k+h) :
    lambertZeroCost h k k r (lambertZeroNode h k r) ≤
      lambertZeroCost h k k r j := by
  by_cases hrk : r < k
  · rw [lambertZeroNode, if_pos hrk]
    rw [lambertSlotNode_of_lt k r hrk] at hj
    by_cases hjk' : j ≤ k
    · rw [cost_before h k r r hrk.le, cost_before h k r j hjk']
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) (by omega)
    · have h1 : lambertZeroCost h k k r r ≤ lambertZeroCost h k k r k := by
        rw [cost_before h k r r hrk.le, cost_before h k r k le_rfl]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hrk.le) (by omega)
      apply h1.trans
      have ha := lambertZeroCost_inside h k r k le_rfl (by omega)
      have hb := lambertZeroCost_inside h k r j (by omega) hjk
      unfold lambertZeroPoleCost at ha hb
      have hp := mul_nonneg (show (0 : ℤ) ≤ (j : ℤ)-k by omega)
        (show (0 : ℤ) ≤ j+k+2*h-1-4*(r : ℤ) by omega)
      nlinarith
  · have hc : k ≤ r := by omega
    rw [lambertSlotNode_of_le k r hc] at hj
    have ho : (lambertZeroNode h k r : ℤ) = lambertZeroOptimalNode (h+2*k) (r+k) := by
      rw [lambertZeroNode, if_neg hrk, Int.toNat_of_nonneg]
      unfold lambertZeroOptimalNode
      omega
    have hok : k ≤ lambertZeroNode h k r := by
      have hh := ho
      unfold lambertZeroOptimalNode at hh
      omega
    have ha := lambertZeroCost_inside h k r (lambertZeroNode h k r) hok
      (lambertZeroNode_bounds h k r hr)
    have hb := lambertZeroCost_inside h k r j (by omega) hjk
    have hm := lambertZeroPoleCost_min (h+2*k) (r+k) j (by exact_mod_cast hj)
    rw [ho] at ha
    omega

/-- The selected node minimizes the translated zero-place cost among all nodes allowed by the single-then-double capacity constraint. -/
theorem lambertZeroCost_min (h k r j : ℕ) (hr : r < h)
    (hj : lambertSlotNode k r ≤ j) :
    lambertZeroCost h k k r (lambertZeroNode h k r) ≤
      lambertZeroCost h k k r j := by
  by_cases hji : j ≤ k+h
  · exact cost_min_inside h k r j hr hj hji
  · apply (cost_min_inside h k r (k+h) hr ?_ le_rfl).trans
      (cost_tail_mono h k r j hr (by omega))
    unfold lambertSlotNode
    split_ifs <;> omega

/-- The translated zero-pole exponent is minus the sum of its capacity-constrained minimum costs. -/
def lambertZeroExponent (h k : ℕ) : ℤ :=
  -∑ r : Fin h, lambertZeroCost h k k r.val (lambertZeroNode h k r.val)

end
end Lambert
