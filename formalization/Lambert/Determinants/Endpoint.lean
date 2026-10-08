import Lambert.Determinants.ZeroCost

/-! # Exact zero-endpoint exponent of the main determinant family -/
namespace Lambert
noncomputable section
open Finset


private theorem quadratic_sum (a b : ℤ) (s : ℕ) :
    6*(∑ i ∈ range s, (i : ℤ)*(a+b*i)) =
      3*a*s*(s-1)+b*s*(s-1)*(2*s-1) := by
  induction s with
  | zero => simp
  | succ s ih => rw [sum_range_succ]; push_cast; linear_combination ih


/-- The zero-place pole exponent for rank 60N and equal shifts 3N is 10023N³+90N²-10N. -/
theorem lambertMain_zero (N : ℕ) :
    lambertZeroExponent (60*N) (3*N) = 10023*(N : ℤ)^3+90*N^2-10*N := by
  let f : ℕ → ℤ := fun r => lambertZeroPoleCost (66*N) r (lambertZeroOptimalNode (66*N) r)
  let c : ℕ → ℤ := fun r =>
    2*lambertZeroCost (60*N) (3*N) (3*N) r (lambertZeroNode (60*N) (3*N) r)
  have htotal : 6*(∑ r ∈ range (66*N), f r) = -18*(22*(N : ℤ))^3+6*(22*N) := by
    have he := lambertZeroOptimalCost_sum (22*N) 0 (by omega)
    norm_num [← mul_assoc] at he
    convert he using 1
    ring
  have hlow : (∑ r ∈ range (6*N), f r) =
      ∑ i ∈ range (3*N), (i : ℤ)*(264*N-6-14*i) := by
    rw [show 6*N=2*(3*N) by omega, sum_range_pairs]
    apply sum_congr rfl
    intro i hi
    have hi := mem_range.mp hi
    have h0 : lambertZeroOptimalNode (66*N) (2*i) = i := by unfold lambertZeroOptimalNode; omega
    have h1 : lambertZeroOptimalNode (66*N) (2*i+1) = i := by unfold lambertZeroOptimalNode; omega
    dsimp [f]
    rw [h0, h1]
    unfold lambertZeroPoleCost
    ring
  have htail : (∑ t ∈ range (3*N), f (63*N+t)) =
      ∑ t ∈ range (3*N), -((60*(N : ℤ)+2*t)*(60*N+2*t+1)) := by
    apply sum_congr rfl
    intro t ht
    have ht := mem_range.mp ht
    have ho : lambertZeroOptimalNode (66*N) (63*N+t) = 60*N+2*t := by
      unfold lambertZeroOptimalNode
      omega
    dsimp [f]
    rw [ho]
    unfold lambertZeroPoleCost
    ring
  have hprefix : (∑ r ∈ range (3*N), c r) =
      ∑ r ∈ range (3*N), (r : ℤ)*(126*N-2-4*r) := by
    apply sum_congr rfl
    intro r hr
    have hr := mem_range.mp hr
    dsimp [c]
    rw [lambertZeroNode, if_pos hr, lambertZeroCost,
      lambertZeroWeightOrder_before _ _ _ hr.le]
    push_cast
    ring
  have hmiddle : (∑ t ∈ range (57*N), c (3*N+t)) =
      (∑ t ∈ range (57*N), f (6*N+t)) + 57*N*(3*(N : ℤ)*(3*N-1)) := by
    have hc (t : ℕ) (ht : t < 57*N) : c (3*N+t) = f (6*N+t)+3*(N : ℤ)*(3*N-1) := by
      have ho : (lambertZeroNode (60*N) (3*N) (3*N+t) : ℤ) =
          lambertZeroOptimalNode (66*N) (6*N+t) := by
        rw [lambertZeroNode, if_neg (by omega), Int.toNat_of_nonneg]
        · congr 1 <;> push_cast <;> ring
        · unfold lambertZeroOptimalNode; omega
      have hk : 3*N ≤ lambertZeroNode (60*N) (3*N) (3*N+t) := by
        have hh := ho
        unfold lambertZeroOptimalNode at hh
        omega
      dsimp [c]
      rw [lambertZeroCost_inside _ _ _ _ hk
        (lambertZeroNode_bounds _ _ _ (by omega)), ho]
      dsimp [f]
      congr 2 <;> ring
    rw [sum_congr rfl (fun t ht => hc t (mem_range.mp ht))]
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
    push_cast
    ring
  have hsplit : (∑ r ∈ range (66*N), f r) =
      (∑ r ∈ range (6*N), f r)+(∑ t ∈ range (57*N), f (6*N+t))+
        ∑ t ∈ range (3*N), f (63*N+t) := by
    rw [show 66*N=63*N+3*N by omega, sum_range_add]
    rw [show 63*N=6*N+57*N by omega, sum_range_add]
  have hcsplit : (∑ r ∈ range (60*N), c r) =
      (∑ r ∈ range (3*N), c r)+(∑ t ∈ range (57*N), c (3*N+t)) := by
    rw [show 60*N=3*N+57*N by omega, sum_range_add]
  have hc : (∑ r ∈ range (60*N), c r) = -2*lambertZeroExponent (60*N) (3*N) := by
    rw [← Fin.sum_univ_eq_sum_range]
    dsimp [c, lambertZeroExponent]
    rw [← mul_sum]
    ring
  have hl := quadratic_sum (264*(N : ℤ)-6) (-14) (3*N)
  have hp := quadratic_sum (126*(N : ℤ)-2) (-4) (3*N)
  have ht := six_mul_sum_neg_consecutive (60*(N : ℤ)) (3*N)
  have hl' : (∑ i ∈ range (3*N), (i : ℤ)*(264*N-6-14*i)) =
      ∑ i ∈ range (3*N), (i : ℤ)*(264*N-6+(-14)*i) := by apply sum_congr rfl; intro i _; ring
  have hp' : (∑ i ∈ range (3*N), (i : ℤ)*(126*N-2-4*i)) =
      ∑ i ∈ range (3*N), (i : ℤ)*(126*N-2+(-4)*i) := by apply sum_congr rfl; intro i _; ring
  rw [hl'] at hlow
  rw [hp'] at hprefix
  rw [hlow, htail] at hsplit
  rw [hprefix, hmiddle, hc] at hcsplit
  push_cast at hl hp ht hcsplit
  nlinarith

end
end Lambert
