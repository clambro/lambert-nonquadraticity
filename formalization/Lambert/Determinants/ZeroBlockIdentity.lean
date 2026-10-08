import Lambert.Determinants.ZeroBlock
import Lambert.Determinants.FinitePart

/-! # Identification of compressed blocks with translated finite-part moments -/
namespace Lambert
noncomputable section
open Polynomial Finset Matrix
open scoped Classical WithZero Topology
variable {K : Type*} [Field K]

private theorem scaled_monomial_derivative (a : K) (r : ℕ) :
    a*(X^r : K[X]).derivative.eval a = (r : K)*a^r := by
  cases r with
  | zero => simp
  | succ r =>
    rw [derivative_X_pow_succ]
    simp only [eval_mul, eval_C, eval_pow, eval_X, pow_succ, Nat.cast_add, Nat.cast_one]
    ring

private theorem block_atom (Z : LaurentSeries K) (k h r j : ℕ) :
    (lambertZeroBlockW Z k h j+(r : LaurentSeries K)*lambertZeroBlockC K k h j)*
        lambertZeroBase K ^ (r*j) =
      -(lambertZeroBase K ^ j)*nodalFiniteValue
        (fun v : Fin h => lambertZeroBase K ^ (k+v.val)) (lambertZeroBase K ^ j) (X^r) -
      (if hj : k ≤ j ∧ j < k+h then Z*(Lagrange.nodalWeight univ
        (fun v : Fin h => lambertZeroBase K ^ (k+v.val)) ⟨j-k, by omega⟩ *
          lambertZeroBase K ^ (r*j)) else 0) := by
  let q := lambertZeroBase K
  let x : Fin h → LaurentSeries K := fun v => q^(k+v.val)
  have hx : Function.Injective x := by
    intro u v he
    exact Fin.ext (Nat.add_left_cancel (lambertZeroBase_pow_injective he))
  by_cases hj : k ≤ j ∧ j < k+h
  · let v : Fin h := ⟨j-k, by omega⟩
    have hj' : k+(j-k)=j := by omega
    have hvx : x v = q^j := by dsimp [x, v]; rw [hj']
    have hn : (complementaryNodal x v).eval (q^j) ≠ 0 := by
      rw [← hvx]
      apply Lagrange.eval_nodal_not_at_node
      intro u hu
      exact hx.ne (mem_erase.mp hu).1.symm
    have hd := scaled_monomial_derivative (q^j) r
    have hv := nodalFiniteValue_at_node x hx v (X^r)
    rw [hvx] at hv
    change _ = -q^j*nodalFiniteValue x (q^j) (X^r)-_
    rw [hv, nodalFinitePart_apply, hvx]
    simp only [lambertZeroBlockW, lambertZeroBlockC, dif_pos hj,
      lambertZeroEvaluationWeight, hj', Lagrange.nodalWeight_eq_eval_nodal_erase_inv,
      eval_pow, eval_X]
    change ((q^j*(complementaryNodal x v).derivative.eval (q^j) /
      (complementaryNodal x v).eval (q^j)-Z)/(complementaryNodal x v).eval (q^j)+
      (r : LaurentSeries K)*(-1/(complementaryNodal x v).eval (q^j)))*q^(r*j) =
      -q^j*((X^r : (LaurentSeries K)[X]).derivative.eval (q^j)/(complementaryNodal x v).eval (q^j)-
        (q^j)^r*(complementaryNodal x v).derivative.eval (q^j)/(complementaryNodal x v).eval (q^j)^2)-
        Z*(((complementaryNodal x v).eval (q^j))⁻¹*q^(r*j))
    have hp : q^(r*j)=(q^j)^r := by rw [← pow_mul, Nat.mul_comm]
    rw [hp]
    field_simp [hn]
    linear_combination (complementaryNodal x v).eval (q^j)*hd
  · have ha : ∀ v : Fin h, q^j ≠ x v := by
      intro v
      exact lambertZeroBase_pow_injective.ne (by have := v.isLt; omega)
    rw [dif_neg hj]
    simp only [lambertZeroBlockW, lambertZeroBlockC, dif_neg hj,
      mul_zero, add_zero, sub_zero]
    rw [nodalFiniteValue_regular _ hx _ ha, eval_pow, eval_X]
    change _*q^(r*j)=_
    rw [← pow_mul, Nat.mul_comm j r]
    ring

/-- Once the truncation contains the complete translated pole window, its compressed block moment equals the nodal finite-part functional. -/
theorem lambertZeroBlockMoment_eq_truncated (Z : LaurentSeries K) (k h N r : ℕ)
    (hN : k+h ≤ N) :
    lambertZeroBlockMoment Z k h N r =
      lambertTruncatedNodal (lambertZeroBase K) Z k h N (X^r) := by
  let q := lambertZeroBase K
  let c : ℕ → LaurentSeries K := fun j =>
    if hj : k ≤ j ∧ j < k+h then Z*(Lagrange.nodalWeight univ
      (fun v : Fin h => q^(k+v.val)) ⟨j-k, by omega⟩*q^(r*j)) else 0
  have hc : (∑ j ∈ range N, c j) =
      Z*∑ v : Fin h, Lagrange.nodalWeight univ (fun v : Fin h => q^(k+v.val)) v*
        (X^r).eval (q^(k+v.val)) := by
    have hs : (∑ j ∈ range (k+h), c j) = ∑ j ∈ range N, c j := by
      apply sum_subset (range_mono hN)
      intro j _ hj
      have := mem_range.not.mp hj
      simp only [c, dif_neg (show ¬(k ≤ j ∧ j < k+h) by omega)]
    rw [← hs, sum_range_add]
    have hz : (∑ j ∈ range k, c j)=0 := by
      apply sum_eq_zero
      intro j hj
      have := mem_range.mp hj
      simp only [c, dif_neg (show ¬(k ≤ j ∧ j < k+h) by omega)]
    rw [hz, zero_add, mul_sum, ← Fin.sum_univ_eq_sum_range (fun j => c (k+j)) h]
    apply sum_congr rfl
    intro v _
    have hv : k ≤ k+v.val ∧ k+v.val < k+h := by have := v.isLt; omega
    simp only [c, dif_pos hv, Nat.add_sub_cancel_left, eval_pow, eval_X]
    rw [← pow_mul, Nat.mul_comm]
  unfold lambertZeroBlockMoment
  simp_rw [block_atom]
  change (∑ j ∈ range N, (-(q^j)*nodalFiniteValue (fun v : Fin h => q^(k+v.val))
    (q^j) (X^r)-c j)) = _
  rw [sum_sub_distrib, hc]
  simp only [lambertTruncatedNodal, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, Polynomial.leval_apply, smul_eq_mul,
    neg_mul, sum_neg_distrib]
  rfl

end
end Lambert
