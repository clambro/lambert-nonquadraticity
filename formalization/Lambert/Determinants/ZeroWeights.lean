import Lambert.Determinants.ZeroLocal
import Lambert.Arithmetic.FactoredFinitePart

/-! # Finite-part weights at zero for translated pole windows -/
namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
variable {K : Type*} [Field K]

/-- The local weight order is the node index minus the sum of its minimum with each pole index. -/
def lambertZeroWeightOrder (k h j : ℕ) : ℤ :=
  (j : ℤ) - ∑ v : Fin h, (min (k+v.val) j : ℕ)

/-- At a pole in a translated window, the complementary denominator has valuation equal to the exponential of the node weight order. -/
theorem lambertZero_complement_valuation (k h : ℕ) (j : Fin h) :
    Valued.v ((complementaryNodal (fun v : Fin h => lambertZeroBase K ^ (k+v.val)) j).eval
      (lambertZeroBase K ^ (k+j.val))) = WithZero.exp (lambertZeroWeightOrder k h (k+j.val)) := by
  simp only [complementaryNodal, Lagrange.nodal, eval_prod, eval_sub, eval_X, eval_C]
  rw [lambertZeroDifferenceProduct_valuation _ (fun v : Fin h => k+v.val) (k+j.val) (by
    intro v hv he
    exact (mem_erase.mp hv).1 (Fin.ext (Nat.add_left_cancel he)))]
  congr 1
  have he := sum_erase_add (s := (univ : Finset (Fin h)))
    (fun v => ((min (k+v.val) (k+j.val) : ℕ) : ℤ)) (mem_univ j)
  simp only [min_self] at he
  unfold lambertZeroWeightOrder
  push_cast at he ⊢
  omega

/-- The scaled logarithmic derivative of a translated complementary pole denominator has nonnegative order. -/
theorem lambertZero_logDerivative_valuation (k h : ℕ) (j : Fin h) :
    let q := lambertZeroBase K
    let D := complementaryNodal (fun v : Fin h => q ^ (k+v.val)) j
    Valued.v (q ^ (k+j.val) * D.derivative.eval (q ^ (k+j.val)) / D.eval (q ^ (k+j.val))) ≤ 1 := by
  dsimp only
  unfold complementaryNodal Lagrange.nodal
  apply linearFactorProduct_logDerivative_valuation_le (univ.erase j)
    (fun v : Fin h => lambertZeroBase K ^ (k+v.val)) (lambertZeroBase K ^ (k+j.val))
  · intro v hv
    exact lambertZeroBase_pow_injective.ne
      (fun he => (mem_erase.mp hv).1 (Fin.ext (Nat.add_left_cancel he.symm)))
  · intro v hv
    rw [map_div₀, lambertZeroBase_pow_valuation,
      lambertZeroBase_sub_valuation (k+j.val) (k+v.val) (by
        intro he
        exact (mem_erase.mp hv).1 (Fin.ext (Nat.add_left_cancel he.symm))),
      ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
    have := Nat.min_le_left (k+j.val) (k+v.val)
    omega

/-- The evaluation weight at a translated pole includes the common residue correction. -/
def lambertZeroEvaluationWeight (Z : LaurentSeries K) (k h : ℕ) (j : Fin h) : LaurentSeries K :=
  let q := lambertZeroBase K
  let D := complementaryNodal (fun v : Fin h => q ^ (k+v.val)) j
  (q ^ (k+j.val) * D.derivative.eval (q ^ (k+j.val)) / D.eval (q ^ (k+j.val)) - Z) /
    D.eval (q ^ (k+j.val))

/-- At translated poles the corrected evaluation weight obeys its exact complementary-denominator order bound. -/
theorem lambertZeroEvaluationWeight_valuation (Z : LaurentSeries K) (hZ : Valued.v Z ≤ 1)
    (k h : ℕ) (j : Fin h) :
    Valued.v (lambertZeroEvaluationWeight Z k h j) ≤
      WithZero.exp (-lambertZeroWeightOrder k h (k+j.val)) := by
  have hl := lambertZero_logDerivative_valuation (K := K) k h j
  unfold lambertZeroEvaluationWeight
  dsimp only at hl ⊢
  rw [map_div₀, lambertZero_complement_valuation]
  calc
    _ ≤ 1 / WithZero.exp (lambertZeroWeightOrder k h (k+j.val)) :=
      div_le_div_of_nonneg_right (Valuation.map_sub_le Valued.v hl hZ) WithZero.exp_pos.le
    _ = _ := by rw [one_div, ← WithZero.exp_neg]

/-- The evaluation coefficient uses a finite-part weight inside the pole window and ordinary evaluation outside it. -/
def lambertZeroBlockW (Z : LaurentSeries K) (k h j : ℕ) : LaurentSeries K :=
  if hj : k ≤ j ∧ j < k+h then lambertZeroEvaluationWeight Z k h ⟨j-k, by omega⟩
  else -(lambertZeroBase K ^ j) /
    (Lagrange.nodal univ (fun v : Fin h => lambertZeroBase K ^ (k+v.val))).eval (lambertZeroBase K ^ j)

/-- The scaled-derivative coefficient vanishes outside the translated pole window. -/
def lambertZeroBlockC (K : Type*) [Field K] (k h j : ℕ) : LaurentSeries K :=
  if hj : k ≤ j ∧ j < k+h then -1 /
    (complementaryNodal (fun v : Fin h => lambertZeroBase K ^ (k+v.val)) ⟨j-k, by omega⟩).eval
      (lambertZeroBase K ^ j)
  else 0

/-- Both translated finite-part weights satisfy their common minimum-sum order bound. -/
theorem lambertZeroBlock_weights (Z : LaurentSeries K) (hZ : Valued.v Z ≤ 1) (k h j : ℕ) :
    Valued.v (lambertZeroBlockW Z k h j) ≤ WithZero.exp (-lambertZeroWeightOrder k h j) ∧
    Valued.v (lambertZeroBlockC K k h j) ≤ WithZero.exp (-lambertZeroWeightOrder k h j) := by
  unfold lambertZeroBlockW lambertZeroBlockC
  split_ifs with hj
  · have he : k+(j-k) = j := by omega
    constructor
    · simpa only [he] using lambertZeroEvaluationWeight_valuation Z hZ k h ⟨j-k, by omega⟩
    · have hd := lambertZero_complement_valuation (K := K) k h ⟨j-k, by omega⟩
      simp only [he] at hd
      rw [map_div₀, Valuation.map_neg, map_one, hd, one_div, ← WithZero.exp_neg]
  · constructor
    · rw [map_div₀, Valuation.map_neg, lambertZeroBase_pow_valuation]
      have hd : Valued.v ((Lagrange.nodal univ
          (fun v : Fin h => lambertZeroBase K ^ (k+v.val))).eval (lambertZeroBase K ^ j)) =
          WithZero.exp (-(∑ v : Fin h, ((min (k+v.val) j : ℕ) : ℤ))) := by
        simp only [Lagrange.nodal, eval_prod, eval_sub, eval_X, eval_C]
        apply lambertZeroDifferenceProduct_valuation
        intro v _ he
        have := v.isLt
        omega
      rw [hd, ← WithZero.exp_sub]
      apply le_of_eq
      congr 1
      unfold lambertZeroWeightOrder
      push_cast
      ring
    · rw [map_zero]; exact zero_le

end
end Lambert
