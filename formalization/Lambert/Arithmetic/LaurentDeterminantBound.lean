import Lambert.Arithmetic.LaurentSeriesLocalOrder
import Lambert.Arithmetic.RectangularDeterminant
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Laurent determinant bounds from integer entry costs

Nonarchimedean valuation bounds combine multiplicatively on permutation terms.
Rearrangement controls monomial evaluation matrices without a product formula.
-/

namespace Lambert
noncomputable section
open Finset Matrix
open scoped Classical WithZero
variable {K : Type*} [Field K]

/-- Integer lower orders add under finite products of Laurent series. -/
theorem laurentProduct_valuation_le {ι : Type*} (s : Finset ι)
    (a : ι → LaurentSeries K) (d : ι → ℤ)
    (ha : ∀ i ∈ s, Valued.v (a i) ≤ WithZero.exp (-d i)) :
    Valued.v (∏ i ∈ s, a i) ≤ WithZero.exp (-(∑ i ∈ s, d i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, map_mul, neg_add, WithZero.exp_add]
    exact mul_le_mul' (ha i (mem_insert_self _ _))
      (ih (fun j hj => ha j (mem_insert_of_mem hj)))

/-- Lower bounds for all permutation costs imply the same lower order for
a Laurent determinant. -/
theorem laurentDeterminant_valuation_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (LaurentSeries K)) (d : ι → ι → ℤ) (D : ℤ)
    (ha : ∀ i j, Valued.v (A i j) ≤ WithZero.exp (-d i j))
    (hd : ∀ σ : Equiv.Perm ι, D ≤ ∑ j, d (σ j) j) :
    Valued.v A.det ≤ WithZero.exp (-D) := by
  rw [Matrix.det_apply']
  apply Valuation.map_sum_le
  intro σ _
  have hp := laurentProduct_valuation_le univ (fun j => A (σ j) j)
    (fun j => d (σ j) j) (fun j _ => ha (σ j) j)
  have hs : Valued.v (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : LaurentSeries K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with he | he <;> simp [he]
  rw [map_mul, hs, one_mul]
  exact hp.trans (WithZero.exp_le_exp.mpr (neg_le_neg (hd σ)))

/-- A sorted node list minimizes its pairing with distinct row degrees in
reverse order. -/
theorem sortedNode_rearrangement {h : ℕ} (j : Fin h → ℤ) (hj : Monotone j)
    (σ : Equiv.Perm (Fin h)) :
    (∑ r, j r * ((h : ℤ) - 1 - r.val)) ≤ ∑ r, j r * (σ r).val := by
  have ha : Antitone (fun r : Fin h => (h : ℤ) - 1 - r.val) := by
    intro r s hrs
    have : r.val ≤ s.val := hrs
    dsimp only
    omega
  have he := (hj.antivary ha).sum_mul_le_sum_mul_comp_perm
    (σ := σ.trans Fin.revPerm)
  have hv (r : Fin h) : (h : ℤ) - 1 - ((Fin.rev (σ r)).val : ℤ) = (σ r).val := by
    rw [Fin.val_rev, Nat.cast_sub (by have := (σ r).isLt; omega)]
    push_cast
    ring
  simp only [Equiv.trans_apply, Fin.revPerm_apply, hv] at he
  exact he

/-- A rectangular product has a prescribed lower determinant order if every
injective selection and every permutation has at least that total entry cost. -/
theorem laurentRectangularDeterminant_valuation_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ (LaurentSeries K)) (B : Matrix κ ι (LaurentSeries K))
    (a : ι → κ → ℤ) (b : κ → ι → ℤ) (D : ℤ)
    (ha : ∀ i j, Valued.v (A i j) ≤ WithZero.exp (-a i j))
    (hb : ∀ i j, Valued.v (B i j) ≤ WithZero.exp (-b i j))
    (hd : ∀ f : ι → κ, Function.Injective f → ∀ σ : Equiv.Perm ι,
      D ≤ ∑ j, (a (σ j) (f j) + b (f j) j)) :
    Valued.v (A * B).det ≤ WithZero.exp (-D) := by
  rw [rectangular_det_expansion]
  apply Valuation.map_sum_le
  intro f _
  by_cases hf : Function.Injective f
  · have he : (Matrix.of fun i j => A i (f j)).det * (∏ j, B (f j) j) =
        (Matrix.of fun i j => A i (f j) * B (f j) j).det := by
      have ht := Matrix.det_mul_row (fun j => B (f j) j) (Matrix.of fun i j => A i (f j))
      simpa only [Matrix.of_apply, mul_comm] using ht.symm
    rw [he]
    apply laurentDeterminant_valuation_le _ (fun i j => a i (f j) + b (f j) j) D
    · intro i j
      rw [Matrix.of_apply, map_mul, neg_add, WithZero.exp_add]
      exact mul_le_mul' (ha i (f j)) (hb (f j) j)
    · exact hd f hf
  · rw [rectangular_det_selection_zero A f hf, zero_mul, map_zero]
    exact zero_le

end
end Lambert
