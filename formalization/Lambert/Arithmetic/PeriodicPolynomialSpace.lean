import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Weighted periodic polynomial spaces

On each residue class, these spaces contain polynomials of bounded degree
multiplied by one of a fixed finite family of weight functions.
-/

namespace Lambert

noncomputable section

open Finset

variable {K : Type*} [Field K]

/-- A weighted periodic monomial vanishes off its residue class and equals a
power of the index times the specified weight on that class. -/
def periodicWeightedMonomial (n : ℕ) (w : ℕ → K) (c d i : ℕ) : K :=
  if i % n = c then (i : K) ^ d * w i else 0

/-- Weighted periodic polynomials are spanned by residue-class monomials of
bounded degree multiplied by one of a fixed finite family of weights. -/
def periodicPolynomialSpace {α : Type*} (h n r : ℕ) (w : α → ℕ → K) :
    Submodule K (Fin h → K) :=
  Submodule.span K (Set.range (fun a : α × Fin n × Fin (r + 1) =>
    fun i : Fin h => periodicWeightedMonomial n (w a.1) a.2.1 a.2.2 i))

/-- Every defining weighted monomial belongs to its periodic polynomial space. -/
theorem periodicWeightedMonomial_mem {α : Type*} (h n r : ℕ) (w : α → ℕ → K)
    (a : α) (c d : ℕ) (hc : c < n) (hd : d ≤ r) :
    (fun i : Fin h => periodicWeightedMonomial n (w a) c d i) ∈
      periodicPolynomialSpace h n r w :=
  Submodule.subset_span ⟨(a, ⟨c, hc⟩, ⟨d, by omega⟩), rfl⟩

/-- Increasing the degree bound enlarges the weighted periodic polynomial space. -/
theorem periodicPolynomialSpace_mono {α : Type*} (h n : ℕ) (w : α → ℕ → K) :
    Monotone (fun r => periodicPolynomialSpace h n r w) := by
  intro r s hrs
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a, c, d⟩, rfl⟩
  exact periodicWeightedMonomial_mem h n s w a c d c.isLt (by have := d.isLt; omega)

/-- The dimension of weighted periodic polynomials is at most the number of
weights times the period times one more than the degree bound. -/
theorem periodicPolynomialSpace_finrank_le {α : Type*} [Fintype α]
    (h n r : ℕ) (w : α → ℕ → K) :
    Module.finrank K (periodicPolynomialSpace h n r w) ≤ Fintype.card α * n * (r + 1) := by
  have he := finrank_range_le_card (R := K)
    (fun a : α × Fin n × Fin (r + 1) =>
      fun i : Fin h => periodicWeightedMonomial n (w a.1) a.2.1 a.2.2 i)
  simpa only [periodicPolynomialSpace, Set.finrank, Fintype.card_prod,
    Fintype.card_fin, mul_assoc] using! he

/-- A polynomial of bounded degree supported on one residue class and multiplied
by an allowed weight belongs to the weighted periodic polynomial space. -/
theorem periodicPolynomialSpace_eval_mem {α : Type*}
    (h n r : ℕ) (w : α → ℕ → K) (a : α) (c : ℕ) (hc : c < n)
    (p : Polynomial K) (hp : p.natDegree ≤ r) :
    (fun i : Fin h => if i.val % n = c then p.eval (i.val : K) * w a i.val else 0) ∈
      periodicPolynomialSpace h n r w := by
  classical
  have he : (fun i : Fin h => if i.val % n = c then p.eval (i.val : K) * w a i.val else 0) =
      ∑ d ∈ range (r + 1), p.coeff d •
        (fun i : Fin h => periodicWeightedMonomial n (w a) c d i.val) := by
    funext i
    simp only [sum_apply, Pi.smul_apply, smul_eq_mul, periodicWeightedMonomial]
    by_cases hi : i.val % n = c
    · simp only [if_pos hi]
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp), sum_mul]
      apply sum_congr rfl
      intro d _
      ring
    · simp [hi]
  rw [he]
  exact Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _
    (periodicWeightedMonomial_mem h n r w a c d hc (Nat.le_of_lt_succ (mem_range.mp hd)))

end

end Lambert
