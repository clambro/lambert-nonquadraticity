import Mathlib.LinearAlgebra.Lagrange

/-!
# Cauchy determinants from polynomial evaluation

A row-scaled Cauchy matrix evaluates the complementary nodal polynomials.  Comparing
that evaluation matrix at two node sets through a common coefficient matrix gives an
exact cross-multiplied Cauchy determinant formula without an induction on matrix size.
-/

namespace Lambert

open Finset Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The Cauchy matrix with entries `1 / (x i - y j)`. -/
def cauchyMatrix {n : ℕ} (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j ↦ (x i - y j)⁻¹

/-- The polynomial having every `y`-node except the node indexed by `j` as a root. -/
def complementaryNodal {n : ℕ} (y : Fin n → K) (j : Fin n) : K[X] :=
  Lagrange.nodal (Finset.univ.erase j) y

/-- Complementary nodal polynomials have degree strictly below the matrix size. -/
theorem degree_complementaryNodal_lt {n : ℕ} (y : Fin n → K) (j : Fin n) :
    (complementaryNodal y j).degree < n := by
  rw [complementaryNodal, Lagrange.degree_nodal]
  norm_cast
  simpa using Finset.card_erase_lt_of_mem (Finset.mem_univ j)

/-- Evaluation of degree-bounded polynomials factors through a Vandermonde matrix and
their coefficient matrix. -/
theorem evaluationMatrix_eq_vandermonde_mul_coefficients {n : ℕ}
    (x : Fin n → K) (p : Fin n → K[X]) (hp : ∀ j, (p j).degree < n) :
    (Matrix.of fun i j ↦ (p j).eval (x i)) =
      Matrix.vandermonde x * Matrix.of (fun (i j : Fin n) ↦ (p j).coeff (i : ℕ)) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.of_apply]
  have hs := Polynomial.sum_fin (fun k c ↦ c * x i ^ k) (by simp) (hp j)
  simpa only [Polynomial.eval, Polynomial.eval₂_eq_sum, RingHom.id_apply,
    Matrix.of_apply, Matrix.vandermonde_apply, mul_comm] using hs.symm

/-- Evaluating the complementary nodal polynomials at their own node set
gives a diagonal matrix. -/
theorem complementaryNodal_evaluation_self {n : ℕ} (y : Fin n → K) :
    (Matrix.of fun i j ↦ (complementaryNodal y j).eval (y i)) =
      Matrix.diagonal (fun j ↦ (complementaryNodal y j).eval (y j)) := by
  ext i j
  by_cases hij : i = j
  · subst i
    simp
  · simp only [Matrix.of_apply, Matrix.diagonal, hij, ↓reduceIte]
    apply Lagrange.eval_nodal_at_node
    simp [hij]

/-- Multiplying each Cauchy row by the full `y`-nodal value produces the
complementary-nodal evaluation matrix. -/
theorem diagonal_nodal_mul_cauchyMatrix {n : ℕ} (x y : Fin n → K)
    (hxy : ∀ i j, x i ≠ y j) :
    Matrix.diagonal (fun i ↦ (Lagrange.nodal Finset.univ y).eval (x i)) *
        cauchyMatrix x y =
      Matrix.of fun i j ↦ (complementaryNodal y j).eval (x i) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.of_apply, cauchyMatrix, complementaryNodal,
    Lagrange.eval_nodal, Lagrange.eval_nodal]
  have hj : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
  have hprod : (∏ k, (x i - y k)) =
      (x i - y j) * ∏ k ∈ Finset.univ.erase j, (x i - y k) :=
    (Finset.mul_prod_erase _ _ hj).symm
  rw [hprod]
  field_simp [sub_ne_zero.mpr (hxy i j)]

/-- The exact Cauchy determinant formula in a division-free product form.

The two Vandermonde factors and all row/column products are displayed explicitly;
when the nodes are pairwise distinct and disjoint, every factor is nonzero and the
usual quotient formula follows by division.
-/
theorem cauchyMatrix_det_product {n : ℕ} (x y : Fin n → K)
    (hxy : ∀ i j, x i ≠ y j) :
    (∏ i, (Lagrange.nodal Finset.univ y).eval (x i)) *
          (cauchyMatrix x y).det * (Matrix.vandermonde y).det =
      (Matrix.vandermonde x).det *
        ∏ j, (complementaryNodal y j).eval (y j) := by
  let A : Matrix (Fin n) (Fin n) K :=
    Matrix.of (fun (i j : Fin n) ↦ (complementaryNodal y j).coeff (i : ℕ))
  have hxFactor := congrArg Matrix.det
    (evaluationMatrix_eq_vandermonde_mul_coefficients x
      (complementaryNodal y) (degree_complementaryNodal_lt y))
  have hyFactor := congrArg Matrix.det
    (evaluationMatrix_eq_vandermonde_mul_coefficients y
      (complementaryNodal y) (degree_complementaryNodal_lt y))
  have hscaled := congrArg Matrix.det (diagonal_nodal_mul_cauchyMatrix x y hxy)
  rw [Matrix.det_mul, Matrix.det_diagonal] at hscaled
  have hself := congrArg Matrix.det (complementaryNodal_evaluation_self y)
  rw [Matrix.det_diagonal] at hself
  change _ = (Matrix.vandermonde x * A).det at hxFactor
  change _ = (Matrix.vandermonde y * A).det at hyFactor
  rw [Matrix.det_mul] at hxFactor hyFactor
  rw [hscaled, hxFactor]
  rw [← hself, hyFactor]
  ring

/-- A Cauchy matrix on two injective, disjoint node sets is nonsingular. -/
theorem cauchyMatrix_det_ne_zero {n : ℕ} (x y : Fin n → K)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, x i ≠ y j) :
    (cauchyMatrix x y).det ≠ 0 := by
  intro hdet
  have hformula := cauchyMatrix_det_product x y hxy
  rw [hdet, mul_zero, zero_mul] at hformula
  have hvx : (Matrix.vandermonde x).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hx
  have hcomp : ∏ j, (complementaryNodal y j).eval (y j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    rw [complementaryNodal, Lagrange.eval_nodal]
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact sub_ne_zero.mpr (hy.ne (Finset.mem_erase.mp hk).1.symm)
  exact (mul_ne_zero hvx hcomp) hformula.symm

end

end Lambert
