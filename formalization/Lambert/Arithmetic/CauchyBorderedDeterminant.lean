import Lambert.Arithmetic.CauchyDeterminant
import Lambert.Arithmetic.CauchyInterpolation
import Lambert.Arithmetic.BorderedDeterminant
import Mathlib.Tactic.LinearCombination

/-!
# Exact Cauchy border corrections

Proper interpolation determines the Schur complement of a Cauchy matrix
as an exact nodal product quotient.
-/

namespace Lambert

open Polynomial Finset Matrix

/-- A Cauchy Schur complement is exactly the product of its new row and column nodal factors divided by the three cross denominators. -/
theorem cauchyMatrix_schur_complement {K : Type*} [Field K] (n : ℕ)
    (x y : Fin n → K) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, x i ≠ y j) (a b : K)
    (hab : a ≠ b) (hay : ∀ j, a ≠ y j) (hbx : ∀ i, b ≠ x i) :
    (a - b)⁻¹ - (fun j => (a - y j)⁻¹) ⬝ᵥ
      ((cauchyMatrix x y)⁻¹ *ᵥ (fun i => (x i - b)⁻¹)) =
      ((Lagrange.nodal Finset.univ x).eval a *
        (Lagrange.nodal Finset.univ y).eval b) /
        ((a - b) * (Lagrange.nodal Finset.univ y).eval a *
          (Lagrange.nodal Finset.univ x).eval b) := by
  classical
  let A := cauchyMatrix x y
  let v := A⁻¹ *ᵥ (fun i => (x i - b)⁻¹)
  let P := cauchyResidueParameter Finset.univ y v
  let Y := Lagrange.nodal Finset.univ y
  let Z := Lagrange.nodal Finset.univ x
  let T := Y - (X - C b) * P
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr (cauchyMatrix_det_ne_zero x y hx hy hxy)
  have hv : A *ᵥ v = fun i => (x i - b)⁻¹ := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec]
  have hP : P.degree < n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      cauchyResidueParameter_degree_lt Finset.univ y v hy.injOn
  have hc (t : K) (ht : ∀ j, t ≠ y j) :
      (fun j => (t - y j)⁻¹) ⬝ᵥ v = P.eval t / Y.eval t := by
    have he := cauchyResidueConvolution_eq_div Finset.univ y P hy.injOn
      (by simpa only [Finset.card_univ, Fintype.card_fin] using hP) t (fun j _ => ht j)
    have hcoeff (j : Fin n) : cauchyResidueCoefficient Finset.univ y P j = v j :=
      cauchyResidueParameter_coefficient Finset.univ y v hy.injOn j (mem_univ j)
    simp only [cauchyResidueConvolution, hcoeff, div_eq_mul_inv] at he
    simpa only [dotProduct, div_eq_mul_inv, mul_comm] using he
  have hroot (i : Fin n) : T.eval (x i) = 0 := by
    have he := congrFun hv i
    have hh := hc (x i) (hxy i)
    have heq : (fun j => (x i - y j)⁻¹) ⬝ᵥ v = (x i - b)⁻¹ := by
      exact he
    rw [heq] at hh
    have hY : Y.eval (x i) ≠ 0 := Lagrange.eval_nodal_not_at_node (fun j _ => hxy i j)
    have hb : x i - b ≠ 0 := sub_ne_zero.mpr (hbx i).symm
    dsimp only [T]
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    field_simp [hY, hb] at hh ⊢
    linear_combination hh
  have hdiv : Z ∣ T :=
    (nodal_dvd_iff_eval_eq_zero Finset.univ x hx.injOn T).mpr (fun i _ => hroot i)
  have hdeg : T.natDegree ≤ n := by
    by_cases hz : P = 0
    · simp only [T, hz, mul_zero, sub_zero, Y, Lagrange.natDegree_nodal,
        Finset.card_univ, Fintype.card_fin, le_refl]
    · have hp := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hP
      apply (Polynomial.natDegree_sub_le Y ((X - C b) * P)).trans
      apply max_le
      · simp only [Y, Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin, le_refl]
      · exact Polynomial.natDegree_mul_le.trans (by
          rw [Polynomial.natDegree_X_sub_C]
          omega)
  obtain ⟨W, hW⟩ := hdiv
  have hWdeg : W.natDegree = 0 := by
    by_cases hz : W = 0
    · simp only [hz, Polynomial.natDegree_zero]
    · rw [hW, Polynomial.natDegree_mul Lagrange.nodal_ne_zero hz] at hdeg
      rw [Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin] at hdeg
      omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero hWdeg] at hW
  have hZb : Z.eval b ≠ 0 := Lagrange.eval_nodal_not_at_node (fun i _ => hbx i)
  have hYa : Y.eval a ≠ 0 := Lagrange.eval_nodal_not_at_node (fun j _ => hay j)
  have hscale : W.coeff 0 = Y.eval b / Z.eval b := by
    have he := congrArg (fun p : K[X] => p.eval b) hW
    simp only [T, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_mul, sub_zero] at he
    exact (eq_div_iff hZb).mpr (by simpa only [mul_comm] using he.symm)
  have he := congrArg (fun p : K[X] => p.eval a) hW
  simp only [T, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C] at he
  rw [hscale] at he
  change (a - b)⁻¹ - (fun j => (a - y j)⁻¹) ⬝ᵥ v =
    (Z.eval a * Y.eval b) / ((a - b) * Y.eval a * Z.eval b)
  rw [hc a hay]
  field_simp [sub_ne_zero.mpr hab, hYa, hZb] at he ⊢
  linear_combination he

/-- Bordering a nonsingular Cauchy matrix gives an exact determinant quotient with all row and column factors retained. -/
theorem cauchyMatrix_bordered_det_quotient {K : Type*} [Field K] (n : ℕ)
    (x y : Fin n → K) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, x i ≠ y j) (a b : K)
    (hab : a ≠ b) (hay : ∀ j, a ≠ y j) (hbx : ∀ i, b ≠ x i) :
    (Matrix.fromBlocks (cauchyMatrix x y)
      (fun i (_ : Unit) => (x i - b)⁻¹)
      (fun (_ : Unit) j => (a - y j)⁻¹)
      (fun (_ _ : Unit) => (a - b)⁻¹)).det / (cauchyMatrix x y).det =
      ((Lagrange.nodal Finset.univ x).eval a *
        (Lagrange.nodal Finset.univ y).eval b) /
        ((a - b) * (Lagrange.nodal Finset.univ y).eval a *
          (Lagrange.nodal Finset.univ x).eval b) := by
  rw [← borderedDeterminant_quotient (cauchyMatrix x y)
    (cauchyMatrix_det_ne_zero x y hx hy hxy)]
  exact cauchyMatrix_schur_complement n x y hx hy hxy a b hab hay hbx

/-- Multiplying each column of a bordered matrix by its own nonzero weight multiplies its determinant quotient by the new column weight alone. -/
theorem borderedDeterminant_column_weights {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (hA : A.det ≠ 0)
    (b c : ι → K) (s : K) (w : ι → K) (hw : ∀ i, w i ≠ 0)
    (t : K) :
    (Matrix.fromBlocks (A * Matrix.diagonal w)
      (fun i (_ : Unit) => b i * t)
      (fun (_ : Unit) j => c j * w j)
      (fun (_ _ : Unit) => s * t)).det /
      (A * Matrix.diagonal w).det =
      t * (Matrix.fromBlocks A (fun i (_ : Unit) => b i)
        (fun (_ : Unit) j => c j) (fun (_ _ : Unit) => s)).det / A.det := by
  classical
  let M := Matrix.fromBlocks A (fun i (_ : Unit) => b i)
    (fun (_ : Unit) j => c j) (fun (_ _ : Unit) => s)
  let D : Matrix (ι ⊕ Unit) (ι ⊕ Unit) K :=
    Matrix.diagonal (Sum.elim w (fun _ => t))
  have he : M * D = Matrix.fromBlocks (A * Matrix.diagonal w)
      (fun i (_ : Unit) => b i * t)
      (fun (_ : Unit) j => c j * w j)
      (fun (_ _ : Unit) => s * t) := by
    ext i j
    rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
      simp [M, D, Matrix.mul_diagonal, Matrix.fromBlocks]
  have hd : D.det = (∏ i, w i) * t := by
    rw [Matrix.det_diagonal]
    simp [Fintype.prod_sum_type]
  have hp : (∏ i, w i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)
  rw [← he, Matrix.det_mul, hd, Matrix.det_mul, Matrix.det_diagonal]
  change M.det * ((∏ i, w i) * t) / (A.det * ∏ i, w i) = t * M.det / A.det
  field_simp [hA, hp]

end Lambert
