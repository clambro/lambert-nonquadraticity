import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Bordered determinant quotients

A nonsingular square block converts an arbitrary bilinear correction into
an exact bordered determinant ratio over any field.
-/

namespace Lambert

open Matrix

/-- A nonsingular field matrix identifies its bilinear Schur correction with the exact bordered determinant quotient. -/
theorem borderedDeterminant_quotient {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (hA : A.det ≠ 0) (b c : ι → K) (s : K) :
    s - c ⬝ᵥ (A⁻¹ *ᵥ b) =
      (Matrix.fromBlocks A (fun i (_ : Unit) => b i)
        (fun (_ : Unit) j => c j) (fun (_ _ : Unit) => s)).det / A.det := by
  have hunit : IsUnit A := A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hA)
  cases hunit.nonempty_invertible
  let B : Matrix ι Unit K := fun i _ => b i
  let C : Matrix Unit ι K := fun _ j => c j
  let D : Matrix Unit Unit K := fun _ _ => s
  change s - c ⬝ᵥ (A⁻¹ *ᵥ b) = (Matrix.fromBlocks A B C D).det / A.det
  have hdet := Matrix.det_fromBlocks₁₁ A B C D
  rw [Matrix.invOf_eq_nonsing_inv, Matrix.det_unique (D - C * A⁻¹ * B)] at hdet
  have hcorner : (D - C * A⁻¹ * B) () () = s - c ⬝ᵥ (A⁻¹ *ᵥ b) := by
    simp only [Matrix.sub_apply, Matrix.mul_apply]
    simp only [D, C, B, dotProduct, mulVec]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, mul_assoc]
  rw [hcorner] at hdet
  apply (eq_div_iff hA).mpr
  rw [mul_comm]
  exact hdet.symm

/-- Separating the last row and column preserves a finite matrix determinant as a bordered lower-block determinant. -/
theorem matrix_det_last_border {R : Type*} [CommRing R] (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.det = (Matrix.fromBlocks (A.submatrix Fin.castSucc Fin.castSucc)
      (Matrix.of (fun i (_ : Unit) => A i.castSucc (Fin.last n)))
      (Matrix.of (fun (_ : Unit) j => A (Fin.last n) j.castSucc))
      (Matrix.of (fun (_ _ : Unit) => A (Fin.last n) (Fin.last n)))).det := by
  classical
  let e : Fin n ⊕ Unit ≃ Fin (n + 1) :=
    (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
  have hcast (i : Fin n) : Fin.castAdd 1 i = i.castSucc := by apply Fin.ext; rfl
  have hlast (i : Unit) : Fin.natAdd n (finOneEquiv.symm i) = Fin.last n := by
    rw [show finOneEquiv.symm i = (0 : Fin 1) from Subsingleton.elim _ _]
    apply Fin.ext
    rfl
  have he : Matrix.reindex e.symm e.symm A =
      Matrix.fromBlocks (A.submatrix Fin.castSucc Fin.castSucc)
        (Matrix.of (fun i (_ : Unit) => A i.castSucc (Fin.last n)))
        (Matrix.of (fun (_ : Unit) j => A (Fin.last n) j.castSucc))
        (Matrix.of (fun (_ _ : Unit) => A (Fin.last n) (Fin.last n))) := by
    ext i j
    rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
      simp [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.submatrix_apply, e, hcast, hlast]
  rw [← he, Matrix.det_reindex_self]

end Lambert
