import Lambert.Arithmetic.NodalDeterminant

/-!
# Bordered determinants and numerator zeros

Evaluation columns impose a nodal factor on the remaining functional rows.
The evaluation columns come first, so the determinant identity has no
unrecorded permutation sign.
-/

namespace Lambert
noncomputable section
open Polynomial Matrix Finset
open scoped Classical
variable {K : Type*} [Field K]

/-- Replacing monomials by monic polynomials of the same successive degrees preserves a determinant of linear functionals. -/
theorem polynomialFunctional_det_monic_basis {n : ℕ} (p : Fin n → K[X])
    (hp : ∀ i, (p i).Monic) (hd : ∀ i, (p i).natDegree = i.val)
    (f : Fin n → K[X] →ₗ[K] K) :
    (Matrix.of fun i j => f j (p i)).det =
      (Matrix.of fun i j => f j (X ^ i.val)).det := by
  let B : Matrix (Fin n) (Fin n) K := fun i j => (p i).coeff j.val
  let M : Matrix (Fin n) (Fin n) K := fun i j => f j (X ^ i.val)
  have hb : B.IsLowerTriangular := by
    intro i j hij
    exact coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hij)
  have hdiag (i : Fin n) : B i i = 1 := by
    dsimp [B]
    rw [← hd i]
    exact (hp i).coeff_natDegree
  have hdet : B.det = 1 := by
    rw [det_of_isLowerTriangular _ hb]
    simp only [hdiag, prod_const_one]
  have he : B * M = Matrix.of (fun i j => f j (p i)) := by
    ext i j
    rw [mul_apply]
    have hpoly : p i = ∑ k : Fin n, (p i).coeff k.val • (X : K[X]) ^ k.val := by
      have hs := (p i).as_sum_range_C_mul_X_pow' (by rw [hd]; exact i.isLt)
      rw [← Fin.sum_univ_eq_sum_range] at hs
      simpa only [smul_eq_C_mul] using hs
    change (∑ k : Fin n, (p i).coeff k.val * f j (X ^ k.val)) = f j (p i)
    conv_rhs => rw [hpoly, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [← he, det_mul, hdet, one_mul]
  rfl

/-- The bordered functional matrix evaluates monomials at its first nodes and applies the remaining linear functionals in its last columns. -/
def borderedFunctionalMatrix {A h : ℕ} (x : Fin A → K)
    (f : Fin h → K[X] →ₗ[K] K) : Matrix (Fin (A + h)) (Fin (A + h)) K :=
  fun i j => Fin.addCases (fun a => x a ^ i.val) (fun a => f a (X ^ i.val)) j

/-- Evaluation columns factor a bordered functional determinant into their Vandermonde and the moment determinant with the nodal numerator. -/
theorem borderedFunctionalMatrix_det {A h : ℕ} (x : Fin A → K)
    (f : Fin h → K[X] →ₗ[K] K) :
    (borderedFunctionalMatrix x f).det =
      (vandermonde x).det *
        (Matrix.of fun i j : Fin h =>
          f j (Lagrange.nodal univ x * X ^ i.val)).det := by
  let p : Fin (A + h) → K[X] := Fin.addCases
    (fun i => X ^ i.val) (fun i => Lagrange.nodal univ x * X ^ i.val)
  let g : Fin (A + h) → K[X] →ₗ[K] K := Fin.addCases
    (fun i => Polynomial.leval (x i)) f
  have hp (i : Fin (A + h)) : (p i).Monic := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [p, Fin.addCases_left] using (monic_X_pow (R := K) j.val)
    · intro j
      simpa only [p, Fin.addCases_right] using
        (Lagrange.nodal_monic (s := univ) (v := x)).mul (monic_X_pow j.val)
  have hd (i : Fin (A + h)) : (p i).natDegree = i.val := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [p]
    · intro j
      simp [p, natDegree_mul, Lagrange.nodal_ne_zero]
  have he := polynomialFunctional_det_monic_basis p hp hd g
  have hm : (Matrix.of fun i j => g j (X ^ i.val)) = borderedFunctionalMatrix x f := by
    ext i j
    refine Fin.addCases ?_ ?_ j
    · intro a
      simp [g, borderedFunctionalMatrix]
    · intro a
      simp [g, borderedFunctionalMatrix]
  have hb : (Matrix.of fun i j => g j (p i)).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (vandermonde x).transpose
        (Matrix.of fun i j => f j (X ^ i.val))
        (0 : Matrix (Fin h) (Fin A) K)
        (Matrix.of fun i j : Fin h => f j (Lagrange.nodal univ x * X ^ i.val)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [p, g, vandermonde_apply]
    · simp [p, g]
    · simp [p, g, Lagrange.eval_nodal_at_node]
    · simp [p, g]
  rw [hm] at he
  rw [← he, ← det_submatrix_equiv_self finSumFinEquiv, hb,
    det_fromBlocks_zero₂₁, det_transpose]

end
end Lambert
