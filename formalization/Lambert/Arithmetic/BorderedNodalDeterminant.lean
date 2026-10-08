import Lambert.Arithmetic.ChristoffelDeterminant

/-! # Nodal elimination with evaluation columns -/

namespace Lambert
noncomputable section
open Polynomial Matrix Finset
open scoped Classical
variable {K : Type*} [Field K]

/-- A bordered nodal matrix combines evaluation columns with complementary-nodal functional columns and polynomial rows. -/
def borderedNodalMatrix {A h d : ℕ} (x : Fin (h + d) → K)
    (f : (Fin A ⊕ Fin h) → K[X] →ₗ[K] K)
    (v : (Fin A ⊕ Fin h) → Fin A → K) :
    Matrix ((Fin A ⊕ Fin h) ⊕ Fin d) ((Fin A ⊕ Fin h) ⊕ Fin d) K := fun i j =>
  match i, (Equiv.sumAssoc (Fin A) (Fin h) (Fin d)) j with
  | Sum.inl i, Sum.inl j => v i j
  | Sum.inl i, Sum.inr j => f i (complementaryNodal x (finSumFinEquiv j))
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr i, Sum.inr j => x (finSumFinEquiv j) ^ i.val

/-- Eliminating the polynomial rows of a bordered nodal matrix leaves its evaluation columns and the first monomial moments, with the exact nodal signs. -/
theorem borderedNodalMatrix_det {A h d : ℕ} (x : Fin (h + d) → K)
    (hx : Function.Injective x) (f : (Fin A ⊕ Fin h) → K[X] →ₗ[K] K)
    (v : (Fin A ⊕ Fin h) → Fin A → K) :
    (borderedNodalMatrix x f v).det =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (h + d))) : ℤ) : K) *
        ((Equiv.Perm.sign (nodalTailReverse h d) : ℤ) : K)) *
      (vandermonde x).det *
        (Matrix.of fun i j : Fin A ⊕ Fin h =>
          Sum.elim (v i) (fun j => f i (X ^ j.val)) j).det := by
  let w := fun j => Lagrange.nodalWeight univ x j
  let V := vandermonde x
  let B₀ := (diagonal w * V).submatrix id (nodalTailReverse h d)
  let B₁ := B₀.submatrix finSumFinEquiv finSumFinEquiv
  let e := Equiv.sumAssoc (Fin A) (Fin h) (Fin d)
  let B := (fromBlocks (1 : Matrix (Fin A) (Fin A) K) 0 0 B₁).submatrix e e
  let M := borderedNodalMatrix x f v
  let C : Matrix (Fin A ⊕ Fin h) (Fin A ⊕ Fin h) K :=
    fun i j => Sum.elim (v i) (fun j => f i (X ^ j.val)) j
  let U : Matrix (Fin A ⊕ Fin h) (Fin d) K :=
    fun i j => f i (X ^ (h + j.rev.val))
  let T : Matrix (Fin d) (Fin d) K :=
    fun i j => ∑ k, w k * x k ^ (i.val + (h + j.rev.val))
  have hB : B.det = ((Equiv.Perm.sign (nodalTailReverse h d) : ℤ) : K) *
      ((∏ j, w j) * V.det) := by
    dsimp only [B]
    rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, one_mul]
    dsimp only [B₁]
    rw [det_submatrix_equiv_self]
    dsimp only [B₀]
    rw [det_permute', det_mul, det_diagonal]
  have hmul (i : Fin A ⊕ Fin h) (j : Fin (h + d)) :
      (∑ k, f i (complementaryNodal x k) *
        (w k * x k ^ (nodalTailReverse h d j).val)) =
      f i (X ^ (nodalTailReverse h d j).val) := by
    have he := congrArg (f i)
      (X_pow_eq_sum_complementary x hx _ (nodalTailReverse h d j).isLt)
    simpa only [map_sum, map_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, w]
      using he.symm
  have he : M * B = fromBlocks C U 0 T := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rcases j with j | j
      · rw [mul_apply]
        simp [M, B, e, borderedNodalMatrix, C, fromBlocks, Matrix.one_apply]
      · rw [mul_apply]
        simp [M, B, B₁, B₀, e, borderedNodalMatrix, C, fromBlocks, diagonal_mul, V]
        simpa only [Fin.sum_univ_add, nodalTailReverse_left, Fin.val_castAdd] using hmul i (Fin.castAdd d j)
    · rw [mul_apply]
      simp [M, B, B₁, B₀, e, borderedNodalMatrix, U, fromBlocks, diagonal_mul, V]
      simpa only [Fin.sum_univ_add, nodalTailReverse_right, Fin.val_natAdd, Fin.val_rev] using hmul i (Fin.natAdd h j)
    · rcases j with j | j
      · rw [mul_apply]
        simp [M, B, e, borderedNodalMatrix, fromBlocks]
      · rw [mul_apply]
        simp [M, B, B₁, B₀, e, borderedNodalMatrix, fromBlocks, diagonal_mul, V]
        have hn := nodalWeight_power_sum x hx (i.val + j.val) (by omega)
        rw [if_neg (by omega)] at hn
        simpa only [Fin.sum_univ_add, w, pow_add, mul_comm, mul_left_comm, mul_assoc] using hn
    · rw [mul_apply]
      simp [M, B, B₁, B₀, e, borderedNodalMatrix, T, fromBlocks, diagonal_mul, V]
      simp only [Fin.sum_univ_add, pow_add, mul_left_comm]
  have ht : T.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    dsimp [T, w]
    rw [nodalWeight_power_sum x hx _ (by have := j.isLt; omega),
      if_neg (by have := j.isLt; omega)]
  have ht1 : T.det = 1 := by
    rw [det_of_isLowerTriangular _ ht]
    apply prod_eq_one
    intro i _
    dsimp [T, w]
    have hi : i.val + (h + (d - (i.val + 1))) = h + d - 1 := by omega
    rw [hi, nodalWeight_power_sum x hx _ (by have := i.isLt; omega), if_pos rfl]
  have hdets := congrArg Matrix.det he
  rw [det_mul, hB, det_fromBlocks_zero₂₁, ht1, mul_one] at hdets
  have hw := nodalWeight_prod_mul_vandermonde_sq x hx
  let a : K := ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (h + d))) : ℤ) : K)
  let b : K := ((Equiv.Perm.sign (nodalTailReverse h d) : ℤ) : K)
  have ha : a ^ 2 = 1 := by
    dsimp [a]
    rw [← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]
    simp
  have hb : b ^ 2 = 1 := by
    dsimp [b]
    rw [← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]
    simp
  change M.det = a * b * V.det * C.det
  change M.det * (b * ((∏ j, w j) * V.det)) = C.det at hdets
  change (∏ j, w j) * V.det ^ 2 = a at hw
  have hmain : M.det * b * a = C.det * V.det := by
    linear_combination V.det * hdets - M.det * b * hw
  linear_combination a * b * hmain - M.det * a ^ 2 * hb - M.det * ha

/-- Bordered monomial moments factor into the pole and evaluation Vandermondes and the moment determinant with its nodal numerator. -/
theorem borderedNodalMatrix_det_moments {A h d : ℕ} (x : Fin (h + d) → K)
    (hx : Function.Injective x) (y : Fin A → K) (Λ : K[X] →ₗ[K] K) :
    (borderedNodalMatrix x
      (fun i => Λ.comp (LinearMap.mulLeft K (X ^ (finSumFinEquiv i).val)))
      (fun i j => y j ^ (finSumFinEquiv i).val)).det =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (h + d))) : ℤ) : K) *
        ((Equiv.Perm.sign (nodalTailReverse h d) : ℤ) : K)) *
      (vandermonde x).det * (vandermonde y).det *
        (Matrix.of fun i j : Fin h => Λ (Lagrange.nodal univ y * X ^ (i.val + j.val))).det := by
  rw [borderedNodalMatrix_det x hx]
  let f : Fin h → K[X] →ₗ[K] K := fun j =>
    Λ.comp (LinearMap.mulRight K (X ^ j.val))
  have he : (Matrix.of fun i j : Fin A ⊕ Fin h =>
      Sum.elim (fun j => y j ^ (finSumFinEquiv i).val)
        (fun j => (Λ.comp (LinearMap.mulLeft K (X ^ (finSumFinEquiv i).val))) (X ^ j.val)) j) =
      (borderedFunctionalMatrix y f).submatrix finSumFinEquiv finSumFinEquiv := by
    ext i j
    rcases j with j | j <;> simp [borderedFunctionalMatrix, f]
  rw [he, det_submatrix_equiv_self, borderedFunctionalMatrix_det]
  have hm : (Matrix.of fun i j : Fin h => f j (Lagrange.nodal univ y * X ^ i.val)) =
      (Matrix.of fun i j : Fin h => Λ (Lagrange.nodal univ y * X ^ (i.val + j.val))) := by
    ext i j
    simp [f, pow_add, mul_assoc]
  rw [hm]
  ring

end
end Lambert
