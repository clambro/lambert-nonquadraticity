import Lambert.Arithmetic.NodalFunctional

/-!
# Determinants of nodal functionals

Barycentric interpolation converts complementary nodal numerators to monomials.
The ordering signs are retained as explicit permutation signs.
-/

namespace Lambert

open Polynomial Finset Matrix

noncomputable section

variable {K : Type*} [Field K]

/-- Below the node count, barycentric power sums extract the top polynomial coefficient. -/
theorem nodalWeight_power_sum {n : ℕ} (x : Fin n → K)
    (hx : Function.Injective x) (k : ℕ) (hk : k < n) :
    (∑ j, Lagrange.nodalWeight univ x j * x j ^ k) =
      if k = n - 1 then 1 else 0 := by
  have he := Lagrange.coeff_eq_sum (s := univ) (v := x) hx.injOn
    (P := (X : K[X]) ^ k) (by simpa using (show (k : WithBot ℕ) < n by exact_mod_cast hk))
  simpa only [card_univ, Fintype.card_fin, eval_pow, eval_X, coeff_X_pow,
    Lagrange.nodalWeight, prod_inv_distrib, div_eq_mul_inv, mul_comm, eq_comm] using he.symm

/-- Below the node count, monomials have their exact complementary-nodal expansion. -/
theorem X_pow_eq_sum_complementary {n : ℕ} (x : Fin n → K)
    (hx : Function.Injective x) (k : ℕ) (hk : k < n) :
    (X : K[X]) ^ k = ∑ j, (Lagrange.nodalWeight univ x j * x j ^ k) •
      complementaryNodal x j := by
  have he := nodal_numerator_decomposition x hx ((X : K[X]) ^ k)
  have hd : (X : K[X]) ^ k /ₘ Lagrange.nodal univ x = 0 := by
    apply (divByMonic_eq_zero_iff Lagrange.nodal_monic).mpr
    simpa using (show (k : WithBot ℕ) < n by exact_mod_cast hk)
  simpa only [hd, mul_zero, zero_add, eval_pow, eval_X] using he

private theorem sign_cast_sq {n : Type*} [Fintype n] [DecidableEq n]
    (p : Equiv.Perm n) : ((Equiv.Perm.sign p : ℤ) : K) ^ 2 = 1 := by
  rw [← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]
  simp

/-- The product of barycentric weights times the squared Vandermonde is the
sign of reversing the node indices. -/
theorem nodalWeight_prod_mul_vandermonde_sq {n : ℕ} (x : Fin n → K)
    (hx : Function.Injective x) :
    (∏ j, Lagrange.nodalWeight univ x j) * (vandermonde x).det ^ 2 =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : K) := by
  let V := vandermonde x
  let W := diagonal (fun j => Lagrange.nodalWeight univ x j)
  let G := V.transpose * (W * V)
  have hg (i j : Fin n) : G i j =
      ∑ k, Lagrange.nodalWeight univ x k * x k ^ (i.val + j.val) := by
    dsimp only [G]
    rw [mul_apply]
    simp only [V, W, transpose_apply, diagonal_mul, vandermonde_apply,
      pow_add]
    apply sum_congr rfl
    intro k _
    ring
  have ht : (G.submatrix id Fin.revPerm).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    simp only [submatrix_apply, id_eq, Fin.revPerm_apply, hg]
    rw [nodalWeight_power_sum x hx _ (by have := j.isLt; simp only [Fin.val_rev]; omega)]
    rw [if_neg (by have := j.isLt; simp only [Fin.val_rev]; omega)]
  have hd (i : Fin n) : (G.submatrix id Fin.revPerm) i i = 1 := by
    simp only [submatrix_apply, id_eq, Fin.revPerm_apply, hg]
    have hi : i.val + i.rev.val = n - 1 := by rw [Fin.val_rev]; omega
    rw [hi, nodalWeight_power_sum x hx _ (by have := i.isLt; omega), if_pos rfl]
  have he : (G.submatrix id Fin.revPerm).det = 1 := by
    rw [det_of_isLowerTriangular _ ht]
    simp only [hd, prod_const_one]
  rw [det_permute'] at he
  simp only [G, V, W, det_mul, det_transpose, det_diagonal] at he
  have hs := sign_cast_sq (K := K) (Fin.revPerm : Equiv.Perm (Fin n))
  linear_combination ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : K) * he -
    ((∏ j, Lagrange.nodalWeight univ x j) * (vandermonde x).det ^ 2) * hs

/-- The last block of a finite index set can be reversed while retaining the first block. -/
def nodalTailReverse (h d : ℕ) : Equiv.Perm (Fin (h + d)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin h))
    (Fin.revPerm : Equiv.Perm (Fin d)))).trans finSumFinEquiv

/-- Reversing the last index block fixes every index of the first block. -/
@[simp] theorem nodalTailReverse_left (h d : ℕ) (i : Fin h) :
    nodalTailReverse h d (Fin.castAdd d i) = Fin.castAdd d i := by
  simp [nodalTailReverse]

/-- Reversing the last index block reverses its local index. -/
@[simp] theorem nodalTailReverse_right (h d : ℕ) (i : Fin d) :
    nodalTailReverse h d (Fin.natAdd h i) = Fin.natAdd h i.rev := by
  simp [nodalTailReverse]

/-- The augmented nodal matrix places the functional rows before the polynomial rows. -/
def augmentedNodalMatrix {h d : ℕ} (x : Fin (h + d) → K)
    (f : Fin h → K[X] →ₗ[K] K) : Matrix (Fin (h + d)) (Fin (h + d)) K :=
  fun i j => Fin.addCases (fun r => f r (complementaryNodal x j))
    (fun r => x j ^ r.val) i

/-- An augmented nodal determinant equals its monomial moment determinant
times the Vandermonde and the two explicit column-order signs. -/
theorem augmentedNodalMatrix_det {h d : ℕ} (x : Fin (h + d) → K)
    (hx : Function.Injective x) (f : Fin h → K[X] →ₗ[K] K) :
    (augmentedNodalMatrix x f).det =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (h + d))) : ℤ) : K) *
        ((Equiv.Perm.sign (nodalTailReverse h d) : ℤ) : K)) *
      (vandermonde x).det * (Matrix.of fun i j : Fin h => f i (X ^ j.val)).det := by
  let w := fun j => Lagrange.nodalWeight univ x j
  let V := vandermonde x
  let M := augmentedNodalMatrix x f
  let B := (diagonal w * V).submatrix id (nodalTailReverse h d)
  let H : Matrix (Fin h) (Fin h) K := fun i j => f i (X ^ j.val)
  let U : Matrix (Fin h) (Fin d) K := fun i j => f i (X ^ (h + j.rev.val))
  let T : Matrix (Fin d) (Fin d) K :=
    fun i j => ∑ k, w k * x k ^ (i.val + (h + j.rev.val))
  have hm (i j : Fin (h + d)) : (M * B) i j =
      Fin.addCases (fun r => f r (X ^ (nodalTailReverse h d j).val))
        (fun r => ∑ k, w k * x k ^ (r.val + (nodalTailReverse h d j).val)) i := by
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · rw [mul_apply]
      simp only [M, B, augmentedNodalMatrix, Fin.addCases_left,
        submatrix_apply, id_eq, diagonal_mul, V, vandermonde_apply]
      have he := congrArg (f r)
        (X_pow_eq_sum_complementary x hx _ (nodalTailReverse h d j).isLt)
      simp only [map_sum, map_smul, smul_eq_mul] at he
      simpa only [w, mul_comm, mul_left_comm, mul_assoc] using he.symm
    · rw [mul_apply]
      simp only [M, B, augmentedNodalMatrix, Fin.addCases_right,
        submatrix_apply, id_eq, diagonal_mul, V, vandermonde_apply, pow_add]
      apply sum_congr rfl
      intro k _
      ring
  have he : (M * B).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks H U 0 T := by
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · simp [submatrix_apply, hm, H, fromBlocks]
    · simp [submatrix_apply, hm, U, fromBlocks]
    · simp only [submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
        hm, Fin.addCases_right, nodalTailReverse_left, Fin.val_castAdd,
        fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [nodalWeight_power_sum x hx _ (by omega), if_neg (by omega)]
    · simp [submatrix_apply, hm, T, fromBlocks]
  have ht : T.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    dsimp [T, w]
    rw [nodalWeight_power_sum x hx _ (by have := j.isLt; omega),
      if_neg (by have := j.isLt; omega)]
  have hd (i : Fin d) : T i i = 1 := by
    dsimp [T, w]
    have hi : i.val + (h + (d - (i.val + 1))) = h + d - 1 := by omega
    rw [hi, nodalWeight_power_sum x hx _ (by have := i.isLt; omega), if_pos rfl]
  have ht1 : T.det = 1 := by
    rw [det_of_isLowerTriangular _ ht]
    simp only [hd, prod_const_one]
  have hdets := congrArg Matrix.det he
  rw [det_submatrix_equiv_self, det_mul, det_fromBlocks_zero₂₁, ht1, mul_one] at hdets
  have hb : B.det = ((Equiv.Perm.sign (nodalTailReverse h d) : ℤ) : K) *
      ((∏ j, w j) * V.det) := by
    dsimp only [B]
    rw [det_permute', det_mul, det_diagonal]
  rw [hb] at hdets
  have hw := nodalWeight_prod_mul_vandermonde_sq x hx
  have hs := sign_cast_sq (K := K) (nodalTailReverse h d)
  have hr := sign_cast_sq (K := K) (Fin.revPerm : Equiv.Perm (Fin (h + d)))
  dsimp only [w, V] at hdets
  dsimp only [M, H] at hdets
  have hmain : (augmentedNodalMatrix x f).det *
      ((Equiv.Perm.sign (nodalTailReverse h d) : ℤ) : K) *
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (h + d))) : ℤ) : K) =
        Matrix.det (fun i j : Fin h => f i (X ^ j.val)) * (vandermonde x).det := by
    linear_combination (vandermonde x).det * hdets -
      ((augmentedNodalMatrix x f).det *
        ((Equiv.Perm.sign (nodalTailReverse h d) : ℤ) : K)) * hw
  change (augmentedNodalMatrix x f).det = _ * _ *
    Matrix.det (fun i j : Fin h => f i (X ^ j.val))
  linear_combination
    (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (h + d))) : ℤ) : K) *
      ((Equiv.Perm.sign (nodalTailReverse h d) : ℤ) : K)) * hmain -
    ((augmentedNodalMatrix x f).det *
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (h + d))) : ℤ) : K) ^ 2) * hs -
    (augmentedNodalMatrix x f).det * hr

end

end Lambert
