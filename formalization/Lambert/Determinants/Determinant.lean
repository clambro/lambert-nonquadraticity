import Lambert.Determinants.Moments
import Lambert.Arithmetic.NodalDeterminant

/-!
# The augmented Lambert determinant identity

Moment rows precede polynomial rows in this formal matrix. This differs from
the research note by a block row permutation. The normalization records the
exact ordering sign, rather than an unspecified plus or minus.
-/

namespace Lambert

open Polynomial Matrix

noncomputable section

variable {K : Type*} [Field K]

/-- The ordering sign of the augmented Lambert identity includes the full
reversal, the extra-column reversal, and the positive-denominator normalization. -/
def lambertAugmentedSign (h d : ℕ) : ℤ :=
  (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (h + d))) : ℤ) *
    (Equiv.Perm.sign (nodalTailReverse h d) : ℤ) * (-1) ^ ((h + d + 1) * h)

/-- The augmented determinant normalization is an integer sign whose square is one. -/
theorem lambertAugmentedSign_sq (h d : ℕ) : lambertAugmentedSign h d ^ 2 = 1 := by
  have hr : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (h + d))) : ℤ) ^ 2 = 1 :=
    congrArg Units.val (Int.units_sq _)
  have ht : (Equiv.Perm.sign (nodalTailReverse h d) : ℤ) ^ 2 = 1 :=
    congrArg Units.val (Int.units_sq _)
  rw [lambertAugmentedSign, mul_pow, mul_pow, hr, ht, pow_right_comm (-1 : ℤ), neg_one_sq]
  simp

/-- The augmented Lambert matrix has shifted simple-pole rows followed by
the polynomial rows belonging to the extra poles. -/
def lambertAugmentedMatrix (q : K) (h k d s : ℕ) :
    Matrix (Fin (h + d)) (Fin (h + d)) K[X] :=
  fun i j => Fin.addCases (fun r => lambertPoleEntry q (r.val + s) (k + j.val))
    (fun r => C (q ^ ((k + j.val) * r.val))) i

/-- At distinct geometric nodes over an infinite field, the augmented matrix
and the shifted moment determinant differ by their exact Vandermonde and ordering sign. -/
theorem lambertAugmentedMatrix_det [Infinite K] (q : K) (h k d s : ℕ)
    (hq : Function.Injective (fun j : Fin (h + d) => q ^ (k + j.val))) :
    (lambertAugmentedMatrix q h k d s).det =
      C ((lambertAugmentedSign h d : K) *
        (vandermonde (fun j : Fin (h + d) => q ^ (k + j.val))).det) *
      lambertPoleDeterminant q h k (h + d) s := by
  apply Polynomial.funext
  intro z
  let ε : K := (-1) ^ (h + d + 1)
  have hε : ε * ε = 1 := by dsimp [ε]; rw [← mul_pow]; simp
  let f : Fin h → K[X] →ₗ[K] K := fun i =>
    ε • (Polynomial.leval z).comp ((lambertNumeratorFunctional q k (h + d)).comp
      (LinearMap.mulLeft K (X ^ (i.val + s))))
  have hf (i : Fin h) (p : K[X]) : f i p =
      ε * (lambertNumeratorFunctional q k (h + d) (X ^ (i.val + s) * p)).eval z := rfl
  have hm : augmentedNodalMatrix (fun j : Fin (h + d) => q ^ (k + j.val)) f =
      (lambertAugmentedMatrix q h k d s).map (Polynomial.eval z) := by
    apply Matrix.ext
    intro i j
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simp only [augmentedNodalMatrix, lambertAugmentedMatrix, Fin.addCases_left,
        Matrix.map_apply, hf, lambertNumeratorFunctional_complementary q k _ hq,
        eval_smul, smul_eq_mul]
      change ε * (ε * _) = _
      rw [← mul_assoc, hε, one_mul]
    · simp [augmentedNodalMatrix, lambertAugmentedMatrix, pow_mul]
  have hp : (Matrix.of fun i j : Fin h => f i (X ^ j.val)) =
      ε • (Matrix.of fun i j : Fin h =>
        (lambertPoleMoment q k (h + d) (i.val + j.val + s)).eval z) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hf,
      ← pow_add, lambertPoleMoment]
    rw [show i.val + s + j.val = i.val + j.val + s by omega]
  have he := augmentedNodalMatrix_det (fun j : Fin (h + d) => q ^ (k + j.val)) hq f
  rw [hm, hp, det_smul, Fintype.card_fin] at he
  have heval (A : Matrix (Fin h) (Fin h) K[X]) :
      A.det.eval z = (A.map (Polynomial.eval z)).det :=
    (Polynomial.evalRingHom z).map_det A
  have heval' (A : Matrix (Fin (h + d)) (Fin (h + d)) K[X]) :
      A.det.eval z = (A.map (Polynomial.eval z)).det :=
    (Polynomial.evalRingHom z).map_det A
  rw [heval', eval_mul, eval_C, lambertPoleDeterminant, heval]
  change _ = _ * Matrix.det (fun i j : Fin h =>
    (lambertPoleMoment q k (h + d) (i.val + j.val + s)).eval z)
  rw [he]
  change _ * _ * (_ * Matrix.det (fun i j : Fin h =>
    (lambertPoleMoment q k (h + d) (i.val + j.val + s)).eval z)) = _
  simp only [lambertAugmentedSign, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, ε, pow_mul]
  ring

/-- The augmented identity holds over the formal rational-function base
without any unproved node-separation hypothesis. -/
theorem lambertAugmentedMatrix_det_formal (h k d s : ℕ) :
    (lambertAugmentedMatrix (RatFunc.X : RatFunc ℚ) h k d s).det =
      C ((lambertAugmentedSign h d : RatFunc ℚ) *
        (vandermonde (fun j : Fin (h + d) => (RatFunc.X : RatFunc ℚ) ^ (k + j.val))).det) *
      lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s := by
  let : Infinite (RatFunc ℚ) := Infinite.of_injective _ ratFunc_X_pow_injective
  apply lambertAugmentedMatrix_det
  intro i j he
  exact Fin.ext (Nat.add_left_cancel (ratFunc_X_pow_injective he))


end

end Lambert
