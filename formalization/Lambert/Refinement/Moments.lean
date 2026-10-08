import Lambert.Determinants.Moments
import Lambert.Arithmetic.BorderedNodalDeterminant

/-! # Lambert determinants with an initial numerator-zero window -/
namespace Lambert
noncomputable section
open Polynomial Matrix Finset
open scoped Classical
variable {K : Type*} [Field K]

/-- The numerator-weighted Lambert determinant inserts zeros at the first geometric nodes before its pole window. -/
def lambertRefinementDeterminant (q : K) (h A b D s : ℕ) : K[X] :=
  (Matrix.of fun i j : Fin h => lambertNumeratorFunctional q b D
    (lambertPoleDenominator q 0 A * X ^ (i.val + j.val + s))).det

/-- With no numerator zeros, the weighted determinant is the shifted finite-window Lambert determinant. -/
theorem lambertRefinementDeterminant_zero (q : K) (h b D s : ℕ) :
    lambertRefinementDeterminant q h 0 b D s = lambertPoleDeterminant q h b D s := by
  simp [lambertRefinementDeterminant, lambertPoleDeterminant, lambertPoleMoment,
    lambertPoleDenominator_eq_prod]

/-- The bordered Lambert matrix has evaluation columns followed by pole columns, with its polynomial rows last. -/
def lambertRefinementBorderedMatrix (q : K) (h A b d s : ℕ) :
    Matrix ((Fin A ⊕ Fin h) ⊕ Fin d) ((Fin A ⊕ Fin h) ⊕ Fin d) K[X] := fun i j =>
  match i, (Equiv.sumAssoc (Fin A) (Fin h) (Fin d)) j with
  | Sum.inl i, Sum.inl j => C (q ^ (j.val * (finSumFinEquiv i).val))
  | Sum.inl i, Sum.inr j => lambertPoleEntry q ((finSumFinEquiv i).val + s)
      (b + (finSumFinEquiv j).val)
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr i, Sum.inr j => C (q ^ ((b + (finSumFinEquiv j).val) * i.val))

/-- The row index separates monomial functional rows from the polynomial tail. -/
def lambertRefinementRowIndex (h A d : ℕ) :
    ((Fin A ⊕ Fin h) ⊕ Fin d) ≃ (Fin (A + h) ⊕ Fin d) :=
  Equiv.sumCongr finSumFinEquiv (Equiv.refl _)

/-- The column index separates evaluation nodes from pole nodes. -/
def lambertRefinementColIndex (h A d : ℕ) :
    ((Fin A ⊕ Fin h) ⊕ Fin d) ≃ (Fin A ⊕ Fin (h + d)) :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv)

/-- Block coordinates expose the evaluation, Lambert, zero, and polynomial entries of the bordered matrix. -/
theorem lambertRefinementBorderedMatrix_apply (q : K) (h A b d s : ℕ)
    (i j : (Fin A ⊕ Fin h) ⊕ Fin d) :
    lambertRefinementBorderedMatrix q h A b d s i j =
      match lambertRefinementRowIndex h A d i, lambertRefinementColIndex h A d j with
      | Sum.inl i, Sum.inl j => C (q ^ (j.val * i.val))
      | Sum.inl i, Sum.inr j => lambertPoleEntry q (i.val + s) (b + j.val)
      | Sum.inr _, Sum.inl _ => 0
      | Sum.inr i, Sum.inr j => C (q ^ ((b + j.val) * i.val)) := by
  rcases i with i | i <;> rcases j with (j | j) | j <;> rfl

/-- The bordered determinant sign records nodal reversal, polynomial-tail reversal, and the numerator and pole signs. -/
def lambertRefinementBorderedSign (h A d : ℕ) : ℤ :=
  (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (h + d))) : ℤ) *
    (Equiv.Perm.sign (nodalTailReverse h d) : ℤ) *
      ((-1) ^ (h + d + 1) * (-1) ^ A) ^ h

/-- The bordered determinant normalization is an integer sign whose square is one. -/
theorem lambertRefinementBorderedSign_sq (h A d : ℕ) :
    lambertRefinementBorderedSign h A d ^ 2 = 1 := by
  have hr : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (h + d))) : ℤ) ^ 2 = 1 :=
    congrArg Units.val (Int.units_sq _)
  have ht : (Equiv.Perm.sign (nodalTailReverse h d) : ℤ) ^ 2 = 1 :=
    congrArg Units.val (Int.units_sq _)
  rw [lambertRefinementBorderedSign, mul_pow, mul_pow, hr, ht,
    pow_right_comm _ h 2, mul_pow, pow_right_comm (-1 : ℤ) (h + d + 1) 2,
    pow_right_comm (-1 : ℤ) A 2, neg_one_sq]
  simp

/-- The bordered matrix equals the numerator-weighted determinant times both Vandermondes and the exact ordering sign. -/
theorem lambertRefinementBorderedMatrix_det [Infinite K] (q : K) (h A b d s : ℕ)
    (hq : Function.Injective (fun j : Fin (h + d) => q ^ (b + j.val))) :
    (lambertRefinementBorderedMatrix q h A b d s).det =
      C ((lambertRefinementBorderedSign h A d : K) *
        (vandermonde (fun j : Fin (h + d) => q ^ (b + j.val))).det *
        (vandermonde (fun j : Fin A => q ^ j.val)).det) *
      lambertRefinementDeterminant q h A b (h + d) s := by
  apply Polynomial.funext
  intro z
  let ε : K := (-1) ^ (h + d + 1)
  have hε : ε * ε = 1 := by dsimp [ε]; rw [← mul_pow]; simp
  let Λ : K[X] →ₗ[K] K := ε • (Polynomial.leval z).comp
    ((lambertNumeratorFunctional q b (h + d)).comp (LinearMap.mulLeft K (X ^ s)))
  have hf (p : K[X]) : Λ p =
      ε * (lambertNumeratorFunctional q b (h + d) (X ^ s * p)).eval z := rfl
  have hentry (i : ℕ) (j : Fin (h + d)) :
      Λ (X ^ i * complementaryNodal (fun j : Fin (h + d) => q ^ (b + j.val)) j) =
        (lambertPoleEntry q (i + s) (b + j.val)).eval z := by
    rw [hf, ← mul_assoc, ← pow_add, Nat.add_comm s,
      lambertNumeratorFunctional_complementary q b _ hq, eval_smul, smul_eq_mul]
    change ε * (ε * _) = _
    rw [← mul_assoc, hε, one_mul]
  have hm : borderedNodalMatrix (fun j : Fin (h + d) => q ^ (b + j.val))
      (fun i => Λ.comp (LinearMap.mulLeft K (X ^ (finSumFinEquiv i).val)))
      (fun i (j : Fin A) => (q ^ j.val) ^ (finSumFinEquiv i).val) =
      (lambertRefinementBorderedMatrix q h A b d s).map (Polynomial.eval z) := by
    ext i j
    rcases i with i | i <;> rcases j with (j | j) | j
    all_goals simp [borderedNodalMatrix, lambertRefinementBorderedMatrix,
      Equiv.sumAssoc, hentry, ← pow_mul]
  have hp : (Matrix.of fun i j : Fin h =>
      Λ (Lagrange.nodal univ (fun j : Fin A => q ^ j.val) * X ^ (i.val + j.val))) =
      (ε * (-1 : K) ^ A) •
        (Matrix.of fun i j : Fin h => (lambertNumeratorFunctional q b (h + d)
          (lambertPoleDenominator q 0 A * X ^ (i.val + j.val + s))).eval z) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hf,
      lambertPoleDenominator, Nat.zero_add, smul_mul_assoc, map_smul,
      eval_smul, smul_eq_mul]
    have he : X ^ s * (Lagrange.nodal univ (fun j : Fin A => q ^ j.val) * X ^ (i.val + j.val)) =
        Lagrange.nodal univ (fun j : Fin A => q ^ j.val) * X ^ (i.val + j.val + s) := by
      rw [pow_add]
      ring
    rw [he]
    have hs : (-1 : K) ^ A * (-1 : K) ^ A = 1 := by rw [← mul_pow]; simp
    rw [mul_assoc, ← mul_assoc ((-1 : K) ^ A), hs, one_mul]
  have he := borderedNodalMatrix_det_moments
    (fun j : Fin (h + d) => q ^ (b + j.val)) hq (fun j : Fin A => q ^ j.val) Λ
  rw [hm, hp, det_smul, Fintype.card_fin] at he
  have heval {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι K[X]) :
      B.det.eval z = (B.map (Polynomial.eval z)).det := (Polynomial.evalRingHom z).map_det B
  rw [heval, eval_mul, eval_C, lambertRefinementDeterminant, heval]
  rw [he]
  simp only [lambertRefinementBorderedSign, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, ε, Matrix.map, Matrix.of_apply]
  ring

end
end Lambert
