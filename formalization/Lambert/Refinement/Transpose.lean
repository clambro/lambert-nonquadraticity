import Lambert.Refinement.Moments

/-! # Transposing numerator-bordered Lambert matrices -/
namespace Lambert
noncomputable section
open Polynomial Matrix Finset
open scoped Classical
variable {K : Type*} [Field K]

/-- The row correspondence for bordered transposition exchanges the evaluation rows with the polynomial tail. -/
def lambertRefinementTransposeRows (h A d : ℕ) :
    ((Fin d ⊕ Fin h) ⊕ Fin A) ≃ ((Fin A ⊕ Fin h) ⊕ Fin d) :=
  (lambertRefinementRowIndex h d A).trans ((Equiv.sumComm _ _).trans
    ((Equiv.sumCongr (Equiv.refl _) (finCongr (Nat.add_comm d h))).trans
      (lambertRefinementColIndex h A d).symm))

/-- The column correspondence for bordered transposition exchanges the polynomial columns with evaluation columns. -/
def lambertRefinementTransposeCols (h A d : ℕ) :
    ((Fin d ⊕ Fin h) ⊕ Fin A) ≃ ((Fin A ⊕ Fin h) ⊕ Fin d) :=
  (lambertRefinementColIndex h d A).trans ((Equiv.sumComm _ _).trans
    ((Equiv.sumCongr (finCongr (Nat.add_comm h A)) (Equiv.refl _)).trans
      (lambertRefinementRowIndex h A d).symm))

private theorem transpose_rows_apply (h A d : ℕ) (i : (Fin d ⊕ Fin h) ⊕ Fin A) :
    lambertRefinementColIndex h A d (lambertRefinementTransposeRows h A d i) =
      (Equiv.sumCongr (Equiv.refl _) (finCongr (Nat.add_comm d h)))
        ((Equiv.sumComm _ _) (lambertRefinementRowIndex h d A i)) := by
  simp only [lambertRefinementTransposeRows, Equiv.trans_apply, Equiv.apply_symm_apply]

private theorem transpose_cols_apply (h A d : ℕ) (i : (Fin d ⊕ Fin h) ⊕ Fin A) :
    lambertRefinementRowIndex h A d (lambertRefinementTransposeCols h A d i) =
      (Equiv.sumCongr (finCongr (Nat.add_comm h A)) (Equiv.refl _))
        ((Equiv.sumComm _ _) (lambertRefinementColIndex h d A i)) := by
  simp only [lambertRefinementTransposeCols, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- The transposition sign is the sign of the exact row-column correspondence. -/
def lambertRefinementTransposeSign (h A d : ℕ) : ℤ :=
  (Equiv.Perm.sign ((lambertRefinementTransposeCols h A d).symm.trans
    (lambertRefinementTransposeRows h A d)) : ℤ)

/-- The bordered transpose permutation contributes an integer sign whose square is one. -/
theorem lambertRefinementTransposeSign_sq (h A d : ℕ) :
    lambertRefinementTransposeSign h A d ^ 2 = 1 := congrArg Units.val (Int.units_sq _)

/-- Transposing the bordered Lambert matrix interchanges the numerator length and excess pole count, up to explicit geometric diagonal factors. -/
theorem lambertRefinementBorderedMatrix_transpose (q : K) (h A b d s : ℕ)
    (hq : ∀ n : ℕ, q ^ (n + 1) ≠ 1) :
    let er := lambertRefinementTransposeRows h A d
    let ec := lambertRefinementTransposeCols h A d
    let ρ : ((Fin d ⊕ Fin h) ⊕ Fin A) → K[X] :=
      Sum.elim (fun _ => 1) (fun i => C (q ^ (s * i.val)))
    let κ : ((Fin d ⊕ Fin h) ⊕ Fin A) → K[X] :=
      fun j => Sum.elim (fun j => C (q ^ (b * j.val))) (fun _ => 1)
        ((Equiv.sumAssoc (Fin d) (Fin h) (Fin A)) j)
    diagonal ρ * (lambertRefinementBorderedMatrix q h A b d s).transpose.submatrix er ec =
      lambertRefinementBorderedMatrix q h d s A b * diagonal κ := by
  dsimp only
  apply Matrix.ext
  intro i j
  rw [diagonal_mul, mul_diagonal]
  simp only [submatrix_apply, transpose_apply, lambertRefinementBorderedMatrix_apply, transpose_rows_apply,
    transpose_cols_apply]
  rcases i with i | i <;> rcases j with (j | j) | j
  all_goals simp [lambertRefinementRowIndex, lambertRefinementColIndex, Equiv.sumAssoc,
    ← pow_add, Nat.mul_add, Nat.add_comm, Nat.mul_comm,
    lambertPoleEntry_symm q hq]

/-- The exact bordered transpose identity retains its permutation sign and both geometric monomial products. -/
theorem lambertRefinementBorderedMatrix_det_transpose (q : K) (h A b d s : ℕ)
    (hq : ∀ n : ℕ, q ^ (n + 1) ≠ 1) :
    C ((∏ i : Fin A, q ^ (s * i.val)) * (lambertRefinementTransposeSign h A d : K)) *
        (lambertRefinementBorderedMatrix q h A b d s).det =
      C (∏ i : Fin d, q ^ (b * i.val)) *
        (lambertRefinementBorderedMatrix q h d s A b).det := by
  have he := congrArg Matrix.det (lambertRefinementBorderedMatrix_transpose q h A b d s hq)
  rw [det_mul, det_diagonal, det_mul, det_diagonal] at he
  have hr : ((lambertRefinementBorderedMatrix q h A b d s).transpose.submatrix
      (lambertRefinementTransposeRows h A d) (lambertRefinementTransposeCols h A d)).det =
      C (lambertRefinementTransposeSign h A d : K) *
        (lambertRefinementBorderedMatrix q h A b d s).det := by
    have he' := det_reindex (lambertRefinementTransposeRows h A d).symm
      (lambertRefinementTransposeCols h A d).symm
      (lambertRefinementBorderedMatrix q h A b d s).transpose
    simpa only [reindex_apply, Equiv.symm_symm, det_transpose, lambertRefinementTransposeSign,
      map_intCast] using he'
  rw [hr] at he
  simp only [Fintype.prod_sum_type, Equiv.sumAssoc_apply_inl_inl,
    Equiv.sumAssoc_apply_inl_inr, Equiv.sumAssoc_apply_inr, Sum.elim_inl, Sum.elim_inr,
    prod_const_one, one_mul, mul_one, ← map_prod] at he
  rw [map_mul]
  convert he using 1 <;> ring

/-- Numerator-weighted determinants with exchanged numerator and excess-pole lengths satisfy an exact polynomial identity with explicit Vandermonde and geometric factors. -/
theorem lambertRefinementDeterminant_transpose (q : K) (h A b d s : ℕ)
    (hq : Function.Injective (fun i : ℕ => q ^ i)) :
    C ((∏ i : Fin A, q ^ (s * i.val)) * (lambertRefinementTransposeSign h A d : K) *
      ((lambertRefinementBorderedSign h A d : K) *
        (vandermonde (fun j : Fin (h + d) => q ^ (b + j.val))).det *
        (vandermonde (fun j : Fin A => q ^ j.val)).det)) *
      lambertRefinementDeterminant q h A b (h + d) s =
    C ((∏ i : Fin d, q ^ (b * i.val)) *
      ((lambertRefinementBorderedSign h d A : K) *
        (vandermonde (fun j : Fin (h + A) => q ^ (s + j.val))).det *
        (vandermonde (fun j : Fin d => q ^ j.val)).det)) *
      lambertRefinementDeterminant q h d s (h + A) b := by
  let : Infinite K := Infinite.of_injective _ hq
  have hn (k L : ℕ) : Function.Injective (fun j : Fin L => q ^ (k + j.val)) := by
    intro i j he
    exact Fin.ext (Nat.add_left_cancel (hq he))
  have hp (n : ℕ) : q ^ (n + 1) ≠ 1 := by
    intro he
    have hz := hq (he.trans (pow_zero q).symm)
    omega
  have he := lambertRefinementBorderedMatrix_det_transpose q h A b d s hp
  rw [lambertRefinementBorderedMatrix_det q h A b d s (hn b (h + d)),
    lambertRefinementBorderedMatrix_det q h d s A b (hn s (h + A))] at he
  simpa only [map_mul, mul_assoc] using he

end
end Lambert
