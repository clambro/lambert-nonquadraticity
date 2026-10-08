import Lambert.Determinants.BorderedFiltration
import Lambert.Refinement.Moments
import Lambert.Determinants.LocalMap

/-! # Local regularization of numerator-bordered Lambert determinants -/
namespace Lambert
noncomputable section
open PowerSeries Matrix Finset
open scoped Classical WithZero
variable {K : Type*} [Field K] [Algebra ℚ K]

private def localRows (h A d : ℕ) :
    Fin (h + d + A) ≃ ((Fin A ⊕ Fin h) ⊕ Fin d) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans (lambertRefinementColIndex h A d).symm)

private def localCols (h A d : ℕ) :
    Fin (h + d + A) ≃ ((Fin A ⊕ Fin h) ⊕ Fin d) :=
  (finCongr (show h + d + A = A + h + d by omega)).trans
    (finSumFinEquiv.symm.trans (lambertRefinementRowIndex h A d).symm)

private theorem rows_apply (h A d : ℕ) (i : Fin (h + d + A)) :
    lambertRefinementColIndex h A d (localRows h A d i) =
      (Equiv.sumComm _ _) (finSumFinEquiv.symm i) := by
  simp only [localRows, Equiv.trans_apply, Equiv.apply_symm_apply]

private theorem cols_apply (h A d : ℕ) (i : Fin (h + d + A)) :
    lambertRefinementRowIndex h A d (localCols h A d i) =
      finSumFinEquiv.symm (Fin.cast (show h + d + A = A + h + d by omega) i) := by
  simp only [localCols, Equiv.trans_apply, Equiv.apply_symm_apply, finCongr_apply]

/-- The local bordered sign records the exact pole-evaluation reindexing and nodal normalization. -/
def lambertBorderedLocalSign (h A d : ℕ) : ℤ :=
  (Equiv.Perm.sign ((localCols h A d).symm.trans (localRows h A d)) : ℤ) *
    lambertRefinementBorderedSign h A d

/-- The local bordered normalization is an integer sign whose square is one. -/
theorem lambertBorderedLocalSign_sq (h A d : ℕ) : lambertBorderedLocalSign h A d ^ 2 = 1 := by
  have hp : (Equiv.Perm.sign ((localCols h A d).symm.trans (localRows h A d)) : ℤ) ^ 2 = 1 :=
    congrArg Units.val (Int.units_sq _)
  rw [lambertBorderedLocalSign, mul_pow, hp, lambertRefinementBorderedSign_sq, one_mul]

/-- Local regularization of a numerator-bordered determinant introduces exactly one parameter factor per moment rank and the evaluation-row geometric monomial. -/
theorem lambertBorderedLocalMatrix_identity (ζ x : K) (hz : ζ ≠ 0) (h A b d s : ℕ) :
    let f := HahnSeries.ofPowerSeries ℤ K
    f (lambertBorderedLocalMatrix ζ x h A b d s).det =
      f (PowerSeries.X : PowerSeries K) ^ h *
        (∏ i : Fin A, f (lambertLocalBase ζ) ^ (s * i.val)) *
        (lambertBorderedLocalSign h A d : LaurentSeries K) *
        f (vandermonde (fun j : Fin (h + d) => lambertLocalBase ζ ^ (b + j.val))).det *
        f (vandermonde (fun j : Fin A => lambertLocalBase ζ ^ j.val)).det *
        ((lambertRefinementDeterminant (RatFunc.X : RatFunc ℚ) h A b (h + d) s).map
          (lambertLocalMap ζ hz)).eval (algebraMap K (LaurentSeries K) x) := by
  let f := HahnSeries.ofPowerSeries ℤ K
  let g := lambertLocalMap ζ hz
  let z := algebraMap K (LaurentSeries K) x
  let B := (Polynomial.eval₂RingHom g z).mapMatrix
    (lambertRefinementBorderedMatrix RatFunc.X h A b d s)
  let ρ : Fin (h + d + A) → LaurentSeries K :=
    Fin.addCases (fun _ => 1) (fun _ => f PowerSeries.X)
  let μ : Fin (h + d + A) → LaurentSeries K :=
    Fin.addCases (fun _ => 1) (fun i => f (lambertLocalBase ζ) ^ (s * i.val))
  let κ : Fin (h + d + A) → LaurentSeries K :=
    fun j => if j.val < h + A then f PowerSeries.X else 1
  have hm : diagonal ρ * f.mapMatrix (lambertBorderedLocalMatrix ζ x h A b d s) =
      diagonal μ * B.transpose.submatrix (localRows h A d) (localCols h A d) * diagonal κ := by
    apply Matrix.ext
    intro i j
    rw [diagonal_mul, mul_diagonal, diagonal_mul]
    simp only [B, submatrix_apply, transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      lambertRefinementBorderedMatrix_apply, cols_apply, rows_apply]
    obtain ⟨j, rfl⟩ := (finCongr (show A + h + d = h + d + A by omega)).surjective j
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ j
      · intro j
        have hj : j.val < h + A := by omega
        simp [lambertBorderedLocalMatrix, lambertBorderedLocalColumn, ρ, μ, κ, hj]
        rw [lambertLocalEntry_symm ζ x (b + i.val),
          lambertLocalEntry_map f HahnSeries.ofPowerSeries_injective,
          Polynomial.eval₂_eq_eval_map, lambertPoleEntry_map,
          lambertLocalMap_X]
        have hc : f (C x) = z := by simp [f, z, LaurentSeries.algebraMap_apply]
        rw [hc]
        simp only [Nat.add_comm s, mul_comm, f]
      · intro j
        have hj : ¬(A + h + j.val < h + A) := by omega
        simp [lambertBorderedLocalMatrix, lambertBorderedPolynomialColumn,
          ρ, μ, κ, hj, g, lambertLocalMap_X, f, Polynomial.eval₂_pow, Polynomial.eval₂_C,
          show A + h + j.val - (h + A) = j.val by omega]
    · intro i
      refine Fin.addCases ?_ ?_ j
      · intro j
        have hj : j.val < h + A := by omega
        simp [lambertBorderedLocalMatrix, lambertBorderedLocalColumn,
          ρ, μ, κ, hj, g, lambertLocalMap_X, f, pow_add, Nat.mul_add,
          Polynomial.eval₂_pow, Polynomial.eval₂_C, mul_comm]
      · intro j
        have hj : ¬(A + h + j.val < h + A) := by omega
        simp [lambertBorderedLocalMatrix, lambertBorderedPolynomialColumn, ρ, μ, κ, hj]
  have hd := congrArg Matrix.det hm
  rw [det_mul, det_diagonal, ← f.map_det, det_mul, det_mul, det_diagonal, det_diagonal] at hd
  have hr : ∏ i, ρ i = f PowerSeries.X ^ A := by simp [ρ, Fin.prod_univ_add]
  have hμ : ∏ i, μ i = ∏ i : Fin A, f (lambertLocalBase ζ) ^ (s * i.val) := by
    simp [μ, Fin.prod_univ_add]
  have hκ : ∏ j, κ j = f PowerSeries.X ^ (h + A) := by
    rw [← (finCongr (show h + A + d = h + d + A by omega)).prod_comp]
    simp [κ, Fin.prod_univ_add]
  have hb : (B.transpose.submatrix (localRows h A d) (localCols h A d)).det =
      (((Equiv.Perm.sign ((localCols h A d).symm.trans (localRows h A d)) : ℤ) : LaurentSeries K)) *
        B.det := by
    simpa only [reindex_apply, Equiv.symm_symm, det_transpose] using
      det_reindex (localRows h A d).symm (localCols h A d).symm B.transpose
  rw [hr, hμ, hκ, hb] at hd
  have hnode : Function.Injective (fun j : Fin (h + d) => (RatFunc.X : RatFunc ℚ) ^ (b + j.val)) := by
    intro i j he
    exact Fin.ext (Nat.add_left_cancel (ratFunc_X_pow_injective he))
  let : Infinite (RatFunc ℚ) := Infinite.of_injective _ ratFunc_X_pow_injective
  have he := congrArg (Polynomial.eval₂ g z)
    (lambertRefinementBorderedMatrix_det RatFunc.X h A b d s hnode)
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C] at he
  change (Polynomial.eval₂RingHom g z) _ = _ at he
  rw [(Polynomial.eval₂RingHom g z).map_det] at he
  change B.det = _ at he
  have hv (k L : ℕ) : g (vandermonde (fun j : Fin L => (RatFunc.X : RatFunc ℚ) ^ (k + j.val))).det =
      f (vandermonde (fun j : Fin L => lambertLocalBase ζ ^ (k + j.val))).det := by
    rw [g.map_det, f.map_det]
    congr 1
    ext i j
    simp [g, lambertLocalMap_X, f, vandermonde_apply]
  rw [map_mul, map_mul, map_intCast, hv] at he
  have hv0 := hv 0 A
  simp only [Nat.zero_add] at hv0
  rw [hv0, Polynomial.eval₂_eq_eval_map] at he
  rw [he] at hd
  have hx : f (PowerSeries.X : PowerSeries K) ≠ 0 :=
    (map_ne_zero_iff f HahnSeries.ofPowerSeries_injective).mpr PowerSeries.X_ne_zero
  apply mul_left_cancel₀ (pow_ne_zero A hx)
  rw [hd]
  simp only [lambertBorderedLocalSign, Int.cast_mul, pow_add]
  ring

end
end Lambert
