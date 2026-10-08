import Lambert.Determinants.LocalMap
import Lambert.Determinants.Determinant
import Lambert.Determinants.MomentsMap
import Lambert.Determinants.TaylorFiltration

/-!
# Regularized augmented Lambert matrices

Only the Lambert columns of the transposed augmented matrix require multiplication
by the local parameter. The extra polynomial columns remain regular.
-/
namespace Lambert
noncomputable section
open PowerSeries Matrix Finset
open scoped Classical WithZero
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The regularized transposed augmented matrix retains unscaled polynomial columns. -/
def lambertCertificateLocalMatrix (ζ x : K) (h k d s : ℕ) :
    Matrix (Fin (h + d)) (Fin (h + d)) (PowerSeries K) := fun i j =>
  Fin.addCases (fun r => lambertLocalEntry ζ x (r.val + s) (k+i.val))
    (fun r => lambertLocalBase ζ ^ ((k+i.val) * r.val)) j

/-- The regularized augmented determinant is the original determinant times exactly one parameter factor per Lambert column. -/
theorem lambertCertificateLocalMatrix_identity (ζ x : K) (hz : ζ ≠ 0) (h k d s : ℕ) :
    (HahnSeries.ofPowerSeries ℤ K) (lambertCertificateLocalMatrix ζ x h k d s).det =
      (HahnSeries.ofPowerSeries ℤ K) (PowerSeries.X : PowerSeries K) ^ h *
        ((lambertAugmentedSign h d : LaurentSeries K) *
          (HahnSeries.ofPowerSeries ℤ K)
            (vandermonde (fun j : Fin (h + d) => lambertLocalBase ζ ^ (k+j.val))).det) *
        ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s).map
          (lambertLocalMap ζ hz)).eval (algebraMap K (LaurentSeries K) x) := by
  let f := HahnSeries.ofPowerSeries ℤ K
  let g := lambertLocalMap ζ hz
  let z := algebraMap K (LaurentSeries K) x
  let A := (Polynomial.eval₂RingHom g z).mapMatrix (lambertAugmentedMatrix RatFunc.X h k d s)
  let c : Fin (h + d) → LaurentSeries K := Fin.addCases (fun _ => f X) (fun _ => 1)
  have hm : f.mapMatrix (lambertCertificateLocalMatrix ζ x h k d s) = A.transpose * diagonal c := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_diagonal]
    refine Fin.addCases ?_ ?_ j
    · intro r
      simp only [lambertCertificateLocalMatrix, Fin.addCases_left, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.transpose_apply, A, c, lambertAugmentedMatrix, g]
      rw [lambertLocalEntry_map f HahnSeries.ofPowerSeries_injective,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_eval_map, lambertPoleEntry_map, lambertLocalMap_X]
      have hc : f (C x) = z := by simp [f, z, LaurentSeries.algebraMap_apply]
      rw [hc, mul_comm]
    · intro r
      simp only [lambertCertificateLocalMatrix, Fin.addCases_right, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.transpose_apply, A, c, lambertAugmentedMatrix, g, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_pow, Polynomial.eval₂_C,
        map_pow, lambertLocalMap_X, mul_one]
      rfl
  have hd := f.map_det (lambertCertificateLocalMatrix ζ x h k d s)
  rw [hm, det_mul, det_transpose, det_diagonal] at hd
  have hc : (∏ j, c j) = f X ^ h := by
    simp [c, Fin.prod_univ_add]
  rw [hc] at hd
  have he := congrArg (Polynomial.eval₂ g z) (lambertAugmentedMatrix_det_formal h k d s)
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C] at he
  change (Polynomial.eval₂RingHom g z) _ = _ at he
  rw [(Polynomial.eval₂RingHom g z).map_det] at he
  change A.det = _ at he
  have hv : g (vandermonde (fun j : Fin (h + d) => RatFunc.X ^ (k+j.val))).det =
      f (vandermonde (fun j : Fin (h + d) => lambertLocalBase ζ ^ (k+j.val))).det := by
    rw [g.map_det, f.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, vandermonde, Matrix.of_apply, map_pow, g, lambertLocalMap_X]
    rfl
  rw [map_mul, map_intCast, hv, Polynomial.eval₂_eq_eval_map] at he
  rw [he] at hd
  exact hd.trans (by dsimp only [g, z]; ring)

end
end Lambert
