import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinants of rectangular products

Column multilinearity expands a rectangular product over all column selections.
Noninjective selections vanish because two selected columns coincide.
-/

namespace Lambert
open Finset Matrix
open scoped Classical

/-- A rectangular product determinant is the sum over column selections of
selected determinants times the corresponding right-hand entries. -/
theorem rectangular_det_expansion {R ι κ : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ R) (B : Matrix κ ι R) :
    (A * B).det = ∑ f : ι → κ,
      (Matrix.of fun i j => A i (f j)).det * ∏ j, B (f j) j := by
  simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
  rw [sum_comm]
  apply sum_congr rfl
  intro f _
  simp only [prod_mul_distrib, sum_mul, mul_assoc, Matrix.of_apply]

/-- A selected determinant vanishes whenever its column selection repeats
an index. -/
theorem rectangular_det_selection_zero {R ι κ : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι κ R) (f : ι → κ)
    (hf : ¬Function.Injective f) :
    (Matrix.of fun i j => A i (f j)).det = 0 := by
  obtain ⟨i, j, he, hn⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
    simpa only [Function.Injective, not_forall, exists_prop] using hf
  exact det_zero_of_column_eq hn (fun k => congrArg (A k) he)

end Lambert
