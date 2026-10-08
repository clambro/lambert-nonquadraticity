import Lambert.Determinants.ZeroBlock
import Lambert.Refinement.ZeroCost

/-! # Rectangular finite-part blocks for the selected numerator family -/
namespace Lambert
noncomputable section
open Finset Matrix
open scoped Classical WithZero
variable {K : Type*} [Field K]

/-- Every selected rectangular permutation cost is bounded by the quadratic zero-pole exponent. -/
theorem lambertRefinementZero_selection_cost_bound (N M : ℕ)
    (f : Fin (500 * N) → Fin M) (hf : Function.Injective f) (σ : Equiv.Perm (Fin (500 * N))) :
    -(lambertRefinementZeroExponent N : ℤ) ≤
      ∑ r : Fin (500 * N), (((σ r).val : ℤ) * lambertSlotNode (27 * N) (f r).val +
        (lambertSlotNode (27 * N) (f r).val : ℤ) * (r.val + 41 * N) +
          lambertZeroWeightOrder (27 * N) (516 * N) (lambertSlotNode (27 * N) (f r).val)) := by
  apply slotSelection_cost_bound (500 * N) M (lambertSlotNode (27 * N))
    (lambertSlotNode_mono (27 * N)) (lambertZeroWeightOrder (27 * N) (516 * N))
    (41 * N) (-(lambertRefinementZeroExponent N : ℤ)) ?_ f hf σ
  intro j hj
  have hp := sum_le_sum (fun r (_ : r ∈ (univ : Finset (Fin (500 * N)))) =>
    lambertRefinementZeroQuadratic_le_cost N r.val (j r) r.isLt (hj r))
  rw [← mul_sum] at hp
  have he := lambertRefinementZeroExponent_bound N
  rw [← Fin.sum_univ_eq_sum_range] at he
  have hc : -(lambertRefinementZeroExponent N : ℤ) ≤
      ∑ r : Fin (500 * N), lambertRefinementZeroCost N r.val (j r) := by omega
  simpa only [lambertRefinementZeroCost, Nat.cast_mul, Nat.cast_ofNat] using hc

/-- The rectangular left block selects the first 500N monomial rows of the 516N-pole finite-part block. -/
def lambertRefinementZeroBlockLeft (K : Type*) [Field K] (N M : ℕ) :
    Matrix (Fin (500 * N)) (Fin (27 * N + 2 * M)) (LaurentSeries K) :=
  (lambertZeroBlockLeft K (516 * N) (27 * N) M).submatrix
    (fun i => ⟨i.val, by omega⟩) id

/-- The rectangular right block uses the 516N-pole weights and moment shift 41N. -/
def lambertRefinementZeroBlockRight (Z : LaurentSeries K) (N M : ℕ) :
    Matrix (Fin (27 * N + 2 * M)) (Fin (500 * N)) (LaurentSeries K) :=
  lambertTranslatedZeroBlockRight Z (500*N) (27*N) (516*N) (41*N) M

/-- Every finite compressed block of the selected rectangular family obeys the quadratic zero-pole bound. -/
theorem lambertRefinementZeroBlock_det_valuation (Z : LaurentSeries K) (hZ : Valued.v Z ≤ 1)
    (N M : ℕ) :
    Valued.v (lambertRefinementZeroBlockLeft K N M * lambertRefinementZeroBlockRight Z N M).det ≤
      WithZero.exp (lambertRefinementZeroExponent N : ℤ) := by
  exact lambertTranslatedZeroBlock_det_valuation Z hZ
    (500*N) (27*N) (516*N) (41*N) M (lambertRefinementZeroExponent N)
    (lambertRefinementZero_selection_cost_bound N (27*N+2*M))

/-- Multiplying the selected finite-part blocks gives the rank-500N moment matrix on the 516N pole window with shift 41N. -/
theorem lambertRefinementZeroBlock_mul (Z : LaurentSeries K) (N M : ℕ) :
    lambertRefinementZeroBlockLeft K N M * lambertRefinementZeroBlockRight Z N M =
      Matrix.of (fun i j : Fin (500 * N) => lambertZeroBlockMoment Z
        (27 * N) (516 * N) (27 * N + M) (i.val + j.val + 41 * N)) := by
  exact lambertTranslatedZeroBlock_mul Z (500*N) (27*N) (516*N) (41*N) M

end
end Lambert
