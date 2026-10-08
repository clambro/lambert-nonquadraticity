import Lambert.Refinement.ZeroBlock
import Lambert.Determinants.ZeroPole

/-! # Zero-place coefficient bounds for the selected rectangular family -/
namespace Lambert
noncomputable section
open Polynomial Finset Matrix Filter
open scoped Classical WithZero Topology
variable {K : Type*} [Field K]

/-- Every nonnegative-order specialization of the selected rectangular determinant satisfies the quadratic zero-place bound. -/
theorem lambertRefinementFamily_zero_eval_valuation (z : LaurentSeries K)
    (hz : Valued.v z ≤ 1) (N : ℕ) :
    Valued.v ((lambertPoleDeterminant (lambertZeroBase K)
      (500 * N) (27 * N) (516 * N) (41 * N)).eval z) ≤
        WithZero.exp (lambertRefinementZeroExponent N : ℤ) := by
  apply lambertPoleDeterminant_zero_eval_valuation_of_blocks
    (500*N) (27*N) (516*N) (41*N) (lambertRefinementZeroExponent N) ?_ z hz
  intro Z hZ m hm
  have he := lambertRefinementZeroBlock_det_valuation Z hZ N (m-27*N)
  rw [lambertRefinementZeroBlock_mul, show 27*N+(m-27*N)=m by omega] at he
  exact he

/-- Every coefficient of the selected rectangular determinant satisfies the same zero-place bound. -/
theorem lambertRefinementFamily_zero_coeff_valuation (N i : ℕ) :
    Valued.v (lambertZeroMap ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ)
      (500 * N) (27 * N) (516 * N) (41 * N)).coeff i)) ≤
        WithZero.exp (lambertRefinementZeroExponent N : ℤ) := by
  exact lambertPoleDeterminant_zero_coeff_valuation_of_eval
    (500*N) (27*N) (516*N) (41*N) (lambertRefinementZeroExponent N)
    (fun z hz => lambertRefinementFamily_zero_eval_valuation z hz N) i

end
end Lambert
