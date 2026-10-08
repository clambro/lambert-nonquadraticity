import Lambert.Arithmetic.NodalFinitePart
import Lambert.Determinants.MomentData
import Lambert.Determinants.FinitePartGenerators

/-!
# Exact finite Lambert finite-part identities

The finite identity applies to arbitrary polynomial numerators. Its error keeps
the polynomial quotient and every simple-pole boundary term explicit.
-/

namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical
variable {K : Type*} [Field K]

/-- A truncated polynomial Lambert functional is the negative geometric
sum of ordinary evaluations. -/
def lambertTruncatedPolynomial (q : K) (N : ℕ) : K[X] →ₗ[K] K :=
  -(∑ m ∈ range N, (q ^ m) • Polynomial.leval (q ^ m))

/-- The polynomial truncation has its finite weighted evaluation formula. -/
theorem lambertTruncatedPolynomial_apply (q : K) (N : ℕ) (p : K[X]) :
    lambertTruncatedPolynomial q N p = -(∑ m ∈ range N, q ^ m * p.eval (q ^ m)) := by
  simp [lambertTruncatedPolynomial]

end
end Lambert
