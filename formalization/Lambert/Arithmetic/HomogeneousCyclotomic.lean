import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Homogeneous cyclotomic values

The binary cyclotomic form is the degree-preserving homogenization of Mathlib's
integer cyclotomic polynomial.
-/

namespace Lambert

open Finset Polynomial

noncomputable section

/-- The homogeneous binary form associated with the `n`th cyclotomic polynomial. -/
def homogeneousCyclotomic (n : ℕ) : MvPolynomial (Fin 2) ℤ :=
  (cyclotomic n ℤ).homogenize (Nat.totient n)

/-- The integer value of the homogeneous `n`th cyclotomic form at `(a,b)`. -/
def homogeneousCyclotomicValue (n : ℕ) (a b : ℤ) : ℤ :=
  MvPolynomial.eval ![a, b] (homogeneousCyclotomic n)

end

end Lambert
