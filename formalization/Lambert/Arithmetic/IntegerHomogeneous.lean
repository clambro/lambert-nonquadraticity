import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Data.Real.Basic

/-!
# Homogeneous integer evaluation

The degree bound determines precisely the power clearing a rational evaluation.
-/
namespace Lambert
noncomputable section
open Polynomial
/-- Homogeneous evaluation of an integer polynomial of degree at most `d`
clears evaluation at `a/b` by exactly `b^d`. -/
theorem integerPolynomial_homogeneous_eval (p : ℤ[X]) (d : ℕ) (hd : p.natDegree ≤ d)
    (a b : ℤ) (hb : b ≠ 0) :
    (MvPolynomial.eval ![a, b] (p.homogenize d) : ℚ) =
      (p.map (Int.castRingHom ℚ)).eval ((a : ℚ) / b) * (b : ℚ) ^ d := by
  have he := Polynomial.eval_homogenize
    ((Polynomial.natDegree_map_le (f := Int.castRingHom ℚ)).trans hd)
    ![(a : ℚ), (b : ℚ)] (show (b : ℚ) ≠ 0 by exact_mod_cast hb)
  rw [Polynomial.homogenize_map] at he
  change (Int.castRingHom ℚ) (MvPolynomial.eval ![a, b] (p.homogenize d)) = _
  rw [MvPolynomial.eval₂_comp]
  have hv : (Int.castRingHom ℚ) ∘ ![a, b] = ![(a : ℚ), (b : ℚ)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simpa only [MvPolynomial.eval_map, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using he

/-- Homogeneous evaluation clears a real evaluation at a rational argument by
the same exact degree bound as rational evaluation. -/
theorem integerPolynomial_homogeneous_eval_real (p : ℤ[X]) (d : ℕ) (hd : p.natDegree ≤ d)
    (a b : ℤ) (hb : b ≠ 0) :
    (MvPolynomial.eval ![a, b] (p.homogenize d) : ℝ) =
      (p.map (Int.castRingHom ℝ)).eval ((a : ℝ) / b) * (b : ℝ) ^ d := by
  have he := Polynomial.eval_homogenize
    ((Polynomial.natDegree_map_le (f := Int.castRingHom ℝ)).trans hd)
    ![(a : ℝ), (b : ℝ)] (show (b : ℝ) ≠ 0 by exact_mod_cast hb)
  rw [Polynomial.homogenize_map] at he
  change (Int.castRingHom ℝ) (MvPolynomial.eval ![a, b] (p.homogenize d)) = _
  rw [MvPolynomial.eval₂_comp]
  have hv : (Int.castRingHom ℝ) ∘ ![a, b] = ![(a : ℝ), (b : ℝ)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simpa only [MvPolynomial.eval_map, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using he

/-- Homogeneous evaluation at the actual polynomial degree is multiplicative
on integer polynomials, including zero polynomials. -/
def integerPolynomialHomogeneousEvaluation (a b : ℤ) : ℤ[X] →*₀ ℤ where
  toFun p := MvPolynomial.eval ![a, b] (p.homogenize p.natDegree)
  map_zero' := by simp
  map_one' := by simp
  map_mul' p q := by
    by_cases hp : p = 0
    · simp [hp]
    by_cases hq : q = 0
    · simp [hq]
    rw [natDegree_mul hp hq, homogenize_mul p q le_rfl le_rfl, map_mul]

/-- Homogeneous evaluation sends the polynomial variable to the first coordinate. -/
theorem integerPolynomialHomogeneousEvaluation_X (a b : ℤ) :
    integerPolynomialHomogeneousEvaluation a b X = a := by
  simp [integerPolynomialHomogeneousEvaluation, Polynomial.homogenize_X]

end
end Lambert
