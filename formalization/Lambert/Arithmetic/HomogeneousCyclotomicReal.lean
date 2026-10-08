import Lambert.Arithmetic.HomogeneousCyclotomic
import Lambert.Arithmetic.IntegerHomogeneous
import Lambert.Arithmetic.CyclotomicLogBound

/-!
# Real homogeneous cyclotomic values and logarithmic bounds
-/
namespace Lambert
noncomputable section
open Polynomial Finset

/-- Real homogeneous cyclotomic evaluation factors into an ordinary cyclotomic
value at `a/b` and the exact denominator power. -/
theorem homogeneousCyclotomicValue_real (n : ℕ) (a b : ℤ) (hb : b ≠ 0) :
    (homogeneousCyclotomicValue n a b : ℝ) =
      (cyclotomic n ℝ).eval ((a : ℝ) / b) * (b : ℝ) ^ Nat.totient n := by
  simpa only [homogeneousCyclotomicValue, homogeneousCyclotomic, map_cyclotomic_int] using
    integerPolynomial_homogeneous_eval_real (cyclotomic n ℤ) (Nat.totient n)
      (by rw [natDegree_cyclotomic]) a b hb

/-- Homogeneous cyclotomic values are positive at positive ordered integer coordinates. -/
theorem homogeneousCyclotomicValue_pos (n : ℕ) (a b : ℤ) (hb : 0 < b) (hab : b < a) :
    0 < (homogeneousCyclotomicValue n a b : ℝ) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hq : (1 : ℝ) < (a : ℝ) / b := (one_lt_div hb0).mpr (by exact_mod_cast hab)
  rw [homogeneousCyclotomicValue_real n a b hb.ne']
  exact mul_pos (cyclotomic_pos' n hq) (pow_pos hb0 _)

/-- Homogeneous cyclotomic logarithms have a uniform error from their degree times `log a`. -/
theorem homogeneousCyclotomicValue_log_bound (n : ℕ) (hn : 0 < n)
    (a b : ℤ) (hb : 0 < b) (hab : b < a) :
    |Real.log (homogeneousCyclotomicValue n a b : ℝ) - (Nat.totient n : ℝ) * Real.log a| ≤
      (1 - ((a : ℝ) / b)⁻¹)⁻¹ ^ 2 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have ha0 : (0 : ℝ) < a := by exact_mod_cast hb.trans hab
  have hq : (1 : ℝ) < (a : ℝ) / b := (one_lt_div hb0).mpr (by exact_mod_cast hab)
  have he := cyclotomic_log_uniform_bound ((a : ℝ) / b) hq n hn
  rw [homogeneousCyclotomicValue_real n a b hb.ne',
    Real.log_mul (cyclotomic_pos' n hq).ne' (pow_pos hb0 _).ne', Real.log_pow]
  rw [Real.log_div ha0.ne' hb0.ne'] at he
  convert he using 2
  ring

end
end Lambert
