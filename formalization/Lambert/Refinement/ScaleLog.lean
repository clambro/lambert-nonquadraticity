import Lambert.Refinement.IntegerReal

/-! # Uniform logarithmic error of shifted cyclotomic clearing scales -/
namespace Lambert
noncomputable section
open Polynomial Finset

/-- The shifted integer scale's logarithm differs from its degree main term by
at most a uniform cyclotomic constant times the total pole exponent. -/
theorem lambertRefinementIntegerScale_log_error (N : ℕ) (a b : ℤ) (hb : 0 < b) (hab : b < a) :
    |Real.log (lambertRefinementIntegerScale N a b : ℝ) -
      ((lambertRefinementClearingZeroExponent N : ℝ) + ∑ n ∈ Ico 1 (543*N),
        (Nat.totient n : ℝ) * lambertRefinementClearingExponent N n) * Real.log a| ≤
      (1 - ((a : ℝ) / b)⁻¹)⁻¹ ^ 2 *
        ∑ n ∈ Ico 1 (543*N), (lambertRefinementClearingExponent N n : ℝ) := by
  have ha : (0 : ℝ) < a := by exact_mod_cast hb.trans hab
  have he : Real.log (lambertRefinementIntegerScale N a b : ℝ) -
      ((lambertRefinementClearingZeroExponent N : ℝ) + ∑ n ∈ Ico 1 (543*N),
        (Nat.totient n : ℝ) * lambertRefinementClearingExponent N n) * Real.log a =
      ∑ n ∈ Ico 1 (543*N), (lambertRefinementClearingExponent N n : ℝ) *
        (Real.log (homogeneousCyclotomicValue n a b : ℝ) - (Nat.totient n : ℝ) * Real.log a) := by
    simp only [lambertRefinementIntegerScale, Int.cast_mul, Int.cast_pow, Int.cast_prod]
    rw [Real.log_mul (pow_pos ha _).ne'
      (prod_pos (fun n _ => pow_pos (homogeneousCyclotomicValue_pos n a b hb hab) _)).ne',
      Real.log_pow, Real.log_prod (fun n _ => (pow_pos (homogeneousCyclotomicValue_pos n a b hb hab) _).ne')]
    simp_rw [Real.log_pow, mul_sub]
    rw [sum_sub_distrib, add_mul, sum_mul]
    ring_nf
    congr 1
    apply sum_congr rfl
    intro n _
    ring
  rw [he, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n hn
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact (mul_le_mul_of_nonneg_left
    (homogeneousCyclotomicValue_log_bound n (mem_Ico.mp hn).1 a b hb hab) (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)

end
end Lambert
