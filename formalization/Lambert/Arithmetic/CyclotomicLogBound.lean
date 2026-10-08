import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Uniform logarithmic bounds for cyclotomic evaluations

Möbius inversion of the divisor product reduces the error to a geometric series.
The resulting constant depends on the evaluation point but not on the cyclotomic index.
-/
namespace Lambert
noncomputable section
open Polynomial Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

private theorem log_one_sub_pow_bound (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (d : ℕ) (hd : 0 < d) : |Real.log (1 - u ^ d)| ≤ u ^ d / (1 - u) := by
  have hp : u ^ d ≤ u := by simpa only [pow_one] using pow_le_pow_of_le_one hu hu1.le (show 1 ≤ d by omega)
  have hpd : 0 < 1 - u ^ d := by linarith
  have hc : 0 < 1 - u := by linarith
  rw [abs_of_nonpos (Real.log_nonpos hpd.le (by have := pow_nonneg hu d; linarith))]
  have hl := Real.one_sub_inv_le_log_of_pos hpd
  have he : (1 - u ^ d)⁻¹ - 1 = u ^ d / (1 - u ^ d) := by field_simp; ring
  calc
    -Real.log (1 - u ^ d) ≤ (1 - u ^ d)⁻¹ - 1 := by linarith
    _ = u ^ d / (1 - u ^ d) := he
    _ ≤ u ^ d / (1 - u) := div_le_div_of_nonneg_left (pow_nonneg hu _) hc (by linarith)

/-- The logarithm of a real cyclotomic value differs from its degree times
`log q` by a constant independent of the positive cyclotomic index. -/
theorem cyclotomic_log_uniform_bound (q : ℝ) (hq : 1 < q) (n : ℕ) (hn : 0 < n) :
    |Real.log ((cyclotomic n ℝ).eval q) - (Nat.totient n : ℝ) * Real.log q| ≤
      (1 - q⁻¹)⁻¹ ^ 2 := by
  have hq0 := zero_lt_one.trans hq
  have hu : 0 ≤ q⁻¹ := (inv_pos.mpr hq0).le
  have hu1 := inv_lt_one_of_one_lt₀ hq
  have hc : 0 < 1 - q⁻¹ := sub_pos.mpr hu1
  let f : ℕ → ℝ := fun d => Real.log ((cyclotomic d ℝ).eval q) -
    (Nat.totient d : ℝ) * Real.log q
  have hs (r : ℕ) (hr : 0 < r) : ∑ d ∈ r.divisors, f d = Real.log (1 - q⁻¹ ^ r) := by
    have he := congrArg (fun p : ℝ[X] => p.eval q) (prod_cyclotomic_eq_X_pow_sub_one hr ℝ)
    simp only [eval_prod, eval_sub, eval_pow, eval_X, eval_one] at he
    dsimp only [f]
    rw [sum_sub_distrib, ← Real.log_prod (fun d _ => (cyclotomic_pos' d hq).ne'), he,
      ← sum_mul, ← Nat.cast_sum, Nat.sum_totient]
    have hp : q ^ r - 1 = q ^ r * (1 - q⁻¹ ^ r) := by
      rw [inv_pow]
      field_simp
    rw [hp, Real.log_mul (pow_pos hq0 _).ne'
      (sub_pos.mpr (pow_lt_one₀ hu hu1 hr.ne')).ne', Real.log_pow]
    ring
  have hi := (sum_eq_iff_sum_mul_moebius_eq).mp hs n hn
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℝ) * Real.log (1 - q⁻¹ ^ b))] at hi
  change |f n| ≤ _
  rw [← hi]
  calc
    _ ≤ ∑ d ∈ n.divisors, |(μ (n / d) : ℝ) * Real.log (1 - q⁻¹ ^ d)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, q⁻¹ ^ d / (1 - q⁻¹) := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul]
      have hm : |(μ (n / d) : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := n / d))
      exact (mul_le_mul_of_nonneg_right hm (abs_nonneg _)).trans
        (by simpa only [one_mul] using log_one_sub_pow_bound q⁻¹ hu hu1 d (Nat.pos_of_mem_divisors hd))
    _ ≤ ∑' d : ℕ, q⁻¹ ^ d / (1 - q⁻¹) :=
      ((summable_geometric_of_lt_one hu hu1).div_const _).sum_le_tsum _
        (fun _ _ => div_nonneg (pow_nonneg hu _) hc.le)
    _ = (1 - q⁻¹)⁻¹ ^ 2 := by
      rw [tsum_div_const, tsum_geometric_of_lt_one hu hu1]
      ring

end
end Lambert
