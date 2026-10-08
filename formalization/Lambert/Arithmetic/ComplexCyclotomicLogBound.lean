import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-! # Uniform cyclotomic logarithm bounds at complex points -/
namespace Lambert
noncomputable section
open Polynomial Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Cyclotomic polynomials do not vanish outside the closed unit disk. -/
theorem cyclotomic_eval_ne_zero_of_one_lt_norm (u : ℂ) (hu : 1 < ‖u‖)
    (n : ℕ) (hn : 0 < n) : (cyclotomic n ℂ).eval u ≠ 0 := by
  intro hz
  have he := eval_eq_zero_of_dvd_of_eval_eq_zero (cyclotomic.dvd_X_pow_sub_one n ℂ) hz
  simp only [eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] at he
  have hh := congrArg norm he
  rw [norm_pow, norm_one] at hh
  have := one_lt_pow₀ hu hn.ne'
  linarith

private theorem log_norm_one_sub_pow_bound (v : ℂ) (hv : ‖v‖ < 1)
    (d : ℕ) (hd : 0 < d) : |Real.log ‖1-v^d‖| ≤ ‖v‖^d/(1-‖v‖) := by
  have hp : ‖v‖^d ≤ ‖v‖ := by
    simpa only [pow_one] using pow_le_pow_of_le_one (norm_nonneg v) hv.le (show 1 ≤ d by omega)
  have hc : 0 < 1-‖v‖ := sub_pos.mpr hv
  have hlo : 1-‖v‖^d ≤ ‖1-v^d‖ := by simpa only [norm_one, norm_pow] using norm_sub_norm_le (1 : ℂ) (v^d)
  have hhi : ‖1-v^d‖ ≤ 1+‖v‖^d := by simpa only [norm_one, norm_pow] using norm_sub_le (1 : ℂ) (v^d)
  have hz : 0 < ‖1-v^d‖ := by linarith
  have hfrac : ‖v‖^d ≤ ‖v‖^d/(1-‖v‖) := by
    apply le_div_self (pow_nonneg (norm_nonneg _) _) (by linarith) (by linarith [norm_nonneg v])
  rw [abs_le]
  constructor
  · have ha := Real.one_sub_inv_le_log_of_pos hz
    have hb : ‖1-v^d‖⁻¹ ≤ (1-‖v‖)⁻¹ := inv_anti₀ hc (by linarith)
    have hpd : 1-‖v‖^d ≠ 0 := by linarith
    have he : (1-‖v‖^d)⁻¹-1 = ‖v‖^d/(1-‖v‖^d) := by field_simp; ring
    have hb' : ‖1-v^d‖⁻¹ ≤ (1-‖v‖^d)⁻¹ := inv_anti₀ (by linarith) hlo
    have hf := div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg v) d) hc
      (show 1-‖v‖ ≤ 1-‖v‖^d by linarith)
    linarith
  · have := Real.log_le_sub_one_of_pos hz
    linarith

/-- The logarithm of the modulus of a complex cyclotomic value differs from its degree main term by a bound independent of the index and argument. -/
theorem cyclotomic_log_norm_uniform_bound (u : ℂ) (hu : 1 < ‖u‖) (n : ℕ) (hn : 0 < n) :
    |Real.log ‖(cyclotomic n ℂ).eval u‖ - (Nat.totient n : ℝ)*Real.log ‖u‖| ≤
      (1-‖u‖⁻¹)⁻¹^2 := by
  have hu0 : u ≠ 0 := by intro hz; norm_num [hz] at hu
  have hv : ‖u⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hu
  have hc : 0 < 1-‖u‖⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hu)
  let f : ℕ → ℝ := fun d => Real.log ‖(cyclotomic d ℂ).eval u‖ -
    (Nat.totient d : ℝ)*Real.log ‖u‖
  have hs (r : ℕ) (hr : 0 < r) : ∑ d ∈ r.divisors, f d = Real.log ‖1-u⁻¹^r‖ := by
    have he := congrArg (fun p : ℂ[X] => ‖p.eval u‖) (prod_cyclotomic_eq_X_pow_sub_one hr ℂ)
    simp only [eval_prod, eval_sub, eval_pow, eval_X, eval_one, norm_prod] at he
    dsimp only [f]
    rw [sum_sub_distrib, ← Real.log_prod (fun d hd => norm_ne_zero_iff.mpr
      (cyclotomic_eval_ne_zero_of_one_lt_norm u hu d (Nat.pos_of_mem_divisors hd))), he,
      ← sum_mul, ← Nat.cast_sum, Nat.sum_totient]
    have hp : u^r-1 = u^r*(1-u⁻¹^r) := by rw [inv_pow]; field_simp
    have hnz : 1-u⁻¹^r ≠ 0 := by
      intro hz
      have hh : u⁻¹^r=1 := by linear_combination -hz
      have hh' := congrArg norm hh
      rw [norm_pow, norm_one] at hh'
      have := pow_lt_one₀ (norm_nonneg (u⁻¹)) hv hr.ne'
      linarith
    rw [hp, norm_mul, norm_pow, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hu0))
      (norm_ne_zero_iff.mpr hnz), Real.log_pow]
    ring
  have hi := (sum_eq_iff_sum_mul_moebius_eq).mp hs n hn
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℝ)*Real.log ‖1-u⁻¹^b‖)] at hi
  change |f n| ≤ _
  rw [← hi]
  calc
    _ ≤ ∑ d ∈ n.divisors, |(μ (n/d) : ℝ)*Real.log ‖1-u⁻¹^d‖| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, ‖u‖⁻¹^d/(1-‖u‖⁻¹) := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul]
      have hm : |(μ (n/d) : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := n/d))
      exact (mul_le_mul_of_nonneg_right hm (abs_nonneg _)).trans
        (by simpa only [one_mul, norm_inv] using (log_norm_one_sub_pow_bound (u⁻¹) hv d (Nat.pos_of_mem_divisors hd)))
    _ ≤ ∑' d : ℕ, ‖u‖⁻¹^d/(1-‖u‖⁻¹) :=
      ((summable_geometric_of_lt_one (inv_nonneg.mpr (norm_nonneg _))
        (inv_lt_one_of_one_lt₀ hu)).div_const _).sum_le_tsum _
          (fun _ _ => div_nonneg (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _) hc.le)
    _ = (1-‖u‖⁻¹)⁻¹^2 := by
      rw [tsum_div_const, tsum_geometric_of_lt_one (inv_nonneg.mpr (norm_nonneg _))
        (inv_lt_one_of_one_lt₀ hu)]
      ring
end
end Lambert
