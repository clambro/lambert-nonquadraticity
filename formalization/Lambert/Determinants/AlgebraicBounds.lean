import Lambert.Determinants.AlgebraicSpecialization
import Lambert.Determinants.ComplexBound
import Lambert.Determinants.Exponents
import Lambert.Arithmetic.ComplexCyclotomicLogBound

/-! # Circle bounds for the bivariate Lambert certificates -/
namespace Lambert
noncomputable section
open Polynomial Finset Filter Topology

/-- The clearing polynomial degree is its zero order plus the totient-weighted cyclotomic mass. -/
theorem lambertCertificateClearingPolynomial_natDegree (h k : ℕ) :
    (lambertCertificateClearingPolynomial h k).natDegree =
      lambertCertificateClearingZeroExponent h k +
        ∑ n ∈ Ico 1 (h+k), Nat.totient n * lambertTranslatedCyclotomicExponent h k n := by
  rw [lambertCertificateClearingPolynomial, (monic_X.pow _).natDegree_mul
    (monic_prod_of_monic _ _ (fun n _ => (cyclotomic.monic n ℤ).pow _)), natDegree_X_pow,
    natDegree_prod_of_monic _ _ (fun n _ => (cyclotomic.monic n ℤ).pow _)]
  simp only [natDegree_pow, natDegree_cyclotomic, mul_comm]

/-- The main clearing polynomial degree divided by N³ tends to 42963+428220/π². -/
theorem lambertMain_clearingDegree_tendsto :
    Tendsto (fun N : ℕ =>
      ((lambertCertificateClearingPolynomial (60*N) (3*N)).natDegree : ℝ)/(N : ℝ)^3)
      atTop (𝓝 (42963+428220/Real.pi^2)) := by
  have he := lambertMain_clearingZero_tendsto.add
    (lambertMain_exponent_totient_tendsto)
  convert he using 1
  · funext N
    rw [lambertCertificateClearingPolynomial_natDegree]
    push_cast
    rw [show 60*N+3*N=63*N by omega, add_div]
  · congr 1; ring

/-- The clearing polynomial has no zeros outside the closed unit disk. -/
theorem lambertCertificateClearingPolynomial_eval_ne_zero (u : ℂ) (hu : 1 < ‖u‖) (h k : ℕ) :
    (lambertCertificateClearingPolynomial h k).eval₂ (Int.castRingHom ℂ) u ≠ 0 := by
  have hu0 : u ≠ 0 := by intro hz; norm_num [hz] at hu
  simp only [lambertCertificateClearingPolynomial, ← eval_map, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_prod, map_cyclotomic_int, eval_mul, eval_pow, eval_X, eval_prod]
  apply mul_ne_zero (pow_ne_zero _ hu0)
  exact prod_ne_zero_iff.mpr (fun n hn => pow_ne_zero _
    (cyclotomic_eval_ne_zero_of_one_lt_norm u hu n (mem_Ico.mp hn).1))

/-- The clearing factor has a uniform logarithmic error on every circle of radius greater than one. -/
theorem lambertCertificateClearingPolynomial_log_error (u : ℂ) (hu : 1 < ‖u‖) (h k : ℕ) :
    |Real.log ‖(lambertCertificateClearingPolynomial h k).eval₂ (Int.castRingHom ℂ) u‖ -
      (lambertCertificateClearingPolynomial h k).natDegree * Real.log ‖u‖| ≤
      (1-‖u‖⁻¹)⁻¹^2 * ∑ n ∈ Ico 1 (h+k), (lambertTranslatedCyclotomicExponent h k n : ℝ) := by
  have hu0 : u ≠ 0 := by intro hz; norm_num [hz] at hu
  have he : Real.log ‖(lambertCertificateClearingPolynomial h k).eval₂ (Int.castRingHom ℂ) u‖ -
      (lambertCertificateClearingPolynomial h k).natDegree * Real.log ‖u‖ =
      ∑ n ∈ Ico 1 (h+k), (lambertTranslatedCyclotomicExponent h k n : ℝ) *
        (Real.log ‖(cyclotomic n ℂ).eval u‖ - (Nat.totient n : ℝ)*Real.log ‖u‖) := by
    rw [lambertCertificateClearingPolynomial_natDegree]
    simp only [lambertCertificateClearingPolynomial, ← eval_map, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_prod, map_cyclotomic_int, eval_mul, eval_pow, eval_X, eval_prod, norm_mul, norm_pow, norm_prod]
    rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hu0))
      (prod_ne_zero_iff.mpr (fun n hn => pow_ne_zero _ (norm_ne_zero_iff.mpr
        (cyclotomic_eval_ne_zero_of_one_lt_norm u hu n (mem_Ico.mp hn).1)))),
      Real.log_pow, Real.log_prod (fun n hn => pow_ne_zero _ (norm_ne_zero_iff.mpr
        (cyclotomic_eval_ne_zero_of_one_lt_norm u hu n (mem_Ico.mp hn).1)))]
    simp_rw [Real.log_pow, mul_sub]
    push_cast
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
  exact (mul_le_mul_of_nonneg_left (cyclotomic_log_norm_uniform_bound u hu n
    (mem_Ico.mp hn).1) (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)

/-- A radial logarithmic bound for the integer certificate, uniform in the argument of the base. -/
def lambertCircleLogBound (h k : ℕ) (R Z : ℝ) : ℝ :=
  (lambertCertificateClearingPolynomial h k).natDegree * Real.log R +
    (1-R⁻¹)⁻¹^2 * (∑ n ∈ Ico 1 (h+k), (lambertTranslatedCyclotomicExponent h k n : ℝ)) +
    (h : ℝ)^2+h*(1+Z+(2*h+2*k)*(R-1)⁻¹)-h*Real.log (geometricProductFloor R⁻¹)

/-- The exponential radial bound dominates the exact bivariate certificate outside the unit disk. -/
theorem lambertCircleLogBound_bound (u z : ℂ) (hu : 1 < ‖u‖) (h k : ℕ) :
    ‖((lambertCertificateIntegerPolynomial h k).map (eval₂RingHom (Int.castRingHom ℂ) u)).eval z‖ ≤
      Real.exp (lambertCircleLogBound h k ‖u‖ ‖z‖) := by
  have hu0 : u ≠ 0 := by intro hz; norm_num [hz] at hu
  have hinj : Function.Injective (fun n : ℕ => u^n) := by
    intro m n he
    apply (pow_right_strictMono₀ hu).injective
    simpa only [norm_pow] using congrArg norm he
  rw [lambertCertificateIntegerPolynomial_specialize u hinj, eval_mul, eval_C, norm_mul]
  have hc := lambertCertificateClearingPolynomial_log_error u hu h k
  have hn := norm_pos_iff.mpr (lambertCertificateClearingPolynomial_eval_ne_zero u hu h k)
  have hcl : ‖(lambertCertificateClearingPolynomial h k).eval₂ (Int.castRingHom ℂ) u‖ ≤
      Real.exp ((lambertCertificateClearingPolynomial h k).natDegree*Real.log ‖u‖ +
        (1-‖u‖⁻¹)⁻¹^2*∑ n ∈ Ico 1 (h+k), (lambertTranslatedCyclotomicExponent h k n : ℝ)) := by
    rw [← Real.log_le_iff_le_exp hn]
    linarith [(abs_le.mp hc).2]
  apply (mul_le_mul hcl (lambertNormalizedDeterminant_norm_le_exp_of_one_lt_norm u hu z h k)
    (norm_nonneg _) (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  dsimp [lambertCircleLogBound]
  push_cast
  ring

/-- The radial logarithmic estimate divided by N³ tends to (42963+428220/π²) log R at every fixed radius and argument bound. -/
theorem lambertCircleLogBound_tendsto (R Z : ℝ) :
    Tendsto (fun N : ℕ => lambertCircleLogBound (60*N) (3*N) R Z/(N : ℝ)^3) atTop
      (𝓝 ((42963+428220/Real.pi^2)*Real.log R)) := by
  have hi : Tendsto (fun N : ℕ => (1 : ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have he := (((lambertMain_clearingDegree_tendsto).mul_const (Real.log R)).add
    (lambertMain_exponent_sum_tendsto.const_mul ((1-R⁻¹)⁻¹^2))).add
    ((hi.const_mul (3600+7560*(R-1)⁻¹)).add
      ((hi.pow 2).const_mul (60*(1+Z-Real.log (geometricProductFloor R⁻¹)))))
  simp only [mul_zero, zero_pow (by omega : 2 ≠ 0), add_zero] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  dsimp [lambertCircleLogBound]
  rw [show 60*N+3*N=63*N by omega]
  push_cast
  field_simp
  ring
end
end Lambert
