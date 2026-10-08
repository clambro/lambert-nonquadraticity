import Lambert.Determinants.AlgebraicBounds
import Lambert.Determinants.NormalizedDecay
import Lambert.Analysis.BivariateDiskBound

/-! # Global conjugate bounds and distinguished decay for algebraic bases -/
namespace Lambert
noncomputable section
open Polynomial Finset Filter Topology

/-- The radial bound controls every base in a disk, including roots of unity and zero. -/
theorem lambertCircleLogBound_disk (R : ℝ) (hR : 1 < R) (u z : ℂ)
    (hu : ‖u‖ ≤ R) (h k : ℕ) :
    ‖((lambertCertificateIntegerPolynomial h k).map (eval₂RingHom (Int.castRingHom ℂ) u)).eval z‖ ≤
      Real.exp (lambertCircleLogBound h k R ‖z‖) := by
  apply integerBivariate_norm_le_on_disk _ z R (zero_lt_one.trans hR) _ ?_ u hu
  intro v hv
  simpa only [hv] using lambertCircleLogBound_bound v z (by simpa only [hv] using hR) h k

/-- The clearing factor's logarithmic modulus divided by N³ tends to (42963+428220/π²) log |u| at every point outside the unit disk. -/
theorem lambertMain_clearing_log_tendsto (u : ℂ) (hu : 1 < ‖u‖) :
    Tendsto (fun N : ℕ => Real.log ‖(lambertCertificateClearingPolynomial (60*N) (3*N)).eval₂
      (Int.castRingHom ℂ) u‖/(N : ℝ)^3) atTop
      (𝓝 ((42963+428220/Real.pi^2)*Real.log ‖u‖)) := by
  have hM := (lambertMain_clearingDegree_tendsto).mul_const (Real.log ‖u‖)
  have herr : Tendsto (fun N : ℕ =>
      (Real.log ‖(lambertCertificateClearingPolynomial (60*N) (3*N)).eval₂ (Int.castRingHom ℂ) u‖ -
        (lambertCertificateClearingPolynomial (60*N) (3*N)).natDegree * Real.log ‖u‖)/(N : ℝ)^3)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (a := fun N : ℕ => (1-‖u‖⁻¹)⁻¹^2 *
        ((∑ n ∈ Ico 1 (63*N), (lambertTranslatedCyclotomicExponent (60*N) (3*N) n : ℝ))/(N : ℝ)^3))
    · intro N
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)^3),
        ← mul_div_assoc]
      have he := lambertCertificateClearingPolynomial_log_error u hu (60*N) (3*N)
      rw [show 60*N+3*N=63*N by omega] at he
      exact div_le_div_of_nonneg_right he (by positivity)
    · simpa only [mul_zero] using lambertMain_exponent_sum_tendsto.const_mul ((1-‖u‖⁻¹)⁻¹^2)
  have he := hM.add herr
  simp only [add_zero] at he
  convert he using 1
  funext N
  ring

private theorem normalized_real_eval (q x : ℝ) (h k : ℕ) :
    (lambertNormalizedDeterminant (q : ℂ) h k).eval (x : ℂ) =
      ((lambertNormalizedDeterminant q h k).eval x : ℝ) := by
  have hm := lambertNormalizedDeterminant_map Complex.ofRealHom q h k
  change (lambertNormalizedDeterminant q h k).map Complex.ofRealHom =
    lambertNormalizedDeterminant (q : ℂ) h k at hm
  rw [← hm]
  exact eval_map_apply (p := lambertNormalizedDeterminant q h k) Complex.ofRealHom x

/-- At a real base greater than one the bivariate certificate does not vanish at the Lambert value. -/
theorem lambertCertificateIntegerPolynomial_real_ne_zero (q : ℝ) (hq : 1 < q) (h k : ℕ) :
    ((lambertCertificateIntegerPolynomial h k).map
      (eval₂RingHom (Int.castRingHom ℂ) (q : ℂ))).eval (lambertValue q : ℂ) ≠ 0 := by
  have hqc : 1 < ‖(q : ℂ)‖ := by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hq)] using hq
  have hinj : Function.Injective (fun n : ℕ => (q : ℂ)^n) := by
    intro m n he
    apply (pow_right_strictMono₀ hq).injective
    have hh := congrArg norm he
    simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hq)] using hh
  rw [lambertCertificateIntegerPolynomial_specialize _ hinj, eval_mul, eval_C,
    normalized_real_eval]
  apply mul_ne_zero (lambertCertificateClearingPolynomial_eval_ne_zero _ hqc h k)
  exact_mod_cast (lambertNormalizedDeterminant_eval_pos q hq h k).ne'

/-- The real Lambert certificate evaluation has cubic logarithmic coefficient (42963+428220/π²-202140) log q for every real q>1. -/
theorem lambertMain_algebraic_log_tendsto (q : ℝ) (hq : 1 < q) :
    Tendsto (fun N : ℕ => Real.log ‖((lambertCertificateIntegerPolynomial (60*N) (3*N)).map
      (eval₂RingHom (Int.castRingHom ℂ) (q : ℂ))).eval (lambertValue q : ℂ)‖/(N : ℝ)^3) atTop
      (𝓝 (((42963+428220/Real.pi^2)-202140)*Real.log q)) := by
  have hqc : 1 < ‖(q : ℂ)‖ := by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hq)] using hq
  have hinj : Function.Injective (fun n : ℕ => (q : ℂ)^n) := by
    intro m n he
    apply (pow_right_strictMono₀ hq).injective
    have hh := congrArg norm he
    simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hq)] using hh
  have he := (lambertMain_clearing_log_tendsto (q : ℂ) hqc).add
    (lambertMain_determinant_log_tendsto q hq)
  convert he using 1
  · funext N
    rw [lambertCertificateIntegerPolynomial_specialize _ hinj, eval_mul, eval_C,
      normalized_real_eval, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lambertNormalizedDeterminant_eval_pos q hq _ _),
      Real.log_mul (norm_ne_zero_iff.mpr (lambertCertificateClearingPolynomial_eval_ne_zero _ hqc _ _))
        (lambertNormalizedDeterminant_eval_pos q hq _ _).ne', add_div]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hq)]
    congr 1
    ring
end
end Lambert
