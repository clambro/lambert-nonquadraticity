import Lambert.Analysis.AtomicMoment
import Lambert.Analysis.MarkovMeasure
import Lambert.Arithmetic.GeometricMoments

/-! # Geometric Markov integral and convergence -/
namespace Lambert
open MeasureTheory Polynomial

/-- The Markov transform of the geometric moment measure is its geometric reciprocal series. -/
theorem markovTransform_geometricMomentMeasure_eq (q x : ℝ) (hq : 0 ≤ q) :
    markovTransform (geometricMomentMeasure q) x =
      ∑' k : ℕ, q ^ (k + 1) / (x - q ^ (k + 1)) := by
  simpa only [markovTransform, geometricMomentMeasure, div_eq_mul_inv] using
    integral_discreteMomentMeasure _ _ (fun k => pow_nonneg hq (k + 1))
      (fun t => (x - t)⁻¹)

/-- The geometric reciprocal series converges at every point strictly above the geometric moment support. -/
theorem summable_geometricMarkov (q x : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hx : q < x) : Summable (fun k : ℕ => q ^ (k + 1) / (x - q ^ (k + 1))) := by
  let μ := geometricMomentMeasure q
  let : IsFiniteMeasure μ := geometricMomentMeasure_isFinite q hq hq1
  have hμ := geometricMomentMeasure_ae_mem q hq hq1.le
  have hf : Integrable (fun t => (x - t)⁻¹) μ := by
    apply integrable_of_continuousOn_compact μ isCompact_Icc hμ
    exact (continuous_const.sub continuous_id).continuousOn.inv₀
      (fun t ht => ne_of_gt (sub_pos.mpr (ht.2.trans_lt hx)))
  have hs := (hasSum_integral_measure (μ := fun k =>
    ENNReal.ofReal (q ^ (k + 1)) • Measure.dirac (q ^ (k + 1))) hf).summable
  simpa only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (pow_nonneg hq _), smul_eq_mul, div_eq_mul_inv] using hs


/-- Scaling a geometric Markov sample outward by the reciprocal ratio removes exactly the first reciprocal-series term. -/
theorem markovTransform_geometric_shift (q x : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hx : q < x) :
    markovTransform (geometricMomentMeasure q) (x / q) =
      markovTransform (geometricMomentMeasure q) x - q / (x - q) := by
  rw [markovTransform_geometricMomentMeasure_eq q (x / q) hq.le,
    markovTransform_geometricMomentMeasure_eq q x hq.le]
  have hterm (k : ℕ) : q ^ (k + 1) / (x / q - q ^ (k + 1)) =
      q ^ (k + 1 + 1) / (x - q ^ (k + 1 + 1)) := by
    rw [div_sub' hq.ne', div_div_eq_mul_div]
    simp only [← pow_succ, ← pow_succ']
  simp_rw [hterm]
  have hs := (summable_geometricMarkov q x hq.le hq1 hx).tsum_eq_zero_add
  simp only [zero_add, pow_one] at hs
  linarith

/-- Every outward geometric orbit sample differs from the initial Markov sample by an explicit finite reciprocal prefix. -/
theorem markovTransform_geometric_orbit (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (j : ℕ) :
    markovTransform (geometricMomentMeasure q) (1 / q ^ j) =
      markovTransform (geometricMomentMeasure q) 1 -
        geometricMomentPrefix q⁻¹ j := by
  rw [geometricMomentPrefix_inv q hq.ne' j]
  induction j with
  | zero => simp
  | succ j ih =>
      have hpow := pow_pos hq j
      have hone : 1 ≤ 1 / q ^ j :=
        (le_div_iff₀ hpow).mpr (by simpa using pow_le_one₀ hq.le hq1.le (n := j))
      have hh := markovTransform_geometric_shift q (1 / q ^ j) hq hq1
        (hq1.trans_le hone)
      have hnode : (1 / q ^ j) / q = 1 / q ^ (j + 1) := by
        rw [div_div, pow_succ]
      have hterm : q / (1 / q ^ j - q) = q ^ (j + 1) / (1 - q ^ (j + 1)) := by
        rw [div_sub' hpow.ne', div_div_eq_mul_div]
        simp only [← pow_succ, ← pow_succ']
      rw [hnode, hterm, ih] at hh
      rw [Finset.sum_range_succ]
      linarith


end Lambert
