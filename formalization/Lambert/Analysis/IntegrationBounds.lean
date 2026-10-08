import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integration on compact supports and against densities
-/

namespace Lambert

open MeasureTheory

/-- A function continuous on a compact real set is integrable for every finite measure carried by that set. -/
theorem integrable_of_continuousOn_compact (μ : Measure ℝ) [IsFiniteMeasure μ]
    {S : Set ℝ} (hS : IsCompact S) (hμ : ∀ᵐ t ∂μ, t ∈ S) (f : ℝ → ℝ)
    (hf : ContinuousOn f S) : Integrable f μ := by
  have hi := hf.integrableOn_compact (μ := μ) hS
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at hi

/-- Integration against a nonnegative integrable real density equals the integral of the density times the integrand. -/
theorem integral_withDensity_ofReal_mul (μ : Measure ℝ) (w : ℝ → ℝ)
    (hw : Integrable w μ) (hn : ∀ᵐ t ∂μ, 0 ≤ w t) (g : ℝ → ℝ) :
    (∫ t, g t ∂μ.withDensity (fun t => ENNReal.ofReal (w t))) = ∫ t, w t * g t ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hw.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hn] with t ht
  simp [ENNReal.toReal_ofReal ht]

end Lambert
