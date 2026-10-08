import Lambert.Analysis.IntegrationBounds
import Lambert.Analysis.Andreief

/-!
# Uniform density bounds for moment Gram determinants

An upper bound on a nonnegative density transfers to its Gram determinant with
one factor per matrix row. Compact support supplies all required integrability.
-/
namespace Lambert
noncomputable section
open MeasureTheory Matrix

/-- Ordered nonnegative continuous weights on compact support give ordered moment Gram determinants. -/
theorem moment_gram_det_weight_mono (μ : Measure ℝ) [IsFiniteMeasure μ]
    {S : Set ℝ} (hS : IsCompact S) (hμ : ∀ᵐ t ∂μ, t ∈ S)
    (w v : ℝ → ℝ) (hw : ContinuousOn w S) (hv : ContinuousOn v S)
    (h : ∀ t ∈ S, 0 ≤ w t ∧ w t ≤ v t) (n : ℕ) :
    (Matrix.of fun i j : Fin n => ∫ t, w t * t ^ (i.val + j.val) ∂μ).det ≤
      (Matrix.of fun i j : Fin n => ∫ t, v t * t ^ (i.val + j.val) ∂μ).det := by
  have hi (f : ℝ → ℝ) (hf : ContinuousOn f S) (i j : Fin n) :
      Integrable (fun t => f t * t ^ i.val * t ^ j.val) μ :=
    integrable_of_continuousOn_compact μ hS hμ _
      ((hf.mul (continuous_pow i.val).continuousOn).mul (continuous_pow j.val).continuousOn)
  simpa only [mul_assoc, ← pow_add] using weighted_andreief_det_mono μ w v
    (fun i : Fin n => fun t => t ^ i.val) (fun j : Fin n => fun t => t ^ j.val)
    (hi w hw) (hi v hv) (hμ.mono h)
    (Filter.Eventually.of_forall (fun _ => mul_self_nonneg _))

end
end Lambert
