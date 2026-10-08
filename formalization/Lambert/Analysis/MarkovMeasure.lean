import Lambert.Analysis.IntegrationBounds

/-!
# Markov transforms and positive nodal measures
-/

namespace Lambert

open scoped Classical

open MeasureTheory

/-- The real Markov transform of a measure at a point is the integral of its reciprocal difference kernel. -/
noncomputable def markovTransform (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ t, (x - t)⁻¹ ∂μ

/-- The positive nodal density is the reciprocal product of the differences between indexed nodes and the integration point. -/
noncomputable def positiveNodalDensity {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (t : ℝ) : ℝ := (∏ i ∈ s, (x i - t))⁻¹

/-- The nodal moment measure weights the original measure by the nonnegative part of the positive nodal density. -/
noncomputable def nodalMomentMeasure {ι : Type*} (μ : Measure ℝ)
    (s : Finset ι) (x : ι → ℝ) : Measure ℝ :=
  μ.withDensity (fun t => ENNReal.ofReal (positiveNodalDensity s x t))

/-- A nodal density is strictly positive at every point below all of its nodes. -/
theorem positiveNodalDensity_pos {ι : Type*} (s : Finset ι) (x : ι → ℝ) (t : ℝ)
    (ht : ∀ i ∈ s, t < x i) : 0 < positiveNodalDensity s x t := by
  apply inv_pos.mpr
  exact Finset.prod_pos (fun i hi => sub_pos.mpr (ht i hi))

/-- A nodal density is continuous on any real set lying strictly below every node. -/
theorem positiveNodalDensity_continuousOn {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (S : Set ℝ) (hx : ∀ t ∈ S, ∀ i ∈ s, t < x i) :
    ContinuousOn (positiveNodalDensity s x) S := by
  have hp : Continuous (fun t : ℝ => ∏ i ∈ s, (x i - t)) := by fun_prop
  exact hp.continuousOn.inv₀
    (fun t ht => ne_of_gt (Finset.prod_pos (fun i hi => sub_pos.mpr (hx t ht i hi))))

end Lambert
