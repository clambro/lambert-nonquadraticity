import Lambert.Analysis.IntegrationBounds

/-!
# Positive discrete moment measures

Summable positive masses at distinct real nodes give finite nondegenerate
moment measures. Geometric nodes are a concrete instance, not an atomless
substitute or an assumed positivity hypothesis.
-/

namespace Lambert

open MeasureTheory

/-- The discrete moment measure puts the nonnegative part of each weight at its indexed real node. -/
noncomputable def discreteMomentMeasure (w x : ℕ → ℝ) : Measure ℝ :=
  Measure.sum (fun k => ENNReal.ofReal (w k) • Measure.dirac (x k))

/-- Integration against a discrete moment measure with nonnegative weights is the corresponding weighted real series. -/
theorem integral_discreteMomentMeasure (w x : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (f : ℝ → ℝ) :
    (∫ t, f t ∂discreteMomentMeasure w x) = ∑' k, w k * f (x k) := by
  simpa only [discreteMomentMeasure, ENNReal.toReal_ofReal (hw _), smul_eq_mul] using
    integral_sum_dirac (f := f) (x := x) (c := fun k => ENNReal.ofReal (w k))
      (fun _ => ENNReal.ofReal_ne_top)

/-- Summable real weights define a finite discrete moment measure. -/
theorem discreteMomentMeasure_isFinite (w x : ℕ → ℝ) (hw : Summable w) :
    IsFiniteMeasure (discreteMomentMeasure w x) := by
  constructor
  simpa [discreteMomentMeasure, Measure.sum_apply, Measure.smul_apply] using hw.tsum_ofReal_lt_top

/-- A discrete moment measure is carried by any measurable set containing every node. -/
theorem discreteMomentMeasure_ae_mem (w x : ℕ → ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (hx : ∀ k, x k ∈ S) :
    ∀ᵐ t ∂discreteMomentMeasure w x, t ∈ S := by
  rw [ae_iff]
  change discreteMomentMeasure w x Sᶜ = 0
  simp [discreteMomentMeasure, Measure.sum_apply, hS.compl, Measure.smul_apply,
    Measure.dirac_apply' _ hS.compl, hx]

/-- The geometric moment measure puts mass `q^(k+1)` at the node `q^(k+1)` for each nonnegative integer `k`. -/
noncomputable def geometricMomentMeasure (q : ℝ) : Measure ℝ :=
  discreteMomentMeasure (fun k => q ^ (k + 1)) (fun k => q ^ (k + 1))

/-- A geometric moment measure with ratio in `[0,1]` is carried by the compact interval from zero to that ratio. -/
theorem geometricMomentMeasure_ae_mem (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ᵐ t ∂geometricMomentMeasure q, t ∈ Set.Icc (0 : ℝ) q := by
  apply discreteMomentMeasure_ae_mem _ _ measurableSet_Icc
  intro k
  refine ⟨pow_nonneg hq _, ?_⟩
  rw [pow_succ]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hq hq1) hq).trans_eq (one_mul q)

/-- Geometric moment measures with ratio between zero and one have finite total mass. -/
theorem geometricMomentMeasure_isFinite (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    IsFiniteMeasure (geometricMomentMeasure q) :=
  discreteMomentMeasure_isFinite _ _
    ((summable_geometric_of_lt_one hq hq1).comp_injective
      (fun _ _ h => Nat.add_right_cancel h))

/-- Every geometric moment integral is exactly its reciprocal power-difference expression. -/
theorem geometricMomentMeasure_moment (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) (j : ℕ) :
    (∫ t : ℝ, t ^ j ∂geometricMomentMeasure u) = u ^ (j + 1) / (1 - u ^ (j + 1)) := by
  rw [show geometricMomentMeasure u =
    discreteMomentMeasure (fun k => u ^ (k + 1)) (fun k => u ^ (k + 1)) from rfl,
    integral_discreteMomentMeasure _ _ (fun k => pow_nonneg hu (k + 1))]
  have he (k : ℕ) : u ^ (k + 1) * (u ^ (k + 1)) ^ j =
      (u ^ (j + 1)) ^ k * u ^ (j + 1) := by
    rw [mul_comm (u ^ (k + 1)), ← pow_succ, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  simp_rw [he]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (pow_nonneg hu _)
    (pow_lt_one₀ hu hu1 (by omega))]
  rw [div_eq_mul_inv, mul_comm]

end Lambert
