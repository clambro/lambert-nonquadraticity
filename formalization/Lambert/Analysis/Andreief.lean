import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Positivity

/-!
# Integration of products of alternants

Andréief's identity expresses the integral of two evaluation determinants as
a factorial times the determinant of their pairwise integrals. Pairwise-product
integrability is explicit; individual integrability alone would not suffice.

See Forrester, "Meet Andréief, Bordeaux 1886, and Andreev, Kharkov 1882–83",
equation (1.7) and Section 2.2, https://arxiv.org/abs/1806.10411.
-/

namespace Lambert

open MeasureTheory

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
  (μ : Measure X) [SigmaFinite μ]

omit [MeasurableSpace X] in
private theorem det_mul_prod_expansion (f g : ι → X → ℝ) (x : ι → X) :
    (Matrix.of fun i j => f i (x j)).det * (∏ j, g j (x j)) =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ j, (f (σ j) (x j) * g j (x j)) := by
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.sum_mul, Finset.prod_mul_distrib, mul_assoc]

/-- An evaluation determinant times a coordinatewise product is integrable when every required pairwise product is integrable. -/
theorem integrable_det_mul_prod (f g : ι → X → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t) μ) :
    Integrable (fun x : ι → X => (Matrix.of fun i j => f i (x j)).det * ∏ j, g j (x j))
      (Measure.pi (fun _ : ι => μ)) := by
  simp_rw [det_mul_prod_expansion]
  exact integrable_finsetSum _ fun σ _ =>
    (Integrable.fintype_prod (fun j => hfg (σ j) j)).const_mul _

/-- For families with integrable pairwise products over a sigma-finite measure, integrating an evaluation determinant against coordinatewise factors gives the determinant of the pairwise integrals. -/
theorem integral_det_mul_prod (f g : ι → X → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t) μ) :
    (∫ x : ι → X, (Matrix.of fun i j => f i (x j)).det * (∏ j, g j (x j))
      ∂Measure.pi (fun _ : ι => μ)) =
      (Matrix.of fun i j => ∫ t, f i t * g j t ∂μ).det := by
  simp_rw [det_mul_prod_expansion]
  rw [integral_finsetSum _ (fun σ _ =>
    (Integrable.fintype_prod (fun j => hfg (σ j) j)).const_mul _)]
  simp only [integral_const_mul, Matrix.det_apply', Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact integral_fintype_prod_eq_prod (fun j t => f (σ j) t * g j t)

omit [MeasurableSpace X] in
private theorem det_mul_det_expansion (f g : ι → X → ℝ) (x : ι → X) :
    (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ((Matrix.of fun i j => f i (x j)).det * ∏ j, g (σ j) (x j)) := by
  simp only [Matrix.det_apply' (Matrix.of fun i j => g i (x j)), Matrix.of_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- A product of two evaluation determinants is integrable when all pairwise function products are integrable. -/
theorem integrable_det_mul_det (f g : ι → X → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t) μ) :
    Integrable (fun x : ι → X =>
      (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det)
      (Measure.pi (fun _ : ι => μ)) := by
  simp_rw [det_mul_det_expansion]
  exact integrable_finsetSum _ fun σ _ =>
    (integrable_det_mul_prod μ f (fun j => g (σ j)) (fun i j => hfg i (σ j))).const_mul _

/-- For families with integrable pairwise products over a sigma-finite measure, the integral of two evaluation determinants is the dimension factorial times the determinant of their pairwise integrals. -/
theorem andreief (f g : ι → X → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t) μ) :
    (∫ x : ι → X,
      (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det
      ∂Measure.pi (fun _ : ι => μ)) =
      ((Fintype.card ι).factorial : ℝ) * (Matrix.of fun i j => ∫ t, f i t * g j t ∂μ).det := by
  simp_rw [det_mul_det_expansion]
  rw [integral_finsetSum _ (fun σ _ =>
    (integrable_det_mul_prod μ f (fun j => g (σ j)) (fun i j => hfg i (σ j))).const_mul _)]
  simp only [integral_const_mul]
  have he (σ : Equiv.Perm ι) :
      ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        (∫ x : ι → X, (Matrix.of fun i j => f i (x j)).det * (∏ j, g (σ j) (x j))
          ∂Measure.pi (fun _ : ι => μ)) =
        (Matrix.of fun i j => ∫ t, f i t * g j t ∂μ).det := by
    rw [integral_det_mul_prod μ f (fun j => g (σ j)) (fun i j => hfg i (σ j))]
    have hd := Matrix.det_permute' σ (Matrix.of fun i j => ∫ t, f i t * g j t ∂μ)
    change ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ((Matrix.of fun i j => ∫ t, f i t * g j t ∂μ).submatrix id σ).det = _
    rw [hd, ← mul_assoc]
    have hs : (((Equiv.Perm.sign σ : ℤ) : ℝ)) ^ 2 = 1 := by
      rw [← sq_abs, abs_unit_intCast, one_pow]
    rw [← pow_two, hs, one_mul]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

/-- If two nonnegative weights are ordered almost everywhere and the common alternant product is
nonnegative almost everywhere, then their weighted moment determinants have the same order. -/
theorem weighted_andreief_det_mono (w v : X → ℝ) (f g : ι → X → ℝ)
    (hwfg : ∀ i j, Integrable (fun t => w t * f i t * g j t) μ)
    (hvfg : ∀ i j, Integrable (fun t => v t * f i t * g j t) μ)
    (hwv : ∀ᵐ t ∂μ, 0 ≤ w t ∧ w t ≤ v t)
    (hfg : ∀ᵐ x : ι → X ∂Measure.pi (fun _ : ι => μ),
      0 ≤ (Matrix.of fun i j => f i (x j)).det *
        (Matrix.of fun i j => g i (x j)).det) :
    (Matrix.of fun i j => ∫ t, w t * f i t * g j t ∂μ).det ≤
      (Matrix.of fun i j => ∫ t, v t * f i t * g j t ∂μ).det := by
  let F := fun x : ι → X =>
    (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det
  have hw' (i j) : Integrable (fun t => (w t * f i t) * g j t) μ := by
    simpa only [mul_assoc] using hwfg i j
  have hv' (i j) : Integrable (fun t => (v t * f i t) * g j t) μ := by
    simpa only [mul_assoc] using hvfg i j
  have hpi : ∀ᵐ x : ι → X ∂Measure.pi (fun _ : ι => μ),
      ∀ i, 0 ≤ w (x i) ∧ w (x i) ≤ v (x i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => μ) (i := i)).eventually hwv
  have hprod : ∀ᵐ x : ι → X ∂Measure.pi (fun _ : ι => μ),
      (∏ i, w (x i)) * F x ≤ (∏ i, v (x i)) * F x := by
    filter_upwards [hpi, hfg] with x hx hF
    apply mul_le_mul_of_nonneg_right _ hF
    exact Finset.prod_le_prod (fun i _ => (hx i).1) (fun i _ => (hx i).2)
  have hscale (q : X → ℝ) (x : ι → X) :
      (Matrix.of fun i j => q (x j) * f i (x j)).det =
        (∏ j, q (x j)) * (Matrix.of fun i j => f i (x j)).det := by
    exact Matrix.det_mul_row (fun j => q (x j)) _
  have hwi : Integrable (fun x : ι → X => (∏ i, w (x i)) * F x)
      (Measure.pi (fun _ : ι => μ)) := by
    have hi := integrable_det_mul_det μ (fun i t => w t * f i t) g hw'
    convert hi using 1
    funext x
    rw [hscale]
    simp only [F, mul_assoc]
  have hvi : Integrable (fun x : ι → X => (∏ i, v (x i)) * F x)
      (Measure.pi (fun _ : ι => μ)) := by
    have hi := integrable_det_mul_det μ (fun i t => v t * f i t) g hv'
    convert hi using 1
    funext x
    rw [hscale]
    simp only [F, mul_assoc]
  have hint := integral_mono_ae hwi hvi hprod
  have haw := andreief μ (fun i t => w t * f i t) g hw'
  have hav := andreief μ (fun i t => v t * f i t) g hv'
  rw [show (fun x : ι → X => (∏ i, w (x i)) * F x) = fun x =>
      (Matrix.of fun i j => w (x j) * f i (x j)).det *
        (Matrix.of fun i j => g i (x j)).det by
      funext x
      dsimp [F]
      rw [hscale]
      simp only [mul_assoc],
    show (fun x : ι → X => (∏ i, v (x i)) * F x) = fun x =>
      (Matrix.of fun i j => v (x j) * f i (x j)).det *
        (Matrix.of fun i j => g i (x j)).det by
      funext x
      dsimp [F]
      rw [hscale]
      simp only [mul_assoc],
    haw, hav] at hint
  exact le_of_mul_le_mul_left hint (by positivity)

end Lambert
