import Lambert.Determinants.RealMoments
import Lambert.Analysis.WeightedGramBound
import Lambert.Analysis.GeometricDeterminantBounds

/-!
# Uniform decay for shifted Lambert windows

Positive density comparison transfers the shifted Cauchy estimate to every
pole window, with a logarithmic error linear in the determinant rank.
-/
namespace Lambert
noncomputable section
open Polynomial MeasureTheory Matrix Finset Filter Topology
open scoped Classical

/-- The reciprocal product of the geometric pole nodes normalizes the window density. -/
def lambertCertificateScale (q : ℝ) (k L : ℕ) : ℝ := (∏ j : Fin L, q ^ (k + j.val))⁻¹

private theorem windowScale_pos (q : ℝ) (hq : 1 < q) (k L : ℕ) :
    0 < lambertCertificateScale q k L := inv_pos.mpr (prod_pos (fun _ _ => pow_pos (zero_lt_one.trans hq) _))

private theorem density_bounds (q : ℝ) (hq : 1 < q) (k L : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc 0 q⁻¹) :
    lambertCertificateScale q k L ≤ positiveNodalDensity univ (fun j : Fin L => q ^ (k + j.val)) t ∧
    positiveNodalDensity univ (fun j : Fin L => q ^ (k + j.val)) t ≤
      (geometricProductFloor q⁻¹)⁻¹ * lambertCertificateScale q k L := by
  have hq0 := zero_lt_one.trans hq
  have hu := inv_pos.mpr hq0
  have hu1 := inv_lt_one_of_one_lt₀ hq
  have hj (j : Fin L) : t < q ^ (k + j.val) := ht.2.trans_lt (hu1.trans_le (one_le_pow₀ hq.le))
  have hp := prod_pos (fun j (_ : j ∈ (univ : Finset (Fin L))) => sub_pos.mpr (hj j))
  have hQ := prod_pos (fun j (_ : j ∈ (univ : Finset (Fin L))) => pow_pos hq0 (k+j.val))
  have hupper : (∏ j : Fin L, (q ^ (k + j.val) - t)) ≤ ∏ j : Fin L, q ^ (k + j.val) :=
    Finset.prod_le_prod (fun j _ => (sub_pos.mpr (hj j)).le) (fun _ _ => sub_le_self _ ht.1)
  have hnorm (j : Fin L) : q ^ (k + j.val) - t = q ^ (k + j.val) * (1 - t * q⁻¹ ^ (k + j.val)) := by
    rw [inv_pow]
    field_simp
  have hg := geometricProductFloor_le_prod_of_injOn q⁻¹ hu hu1 univ
    (fun j : Fin L => k + j.val + 1) (by intros; omega)
    (by intro i _ j _ he; apply Fin.ext; dsimp at he; omega)
  have hnormlower : geometricProductFloor q⁻¹ ≤ ∏ j : Fin L, (1 - t * q⁻¹ ^ (k + j.val)) := by
    apply hg.1.trans
    apply Finset.prod_le_prod
    · intro j _
      exact (sub_pos.mpr (pow_lt_one₀ hu.le hu1 (by omega))).le
    · intro j _
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right ht.2 (pow_nonneg hu.le (k + j.val))]
  have hlower : geometricProductFloor q⁻¹ * (∏ j : Fin L, q ^ (k + j.val)) ≤
      ∏ j : Fin L, (q ^ (k + j.val) - t) := by
    simp_rw [hnorm]
    rw [prod_mul_distrib]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hnormlower hQ.le
  constructor
  · exact inv_anti₀ hp hupper
  · have he := inv_anti₀ (mul_pos (geometricProductFloor_pos _) hQ) hlower
    simpa only [_root_.mul_inv_rev, mul_comm, lambertCertificateScale, positiveNodalDensity] using he

private theorem density_continuous (q : ℝ) (hq : 1 < q) (k L : ℕ) :
    ContinuousOn (positiveNodalDensity univ (fun j : Fin L => q ^ (k + j.val))) (Set.Icc 0 q⁻¹) :=
  positiveNodalDensity_continuousOn _ _ _ (fun _t ht _j _ =>
    ht.2.trans_lt ((inv_lt_one_of_one_lt₀ hq).trans_le (one_le_pow₀ hq.le)))

/-- Every shifted Lambert determinant lies between scalar multiples of its shifted geometric moment determinant. -/
theorem lambertPoleDeterminant_geometric_bounds (q : ℝ) (hq : 1 < q) (h k L s : ℕ) :
    lambertCertificateScale q k L ^ h * shiftedGeometricMomentDeterminant q h s ≤
      (lambertPoleDeterminant q h k L s).eval (lambertValue q) ∧
    (lambertPoleDeterminant q h k L s).eval (lambertValue q) ≤
      ((geometricProductFloor q⁻¹)⁻¹ * lambertCertificateScale q k L) ^ h *
        shiftedGeometricMomentDeterminant q h s := by
  let μ := geometricMomentMeasure q⁻¹
  have hu := inv_pos.mpr (zero_lt_one.trans hq)
  have hu1 := inv_lt_one_of_one_lt₀ hq
  let := geometricMomentMeasure_isFinite q⁻¹ hu.le hu1
  have hs := geometricMomentMeasure_ae_mem q⁻¹ hu.le hu1.le
  let w := positiveNodalDensity univ (fun j : Fin L => q ^ (k + j.val))
  have hw := density_continuous q hq k L
  have hwi := integrable_of_continuousOn_compact μ isCompact_Icc hs w hw
  have hwn : ∀ᵐ t ∂μ, 0 ≤ w t := hs.mono (fun t ht =>
    (windowScale_pos q hq k L).le.trans (density_bounds q hq k L t ht).1)
  have hD : (lambertPoleDeterminant q h k L s).eval (lambertValue q) =
      (Matrix.of fun i j : Fin h => ∫ t, (w t * t ^ s) * t ^ (i.val + j.val) ∂μ).det := by
    rw [lambertPoleDeterminant_eval_gram q hq]
    apply congrArg Matrix.det
    ext i j
    change (∫ t, t ^ (i.val + j.val + s)
      ∂μ.withDensity (fun t => ENNReal.ofReal (w t))) = _
    rw [integral_withDensity_ofReal_mul μ w hwi hwn]
    congr 1
    funext t
    rw [pow_add]
    ring
  have hconst (C : ℝ) :
      (Matrix.of fun i j : Fin h => ∫ t, (C * t ^ s) * t ^ (i.val + j.val) ∂μ).det =
      C ^ h * shiftedGeometricMomentDeterminant q h s := by
    have hm : (Matrix.of fun i j : Fin h => ∫ t, (C * t ^ s) * t ^ (i.val + j.val) ∂μ) =
        C • (Matrix.of fun i j : Fin h => (q ^ (i.val + j.val + s + 1) - 1)⁻¹) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      have he : (fun t : ℝ => (C * t ^ s) * t ^ (i.val + j.val)) =
          fun t => C * t ^ (i.val + j.val + s) := by funext t; rw [pow_add]; ring
      rw [he, integral_const_mul]
      congr 1
      exact congrArg (fun M => M i j) (shiftedGeometricMomentMatrix_integral q hq h s)
    rw [hm, Matrix.det_smul, Fintype.card_fin]
    rfl
  have hlo := moment_gram_det_weight_mono μ isCompact_Icc hs
    (fun t => lambertCertificateScale q k L * t ^ s) (fun t => w t * t ^ s)
    (by fun_prop) (hw.mul (continuous_pow s).continuousOn)
    (fun t ht => ⟨mul_nonneg (windowScale_pos q hq k L).le (pow_nonneg ht.1 _),
      mul_le_mul_of_nonneg_right (density_bounds q hq k L t ht).1 (pow_nonneg ht.1 _)⟩) h
  have hup := moment_gram_det_weight_mono μ isCompact_Icc hs
    (fun t => w t * t ^ s)
    (fun t => ((geometricProductFloor q⁻¹)⁻¹ * lambertCertificateScale q k L) * t ^ s)
    (hw.mul (continuous_pow s).continuousOn) (by fun_prop)
    (fun t ht => ⟨mul_nonneg ((windowScale_pos q hq k L).le.trans
      (density_bounds q hq k L t ht).1) (pow_nonneg ht.1 _),
      mul_le_mul_of_nonneg_right (density_bounds q hq k L t ht).2 (pow_nonneg ht.1 _)⟩) h
  rw [hconst, ← hD] at hlo
  rw [hconst, ← hD] at hup
  exact ⟨hlo, hup⟩

/-- Every shifted Lambert determinant is strictly positive at its Lambert value for bases greater than one. -/
theorem lambertPoleDeterminant_eval_pos (q : ℝ) (hq : 1 < q) (h k L s : ℕ) :
    0 < (lambertPoleDeterminant q h k L s).eval (lambertValue q) :=
  (mul_pos (pow_pos (windowScale_pos q hq k L) _)
    (shiftedGeometricMomentDeterminant_pos q hq h s)).trans_le
      (lambertPoleDeterminant_geometric_bounds q hq h k L s).1

private theorem log_windowScale (q : ℝ) (hq : 1 < q) (k L : ℕ) :
    Real.log (lambertCertificateScale q k L) = -((L : ℝ) * k + L * (L - 1) / 2) * Real.log q := by
  rw [lambertCertificateScale, Real.log_inv, Real.log_prod (fun j _ => (pow_pos (zero_lt_one.trans hq) (k+j.val)).ne')]
  simp_rw [Real.log_pow]
  rw [← sum_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((k+j : ℕ) : ℝ)) L]
  simp only [Nat.cast_add, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have he (n : ℕ) : (∑ j ∈ range n, (j : ℝ)) = (n : ℝ) * (n - 1) / 2 := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
  rw [he]
  ring

/-- Shifted Lambert determinants have their exact cubic logarithmic term with a linear error uniform in the window and shift. -/
theorem lambertPoleDeterminant_log_bounds (q : ℝ) (hq : 1 < q) (h k L s : ℕ) :
    let K := (h : ℝ) * (h + 1) * (2 * h + 1) / 6 + s * h * (h + 1) / 2 +
      h * (L * k + L * (L - 1) / 2);
    -K * Real.log q + 2 * h * Real.log (geometricProductFloor q⁻¹) ≤
      Real.log ((lambertPoleDeterminant q h k L s).eval (lambertValue q)) ∧
    Real.log ((lambertPoleDeterminant q h k L s).eval (lambertValue q)) ≤
      -K * Real.log q - 4 * h * Real.log (geometricProductFloor q⁻¹) := by
  dsimp only
  obtain ⟨hl, hu⟩ := lambertPoleDeterminant_geometric_bounds q hq h k L s
  have hlo := Real.log_le_log (mul_pos (pow_pos (windowScale_pos q hq k L) h)
    (shiftedGeometricMomentDeterminant_pos q hq h s)) hl
  have hup := Real.log_le_log (lambertPoleDeterminant_eval_pos q hq h k L s) hu
  rw [Real.log_mul (pow_pos (windowScale_pos q hq k L) h).ne'
    (shiftedGeometricMomentDeterminant_pos q hq h s).ne', Real.log_pow, log_windowScale q hq] at hlo
  rw [Real.log_mul (pow_pos (mul_pos (inv_pos.mpr (geometricProductFloor_pos _))
      (windowScale_pos q hq k L)) h).ne'
    (shiftedGeometricMomentDeterminant_pos q hq h s).ne', Real.log_pow,
    Real.log_mul (inv_ne_zero (geometricProductFloor_pos _).ne') (windowScale_pos q hq k L).ne',
    Real.log_inv, log_windowScale q hq] at hup
  obtain ⟨hgl, hgu⟩ := shiftedGeometricMomentDeterminant_log_bounds q hq h s
  constructor <;> nlinarith

end
end Lambert
