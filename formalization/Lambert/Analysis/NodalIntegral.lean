import Lambert.Analysis.MarkovMeasure
import Mathlib.Topology.Algebra.Polynomial
import Lambert.Arithmetic.NodalFinitePart

/-!
# Polynomial integration with a positive nodal denominator

The nodal functional agrees with integration for arbitrary polynomial numerators,
including the quotient term beyond the proper partial-fraction range.
-/
namespace Lambert
noncomputable section
open Polynomial MeasureTheory Finset
open scoped Classical

/-- Integrating polynomial values against a continuous weight on compact support
is a linear functional on real polynomials. -/
def compactPolynomialIntegral (μ : Measure ℝ) [IsFiniteMeasure μ]
    {S : Set ℝ} (hS : IsCompact S) (hμ : ∀ᵐ t ∂μ, t ∈ S)
    (w : ℝ → ℝ) (hw : ContinuousOn w S) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ t, w t * p.eval t ∂μ
  map_add' p r := by
    simp only [eval_add, mul_add]
    exact integral_add
      (integrable_of_continuousOn_compact μ hS hμ _ (hw.mul p.continuous.continuousOn))
      (integrable_of_continuousOn_compact μ hS hμ _ (hw.mul r.continuous.continuousOn))
  map_smul' a p := by
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm (w _) a]
    exact integral_const_mul a _

/-- Integrating over a positive nodal measure is the signed nodal functional
whose polynomial part is ordinary integration and whose pole values are negative Markov samples. -/
theorem integral_polynomial_nodalFunctional (μ : Measure ℝ) [IsFiniteMeasure μ]
    {S : Set ℝ} (hS : IsCompact S) (hμ : ∀ᵐ t ∂μ, t ∈ S)
    {L : ℕ} (x : Fin L → ℝ) (hx : Function.Injective x)
    (hb : ∀ t ∈ S, ∀ j, t < x j) (p : ℝ[X]) :
    (∫ t, p.eval t ∂nodalMomentMeasure μ univ x) =
      (-1 : ℝ) ^ L * nodalFunctional x
        (compactPolynomialIntegral μ hS hμ (fun _ => 1) continuousOn_const)
        (fun j => -markovTransform μ (x j)) p := by
  let w := positiveNodalDensity univ x
  have hw : ContinuousOn w S := positiveNodalDensity_continuousOn _ _ _ (fun t ht j _ => hb t ht j)
  have hwi := integrable_of_continuousOn_compact μ hS hμ w hw
  have hwn : ∀ᵐ t ∂μ, 0 ≤ w t := by
    filter_upwards [hμ] with t ht
    exact (positiveNodalDensity_pos _ _ _ (fun j _ => hb t ht j)).le
  rw [nodalMomentMeasure, integral_withDensity_ofReal_mul μ _ hwi hwn]
  have hpoint (t : ℝ) (ht : t ∈ S) : w t * p.eval t =
      (-1 : ℝ) ^ L * ((p /ₘ Lagrange.nodal univ x).eval t +
        ∑ j, (Lagrange.nodalWeight univ x j * p.eval (x j)) * (-(x j - t)⁻¹)) := by
    have hn : (Lagrange.nodal univ x).eval t = (-1 : ℝ) ^ L * ∏ j, (x j - t) := by
      rw [Lagrange.eval_nodal]
      conv_lhs => arg 2; ext j; rw [show t - x j = -(x j - t) by ring]
      rw [prod_neg, card_univ, Fintype.card_fin]
    have hp' := nodalFiniteValue_regular x hx t (fun j => ne_of_lt (hb t ht j)) p
    rw [nodalFiniteValue_apply] at hp'
    simp only [if_neg (ne_of_lt (hb t ht _)), one_div] at hp'
    have hs : (∑ j, (Lagrange.nodalWeight univ x j * p.eval (x j)) * (t - x j)⁻¹) =
        ∑ j, (Lagrange.nodalWeight univ x j * p.eval (x j)) * (-(x j - t)⁻¹) := by
      apply sum_congr rfl
      intro j _
      rw [show t - x j = -(x j - t) by ring, inv_neg]
    rw [hs, hn] at hp'
    rw [hp']
    have hs0 : (-1 : ℝ) ^ L ≠ 0 := pow_ne_zero _ (by norm_num)
    dsimp only [w, positiveNodalDensity]
    field_simp
  have hk (j : Fin L) : Integrable (fun t => (x j - t)⁻¹) μ :=
    integrable_of_continuousOn_compact μ hS hμ _
      ((continuous_const.sub continuous_id).continuousOn.inv₀
        (fun t ht => (sub_pos.mpr (hb t ht j)).ne'))
  have hquot : Integrable (fun t => (p /ₘ Lagrange.nodal univ x).eval t) μ :=
    integrable_of_continuousOn_compact μ hS hμ _ (by fun_prop)
  have hsum : Integrable (fun t => ∑ j, (Lagrange.nodalWeight univ x j * p.eval (x j)) *
      (-(x j - t)⁻¹)) μ := integrable_finsetSum _ (fun j _ => (hk j).neg.const_mul _)
  rw [integral_congr_ae (hμ.mono hpoint), integral_const_mul,
    integral_add hquot hsum, integral_finsetSum (f := fun j t => (Lagrange.nodalWeight univ x j * p.eval (x j)) *
      (-(x j - t)⁻¹)) univ (fun j _ => (hk j).neg.const_mul _)]
  simp only [integral_const_mul, integral_neg, nodalFunctional_apply, compactPolynomialIntegral,
    LinearMap.coe_mk, AddHom.coe_mk, one_mul, smul_eq_mul, markovTransform]

end
end Lambert
