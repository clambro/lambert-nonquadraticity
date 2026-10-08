import Lambert.Determinants.ZeroLocal
import Lambert.Determinants.FinitePartIdentity
import Lambert.Arithmetic.LaurentConvergence

/-!
# The formal limit of finite Lambert finite-part sums

The limit takes place in the Laurent valuation topology at zero. Polynomial
coefficients and nodal residues are fixed Laurent series, so multiplication
preserves convergence even when those coefficients themselves have poles.
-/

namespace Lambert
noncomputable section
open Filter Finset Polynomial
open scoped Topology Classical WithZero
variable {K : Type*} [Field K]

/-- Positive rational Lambert prefixes tend to the constructed formal Lambert series. -/
theorem lambertPositivePrefix_tendsto :
    Tendsto (lambertPositivePrefix (lambertZeroBase K)) atTop
      (𝓝 (lambertFormalSeries K : LaurentSeries K)) := by
  have ht : Tendsto (fun N =>
      ((lambertFormalSeries K - lambertFormalPrefix K N : PowerSeries K) : LaurentSeries K))
        atTop (𝓝 0) := by
    apply laurent_tendsto_zero_of_orders
    intro d
    filter_upwards [eventually_ge_atTop d] with N hN
    exact (laurentSeries_valuation_le_of_order _ _ (lambertFormalSeries_sub_prefix_order N)).trans
      (WithZero.exp_le_exp.mpr (by omega))
  have he := (tendsto_const_nhds (x := (lambertFormalSeries K : LaurentSeries K))).sub ht
  simpa only [map_sub, sub_sub_cancel, lambertFormalPrefix_laurent, sub_zero, lambertZeroBase] using he

/-- Polynomial monomial truncations tend to their reciprocal-geometric moments. -/
theorem lambertTruncatedPolynomial_X_pow_tendsto (r : ℕ) :
    Tendsto (fun N => lambertTruncatedPolynomial (lambertZeroBase K) N (X ^ r)) atTop
      (𝓝 (1 / (lambertZeroBase K ^ (r + 1) - 1))) := by
  let q := lambertZeroBase K
  have hr : q ^ (r + 1) ≠ 1 := by
    simpa only [pow_zero] using (lambertZeroBase_pow_injective (K := K)).ne
      (show r + 1 ≠ 0 by omega)
  have hp : Tendsto (fun N : ℕ => q ^ (N * (r + 1))) atTop (𝓝 0) := by
    have hv : Valued.v (q ^ (r + 1)) ≤ WithZero.exp (-1) := by
      rw [lambertZeroBase_pow_valuation, WithZero.exp_le_exp]
      omega
    simpa only [← pow_mul, Nat.mul_comm (r + 1)] using
      Valued.tendsto_zero_pow_of_le_exp_neg_one hv
  have he (N : ℕ) : lambertTruncatedPolynomial q N (X ^ r) =
      1 / (q ^ (r + 1) - 1) - q ^ (N * (r + 1)) / (q ^ (r + 1) - 1) := by
    have hh := lambertFiniteMonomial_remainder q r N hr
    rw [lambertTruncatedPolynomial_apply]
    have hs : (∑ m ∈ range N, q ^ m * (X ^ r : (LaurentSeries K)[X]).eval (q ^ m)) =
        ∑ m ∈ range N, q ^ (m * (r + 1)) := by
      apply sum_congr rfl
      intro m _
      rw [eval_pow, eval_X, ← pow_mul, ← pow_add]
      congr 1
      ring
    rw [hs]
    linear_combination -hh
  change Tendsto (fun N => lambertTruncatedPolynomial q N (X ^ r)) atTop
    (𝓝 (1 / (q ^ (r + 1) - 1)))
  simp_rw [he]
  simpa only [zero_div, sub_zero] using
    tendsto_const_nhds.sub (hp.div_const (q ^ (r + 1) - 1))

/-- Truncated polynomial functionals converge for every fixed Laurent-coefficient
polynomial, including polynomials whose coefficients have poles at zero. -/
theorem lambertTruncatedPolynomial_tendsto (z : LaurentSeries K) (p : (LaurentSeries K)[X]) :
    Tendsto (fun N => lambertTruncatedPolynomial (lambertZeroBase K) N p) atTop
      (𝓝 ((lambertPolynomialFunctional (lambertZeroBase K) p).eval z)) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [map_add, eval_add]
    exact hp.add hr
  | monomial r a =>
    simp only [← smul_X_eq_monomial, map_smul, eval_smul, smul_eq_mul,
      lambertPolynomialFunctional_X_pow, eval_C]
    exact tendsto_const_nhds.mul (lambertTruncatedPolynomial_X_pow_tendsto r)

/-- The corrected finite simple-pole values tend to their prescribed Lambert
values, with the pole-dependent cutoff retained. -/
theorem lambertTruncatedPole_tendsto (z : LaurentSeries K) (j : ℕ) :
    Tendsto (fun N => -lambertFinitePoleSum (lambertZeroBase K) N j -
      (z + lambertPositivePrefix (lambertZeroBase K) N)) atTop
      (𝓝 (-(z - geometricMomentPrefix (lambertZeroBase K) j))) := by
  have hshift := lambertPositivePrefix_tendsto (K := K) |>.comp (tendsto_sub_atTop_nat (j + 1))
  have hdiff := hshift.sub (lambertPositivePrefix_tendsto (K := K))
  have ht := (tendsto_const_nhds (x := -(z - geometricMomentPrefix (lambertZeroBase K) j))).add hdiff
  simp only [sub_self, add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (j + 1)] with N hN
  have he : j + 1 + (N - (j + 1)) = N := by omega
  have hh := lambertFinitePoleSum_eq (lambertZeroBase K) lambertZeroBase_ne_zero j (N - (j + 1))
  rw [he] at hh
  rw [hh]
  dsimp only [Function.comp_def]
  ring

end
end Lambert
