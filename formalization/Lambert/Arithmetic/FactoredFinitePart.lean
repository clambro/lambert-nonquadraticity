import Lambert.Arithmetic.NodalFinitePart
import Lambert.Arithmetic.LaurentSeriesLocalOrder

/-!
# Logarithmic derivatives of factored nodal denominators

The evaluation identity makes the finite-part weight bound a finite sum of
geometric ratios, with nonvanishing hypotheses retained explicitly.
-/

namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
variable {K : Type*} [Field K]

/-- The logarithmic derivative of a product of distinct linear factors is
the sum of their reciprocal differences at every regular evaluation point. -/
theorem linearFactorProduct_derivative_eval {ι : Type*} (s : Finset ι) (x : ι → K)
    (a : K) (ha : ∀ j ∈ s, a ≠ x j) :
    (∏ j ∈ s, (X - C (x j))).derivative.eval a =
      (∑ j ∈ s, 1 / (a - x j)) * (∏ j ∈ s, (X - C (x j))).eval a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj, derivative_mul, eval_add, eval_mul,
      eval_mul, derivative_sub, derivative_X, derivative_C]
    simp only [sub_zero, eval_one, eval_sub, eval_X, eval_C, one_mul]
    rw [ih (fun k hk => ha k (mem_insert_of_mem hk))]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    field_simp [sub_ne_zero.mpr (ha j (mem_insert_self _ _))]

/-- A logarithmic derivative multiplied by its node has nonnegative order
when every individual node-to-difference ratio does. -/
theorem linearFactorProduct_logDerivative_valuation_le {ι : Type*} (s : Finset ι)
    (x : ι → LaurentSeries K) (a : LaurentSeries K)
    (ha : ∀ j ∈ s, a ≠ x j)
    (hv : ∀ j ∈ s, Valued.v (a / (a - x j)) ≤ 1) :
    Valued.v (a * (∏ j ∈ s, (X - C (x j))).derivative.eval a /
      (∏ j ∈ s, (X - C (x j))).eval a) ≤ 1 := by
  have hD : (∏ j ∈ s, (X - C (x j))).eval a ≠ 0 := by
    rw [eval_prod]
    apply prod_ne_zero_iff.mpr
    intro j hj
    simpa using sub_ne_zero.mpr (ha j hj)
  rw [linearFactorProduct_derivative_eval s x a ha]
  have he : a * ((∑ j ∈ s, 1 / (a - x j)) * (∏ j ∈ s, (X - C (x j))).eval a) /
      (∏ j ∈ s, (X - C (x j))).eval a = ∑ j ∈ s, a / (a - x j) := by
    rw [← mul_assoc, mul_div_cancel_right₀ _ hD, mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [he]
  exact Valuation.map_sum_le Valued.v hv

end
end Lambert
