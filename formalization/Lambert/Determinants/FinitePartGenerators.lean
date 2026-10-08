import Lambert.Arithmetic.GeometricMoments
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Finite geometric sums in the Lambert finite-part identity

Truncation identities retain their exact rational boundary terms. No infinite
sum or convergence statement is used in this algebraic layer.
-/

namespace Lambert

noncomputable section

open Finset

variable {K : Type*} [Field K]

/-- A finite positive Lambert prefix uses the local-at-zero denominators `1-q^m`. -/
def lambertPositivePrefix (q : K) (N : ℕ) : K :=
  ∑ k ∈ range N, q ^ (k + 1) / (1 - q ^ (k + 1))

/-- A truncated finite-part sum omits the singular summand at its simple pole. -/
def lambertFinitePoleSum (q : K) (N j : ℕ) : K :=
  -(∑ m ∈ range N, if m = j then 0 else q ^ m / (q ^ j - q ^ m))

private theorem geometricPoleRatio_before (q : K) (hq : q ≠ 0) (i d : ℕ) :
    q ^ i / (q ^ (i + d) - q ^ i) = 1 / (q ^ d - 1) := by
  rw [pow_add, ← mul_sub_one]
  simpa only [mul_one] using (mul_div_mul_left (1 : K) (q ^ d - 1) (pow_ne_zero i hq))

private theorem geometricPoleRatio_after (q : K) (hq : q ≠ 0) (i d : ℕ) :
    q ^ (i + d) / (q ^ i - q ^ (i + d)) = q ^ d / (1 - q ^ d) := by
  rw [pow_add, ← mul_one_sub]
  exact mul_div_mul_left _ _ (pow_ne_zero i hq)

/-- A finite simple-pole sum splits exactly into its backward geometric prefix
and a forward positive Lambert prefix. -/
theorem lambertFinitePoleSum_eq (q : K) (hq : q ≠ 0) (j T : ℕ) :
    lambertFinitePoleSum q (j + 1 + T) j =
      -geometricMomentPrefix q j - lambertPositivePrefix q T := by
  have hlo : (∑ m ∈ range j, q ^ m / (q ^ j - q ^ m)) = geometricMomentPrefix q j := by
    rw [← sum_range_reflect (fun m => q ^ m / (q ^ j - q ^ m)) j]
    unfold geometricMomentPrefix
    apply sum_congr rfl
    intro k hk
    have hk' := mem_range.mp hk
    have he : j - 1 - k + (k + 1) = j := by omega
    have hr := geometricPoleRatio_before q hq (j - 1 - k) (k + 1)
    rw [he] at hr
    exact hr
  unfold lambertFinitePoleSum
  rw [sum_range_add, sum_range_succ]
  have hl : (∑ m ∈ range j, if m = j then 0 else q ^ m / (q ^ j - q ^ m)) =
      geometricMomentPrefix q j := by
    rw [← hlo]
    apply sum_congr rfl
    intro m hm
    rw [if_neg (Nat.ne_of_lt (mem_range.mp hm))]
  have hr : (∑ k ∈ range T, if j + 1 + k = j then 0 else
      q ^ (j + 1 + k) / (q ^ j - q ^ (j + 1 + k))) = lambertPositivePrefix q T := by
    unfold lambertPositivePrefix
    apply sum_congr rfl
    intro k _
    rw [if_neg (by omega), show j + 1 + k = j + (k + 1) by omega,
      geometricPoleRatio_after q hq]
  rw [hl, if_pos rfl, add_zero, hr]
  ring

/-- A truncated polynomial monomial sum has an exact geometric remainder. -/
theorem lambertFiniteMonomial_remainder (q : K) (r N : ℕ)
    (hq : q ^ (r + 1) ≠ 1) :
    1 / (q ^ (r + 1) - 1) - (-(∑ m ∈ range N, q ^ (m * (r + 1)))) =
      q ^ (N * (r + 1)) / (q ^ (r + 1) - 1) := by
  have he := geom_sum_mul (q ^ (r + 1)) N
  simp only [← pow_mul, Nat.mul_comm (r + 1)] at he
  apply (eq_div_iff (sub_ne_zero.mpr hq)).mpr
  field_simp [sub_ne_zero.mpr hq]
  linear_combination he

end

end Lambert
