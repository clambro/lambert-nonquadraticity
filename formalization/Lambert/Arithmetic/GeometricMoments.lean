import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.FieldSimp

/-!
# Reciprocal geometric moments and finite prefixes
-/

namespace Lambert

open Finset

/-- A geometric rational moment equals the reciprocal power difference at the inverse base, including poles where both field expressions vanish. -/
theorem geometricReciprocalMoment_inverse_base {K : Type*} [Field K]
    (u : K) (hu : u ≠ 0) (d : ℕ) :
    u ^ d / (1 - u ^ d) = ((u⁻¹) ^ d - 1)⁻¹ := by
  rw [inv_pow]
  by_cases hd : u ^ d = 1
  · simp [hd]
  · field_simp [pow_ne_zero d hu, sub_ne_zero.mpr (Ne.symm hd)]

/-- The finite reciprocal-geometric prefix is the sum of the first N positive-exponent moments. -/
def geometricMomentPrefix {K : Type*} [Field K] (q : K) (N : ℕ) : K :=
  ∑ k ∈ range N, 1 / (q ^ (k + 1) - 1)

/-- Reciprocal-base geometric prefixes equal the finite positive-ratio reciprocal sums at every nonzero base. -/
theorem geometricMomentPrefix_inv {K : Type*} [Field K] (q : K) (hq : q ≠ 0) (N : ℕ) :
    geometricMomentPrefix q⁻¹ N = ∑ k ∈ range N, q ^ (k + 1) / (1 - q ^ (k + 1)) := by
  unfold geometricMomentPrefix
  apply sum_congr rfl
  intro k hk
  rw [inv_pow, ← one_div, div_sub_one (pow_ne_zero _ hq), one_div_div]

end Lambert
