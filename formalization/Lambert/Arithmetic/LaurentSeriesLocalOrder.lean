import Lambert.Arithmetic.PolynomialEvaluationSubmodule
import Mathlib.RingTheory.LaurentSeries

/-!
# Local order and coefficientwise bounds

The coefficient filtration on Laurent series is a scalar submodule. Constant
interpolation therefore turns uniform evaluation bounds into coefficient bounds.
-/

namespace Lambert

noncomputable section

open PowerSeries WithZero
open scoped WithZero

variable {K : Type*} [Field K]

local instance : Module K (LaurentSeries K) := Algebra.toModule

/-- Laurent series vanishing below a specified signed order form a scalar submodule. -/
def laurentOrderSubmodule (K : Type*) [Field K] (d : ℤ) : Submodule K (LaurentSeries K) where
  carrier := {f | ∀ k < d, f.coeff k = 0}
  zero_mem' := by simp
  add_mem' hf hg := by intro k hk; simp [hf k hk, hg k hk]
  smul_mem' a f hf := by
    intro k hk
    rw [Algebra.smul_def, LaurentSeries.algebraMap_apply, HahnSeries.C_mul_eq_smul]
    simp [hf k hk]

/-- Membership in the Laurent coefficient filtration is equivalent to the
corresponding nonarchimedean valuation bound. -/
theorem mem_laurentOrderSubmodule (f : LaurentSeries K) (d : ℤ) :
    f ∈ laurentOrderSubmodule K d ↔ Valued.v f ≤ exp (-d) :=
  (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K).symm

/-- A lower power-series order bound gives the same lower Laurent-series order bound. -/
theorem laurentSeries_valuation_le_of_order (f : PowerSeries K) (d : ℕ)
    (hf : (d : ℕ∞) ≤ f.order) :
    Valued.v (f : LaurentSeries K) ≤ exp (-(d : ℤ)) := by
  apply (LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero K f).mpr
  intro k hk
  exact coeff_of_lt_order k (lt_of_lt_of_le (by exact_mod_cast hk) hf)

/-- A finite power-series order determines its Laurent valuation exactly. -/
theorem laurentSeries_valuation_eq_of_order (f : PowerSeries K) (d : ℕ)
    (hf : f.order = d) :
    Valued.v (f : LaurentSeries K) = exp (-(d : ℤ)) := by
  have h0 : f ≠ 0 := by intro he; simp [he] at hf
  have hv : Valued.v (f : LaurentSeries K) ≠ 0 := by
    apply (map_ne_zero _).mpr
    exact fun he => h0 (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (he.trans (map_zero _).symm))
  have hlo := laurentSeries_valuation_le_of_order f d hf.ge
  have hnext : ¬ Valued.v (f : LaurentSeries K) ≤ exp (-((d + 1 : ℕ) : ℤ)) := by
    intro he
    have hc := (LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero K f).mp he d (Nat.lt_succ_self _)
    exact (order_eq_nat.mp hf).1 hc
  rw [← log_le_iff_le_exp hv] at hlo hnext
  rw [← exp_log hv]
  congr 1
  push_cast at hnext
  omega

/-- Uniform Laurent order bounds at all scalar values imply the same bound
for every polynomial coefficient, including zero coefficients. -/
theorem laurentSeries_coeff_valuation_le_of_eval [Infinite K]
    (p : Polynomial (LaurentSeries K)) (d : ℤ)
    (hp : ∀ x : K, Valued.v (p.eval (algebraMap K (LaurentSeries K) x)) ≤ exp (-d))
    (k : ℕ) : Valued.v (p.coeff k) ≤ exp (-d) := by
  apply (mem_laurentOrderSubmodule _ d).mp
  refine polynomial_coeff_mem_of_forall_eval_mem (K := K) (L := LaurentSeries K) (laurentOrderSubmodule K d) p ?_ k
  intro x
  exact (mem_laurentOrderSubmodule _ d).mpr (hp x)

/-- Constant Laurent series have nonnegative order. -/
theorem laurentConstant_valuation_le (c : K) :
    Valued.v (algebraMap K (LaurentSeries K) c) ≤ 1 := by
  have he := laurentSeries_valuation_le_of_order (PowerSeries.C c) 0 (by simp)
  simpa only [Nat.cast_zero, neg_zero, WithZero.exp_zero,
    HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply] using he

/-- Natural scalar coefficients cannot decrease the order of a Laurent series. -/
theorem laurentNatCast_valuation_le (n : ℕ) : Valued.v (n : LaurentSeries K) ≤ 1 := by
  simpa only [map_natCast] using laurentConstant_valuation_le (K := K) (n : K)

end

end Lambert
