import Mathlib.FieldTheory.RatFunc.Valuation
import Lambert.Arithmetic.PolynomialEvaluationSubmodule

/-!
# Coefficientwise bounds at rational-function infinity

Scalar interpolation transfers boundedness at infinity from all constant
specializations to individual coefficients.
-/
namespace Lambert
noncomputable section
open Polynomial WithZero Finset
open scoped Classical
variable {K : Type*} [Field K]

/-- Rational functions bounded by a fixed infinity degree form a vector subspace
 over the constant field. -/
def ratFuncInfinitySubmodule (K : Type*) [Field K] (d : ℤ) : Submodule K (RatFunc K) where
  carrier := {f | RatFunc.inftyValuation K f ≤ exp d}
  zero_mem' := by simp
  add_mem' hf hg := by
    exact Valuation.map_add_le (RatFunc.inftyValuation K) hf hg
  smul_mem' a f hf := by
    by_cases ha : a = 0
    · simp [ha]
    · change RatFunc.inftyValuation K (a • f) ≤ _
      rw [Algebra.smul_def, map_mul]
      change RatFunc.inftyValuation K (RatFunc.C a) * RatFunc.inftyValuation K f ≤ _
      rwa [RatFunc.inftyValuation.C _ ha, one_mul]

/-- Uniform infinity bounds at all constant specializations bound every
coefficient of a polynomial over rational functions. -/
theorem ratFunc_coeff_inftyValuation_le_of_eval [Infinite K]
    (p : (RatFunc K)[X]) (d : ℤ)
    (hp : ∀ a : K, RatFunc.inftyValuation K (p.eval (RatFunc.C a)) ≤ exp d) (k : ℕ) :
    RatFunc.inftyValuation K (p.coeff k) ≤ exp d := by
  exact polynomial_coeff_mem_of_forall_eval_mem (ratFuncInfinitySubmodule K d) p (fun a => by
    change RatFunc.inftyValuation K (p.eval ((algebraMap K (RatFunc K)) a)) ≤ _
    simpa using hp a) k

/-- Clearing a rational function bounded at infinity gives a numerator whose
degree does not exceed that of the clearing polynomial. -/
theorem ratFunc_cleared_natDegree_le {f : RatFunc K} (hf : RatFunc.inftyValuation K f ≤ 1)
    {N T : K[X]} (hT : T ≠ 0)
    (he : algebraMap K[X] (RatFunc K) N = algebraMap K[X] (RatFunc K) T * f) :
    N.natDegree ≤ T.natDegree := by
  by_cases hN : N = 0
  · simp [hN]
  have hb : RatFunc.inftyValuation K (algebraMap K[X] (RatFunc K) N) ≤
      RatFunc.inftyValuation K (algebraMap K[X] (RatFunc K) T) := by
    rw [he, map_mul]
    simpa using mul_le_mul' le_rfl hf
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial _ hN,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial _ hT] at hb
  exact_mod_cast WithZero.exp_le_exp.mp hb

/-- A finite product of rational functions has infinity valuation bounded by the sum of individual exponent bounds. -/
theorem ratFunc_product_inftyValuation_le {ι : Type*} (s : Finset ι) (a : ι → RatFunc K)
    (d : ι → ℤ) (ha : ∀ i ∈ s, RatFunc.inftyValuation K (a i) ≤ exp (d i)) :
    RatFunc.inftyValuation K (∏ i ∈ s, a i) ≤ exp (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, map_mul, exp_add]
    exact mul_le_mul' (ha i (mem_insert_self _ _))
      (ih (fun j hj => ha j (mem_insert_of_mem hj)))


end
end Lambert
