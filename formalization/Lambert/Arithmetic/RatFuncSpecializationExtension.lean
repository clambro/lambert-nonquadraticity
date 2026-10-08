import Lambert.Arithmetic.RatFuncPoleSupport
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Regular rational-function specialization in extension fields -/
namespace Lambert
noncomputable section
open Polynomial
universe u
variable {F K : Type u} [Field F] [Field K]

/-- Rational functions whose reduced denominators stay nonzero under specialization form a subring. -/
def ratFuncRegularAt₂ (f : F →+* K) (q : K) : Subring (RatFunc F) where
  carrier := {g | g.denom.eval₂ f q ≠ 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    intro hz
    have he := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f q (RatFunc.denom_add_dvd a b) hz
    rw [eval₂_mul] at he
    exact mul_ne_zero ha hb he
  mul_mem' {a b} ha hb := by
    intro hz
    have he := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f q (RatFunc.denom_mul_dvd a b) hz
    rw [eval₂_mul] at he
    exact mul_ne_zero ha hb he
  neg_mem' {a} ha := by
    intro hz
    have hd : (-a).denom ∣ a.denom := by
      apply (RatFunc.denom_dvd a.denom_ne_zero).mpr
      refine ⟨-a.num, ?_⟩
      rw [map_neg, neg_div, RatFunc.num_div_denom]
    exact ha (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f q hd hz)

/-- Evaluation into an extension field is a homomorphism on the regular specialization subring. -/
def ratFuncSpecialization₂ (f : F →+* K) (q : K) : ratFuncRegularAt₂ f q →+* K where
  toFun g := RatFunc.eval f q g.val
  map_zero' := RatFunc.eval_zero _ _
  map_one' := RatFunc.eval_one _ _
  map_add' a b := RatFunc.eval_add f q a.property b.property
  map_mul' a b := RatFunc.eval_mul f q a.property b.property

/-- Polynomial rational functions are regular under extension-field specialization. -/
theorem ratFuncRegularAt₂_polynomial (f : F →+* K) (q : K) (p : F[X]) :
    algebraMap F[X] (RatFunc F) p ∈ ratFuncRegularAt₂ f q := by
  change (algebraMap F[X] (RatFunc F) p).denom.eval₂ f q ≠ 0
  simp

/-- Inverses of polynomials that do not vanish specialize regularly into extension fields. -/
theorem ratFuncRegularAt₂_inverse (f : F →+* K) (q : K) (p : F[X]) (hp : p.eval₂ f q ≠ 0) :
    (algebraMap F[X] (RatFunc F) p)⁻¹ ∈ ratFuncRegularAt₂ f q := by
  intro hz
  have hd := RatFunc.denom_div_dvd (1 : F[X]) p
  simp only [map_one, one_div] at hd
  exact hp (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f q hd hz)

/-- Every integer power of the formal variable specializes regularly at a nonzero extension-field point. -/
theorem ratFunc_X_zpow_regular₂ (f : F →+* K) (q : K) (hq : q ≠ 0) (n : ℤ) :
    (RatFunc.X : RatFunc F)^n ∈ ratFuncRegularAt₂ f q := by
  apply subring_zpow_mem_of_inv_mem
  · exact ratFuncRegularAt₂_polynomial f q X
  · exact ratFuncRegularAt₂_inverse f q X (by simpa using hq)

/-- Integer powers of the formal variable specialize to the corresponding powers of a nonzero point. -/
theorem ratFunc_X_zpow_eval₂ (f : F →+* K) (q : K) (hq : q ≠ 0) (n : ℤ) :
    RatFunc.eval f q ((RatFunc.X : RatFunc F)^n) = q^n := by
  let Q : ratFuncRegularAt₂ f q := ⟨RatFunc.X, ratFuncRegularAt₂_polynomial f q X⟩
  let I : ratFuncRegularAt₂ f q := ⟨RatFunc.X⁻¹, ratFuncRegularAt₂_inverse f q X (by simpa using hq)⟩
  have hQ : ratFuncSpecialization₂ f q Q=q := RatFunc.eval_X _ _
  have hI : ratFuncSpecialization₂ f q I=q⁻¹ := by
    have he : Q*I=1 := by apply Subtype.ext; exact mul_inv_cancel₀ RatFunc.X_ne_zero
    have hh := congrArg (ratFuncSpecialization₂ f q) he
    rw [map_mul, map_one, hQ] at hh
    exact mul_left_cancel₀ hq (hh.trans (mul_inv_cancel₀ hq).symm)
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    change ratFuncSpecialization₂ f q (Q^n)=q^n
    rw [map_pow, hQ]
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    change ratFuncSpecialization₂ f q (I^(n+1))=_
    rw [map_pow, hI]

end
end Lambert
