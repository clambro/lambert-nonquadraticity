import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Subrings with restricted rational-function poles

Reduced denominator support is stable under ring operations. The support condition
is expressed on irreducible polynomial divisors, so it also excludes unseen poles.
-/
namespace Lambert
noncomputable section
open Polynomial
variable {K : Type*} [Field K]

/-- Rational functions whose irreducible denominator factors belong to a fixed
allowed set form a subring. -/
def ratFuncPoleSupport (allowed : K[X] → Prop) : Subring (RatFunc K) where
  carrier := {f | ∀ p : K[X], Irreducible p → p ∣ f.denom → allowed p}
  zero_mem' := by
    intro p hp hd
    exact (hp.not_isUnit (isUnit_of_dvd_one (by simpa using hd))).elim
  one_mem' := by
    intro p hp hd
    exact (hp.not_isUnit (isUnit_of_dvd_one (by simpa using hd))).elim
  add_mem' := by
    intro f g hf hg p hp hd
    rcases hp.prime.dvd_or_dvd (hd.trans (RatFunc.denom_add_dvd f g)) with h | h
    · exact hf p hp h
    · exact hg p hp h
  mul_mem' := by
    intro f g hf hg p hp hd
    rcases hp.prime.dvd_or_dvd (hd.trans (RatFunc.denom_mul_dvd f g)) with h | h
    · exact hf p hp h
    · exact hg p hp h
  neg_mem' := by
    intro f hf p hp hd
    have he : (-f).denom ∣ f.denom := by
      apply (RatFunc.denom_dvd f.denom_ne_zero).mpr
      refine ⟨-f.num, ?_⟩
      rw [map_neg, neg_div, RatFunc.num_div_denom]
    exact hf p hp (hd.trans he)

/-- A subring containing an element and its inverse contains every integer power of that element. -/
theorem subring_zpow_mem_of_inv_mem {F : Type*} [Field F] (S : Subring F)
    {x : F} (hx : x ∈ S) (hi : x⁻¹ ∈ S) (n : ℤ) : x ^ n ∈ S := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using S.pow_mem hx n
  | negSucc n => simpa only [zpow_negSucc, inv_pow] using S.pow_mem hi (n + 1)

/-- Polynomial rational functions have no denominator factors. -/
theorem ratFuncPoleSupport_polynomial (allowed : K[X] → Prop) (p : K[X]) :
    algebraMap K[X] (RatFunc K) p ∈ ratFuncPoleSupport allowed := by
  intro r hr hd
  exact (hr.not_isUnit (isUnit_of_dvd_one (by simpa using hd))).elim

/-- The inverse of a polynomial has only the irreducible poles of that polynomial. -/
theorem ratFuncPoleSupport_inverse (allowed : K[X] → Prop) (p : K[X])
    (hp : ∀ r : K[X], Irreducible r → r ∣ p → allowed r) :
    (algebraMap K[X] (RatFunc K) p)⁻¹ ∈ ratFuncPoleSupport allowed := by
  intro r hr hd
  apply hp r hr
  have he := RatFunc.denom_div_dvd (1 : K[X]) p
  simp only [map_one, one_div] at he
  exact hd.trans he

end
end Lambert
