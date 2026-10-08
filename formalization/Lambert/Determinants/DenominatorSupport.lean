import Lambert.Arithmetic.RatFuncPoleSupport
import Lambert.Determinants.IntegerPresentation
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Denominator support for translated Lambert determinants

The augmented identity excludes every pole except zero and roots of unity.
-/
namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical

/-- The allowed Lambert denominator factors are the base variable and the
positive-order cyclotomic polynomials, up to multiplication by a nonzero constant. -/
def IsLambertPoleFactor (p : ℚ[X]) : Prop :=
  Associated p X ∨ ∃ n : ℕ, 0 < n ∧ Associated p (cyclotomic n ℚ)

/-- Every irreducible factor of a formal base-power difference is a Lambert pole factor. -/
theorem lambertPowerDifference_denominator_support (i j : ℕ) (hij : i < j) (p : ℚ[X])
    (hp : Irreducible p) (hd : p ∣ X ^ j - X ^ i) : IsLambertPoleFactor p := by
  have he : (X ^ j - X ^ i : ℚ[X]) = X ^ i * (X ^ (j - i) - 1) := by
    rw [mul_sub, ← pow_add, Nat.add_sub_of_le hij.le, mul_one]
  rw [he] at hd
  rcases hp.prime.dvd_or_dvd hd with h | h
  · exact Or.inl (hp.associated_of_dvd irreducible_X (hp.prime.dvd_of_dvd_pow h))
  · rw [← prod_cyclotomic_eq_X_pow_sub_one (Nat.sub_pos_of_lt hij) ℚ] at h
    obtain ⟨n, hn, hpn⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp h
    have hnpos : 0 < n := Nat.pos_of_mem_divisors hn
    exact Or.inr ⟨n, hnpos, hp.associated_of_dvd (cyclotomic.irreducible_rat hnpos) hpn⟩

/-- Every irreducible denominator factor of an augmented-window Lambert
coefficient is either the base variable or a positive-order cyclotomic factor. -/
theorem lambertPoleDeterminant_denominator_support (h k d s a : ℕ) (p : ℚ[X])
    (hp : Irreducible p)
    (hd : p ∣ ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s).coeff a).denom) :
    IsLambertPoleFactor p := by
  have hm : (lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s).coeff a ∈
      ratFuncPoleSupport IsLambertPoleFactor := by
    apply lambertPoleDeterminant_coeff_mem_subring
    · exact ratFuncPoleSupport_polynomial _ X
    · intro n
      simpa only [map_sub, map_pow, RatFunc.algebraMap_X, map_one, pow_zero, one_div] using
        ratFuncPoleSupport_inverse IsLambertPoleFactor (X ^ (n + 1) - X ^ 0)
          (lambertPowerDifference_denominator_support 0 (n + 1) (Nat.succ_pos n))
    · intro i j hij
      simpa only [map_sub, map_pow, RatFunc.algebraMap_X] using
        ratFuncPoleSupport_inverse IsLambertPoleFactor (X ^ j - X ^ i)
          (lambertPowerDifference_denominator_support i j hij)
  exact hm p hp hd

end
end Lambert
