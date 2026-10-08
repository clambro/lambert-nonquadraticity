import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Algebra.Polynomial.Div

/-!
# Polynomial substitution in a formal local parameter

A power series with a simple displacement from its constant term preserves
polynomial root multiplicity and defines an injective substitution map.
-/

namespace Lambert

noncomputable section

variable {K : Type*} [Field K]

/-- The constant coefficient of polynomial substitution is evaluation at the
constant coefficient of the substituted series. -/
theorem powerSeries_constantCoeff_eval₂ (p : Polynomial K) (u : PowerSeries K) :
    PowerSeries.constantCoeff (p.eval₂ PowerSeries.C u) = p.eval (PowerSeries.constantCoeff u) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval₂_add, map_add, hp, hq, Polynomial.eval_add]
  | monomial n a => simp [Polynomial.eval₂_monomial]

/-- Substitution by a series whose displacement has order one preserves the
root multiplicity of every nonzero polynomial at its constant term. -/
theorem powerSeries_eval₂_order_eq_rootMultiplicity (u : PowerSeries K)
    (hu : (u - PowerSeries.C (PowerSeries.constantCoeff u)).order = 1)
    (p : Polynomial K) (hp : p ≠ 0) :
    (p.eval₂ PowerSeries.C u).order = p.rootMultiplicity (PowerSeries.constantCoeff u) := by
  obtain ⟨q, he, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp
    (PowerSeries.constantCoeff u)
  have hq0 : q.eval (PowerSeries.constantCoeff u) ≠ 0 := by
    simpa only [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot] using hq
  have ho : (q.eval₂ PowerSeries.C u).order = 0 := by
    apply PowerSeries.order_eq_nat.mpr
    constructor
    · rw [PowerSeries.coeff_zero_eq_constantCoeff, powerSeries_constantCoeff_eval₂]
      exact hq0
    · intro i hi
      omega
  conv_lhs => rw [he]
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_C, PowerSeries.order_mul, PowerSeries.order_pow, hu, ho]
  simp

/-- Substitution by a series with first-order displacement is injective on polynomials. -/
theorem powerSeries_eval₂_injective (u : PowerSeries K)
    (hu : (u - PowerSeries.C (PowerSeries.constantCoeff u)).order = 1) :
    Function.Injective (Polynomial.eval₂RingHom PowerSeries.C u : Polynomial K →+* PowerSeries K) := by
  intro p q he
  by_contra hn
  have ho := powerSeries_eval₂_order_eq_rootMultiplicity u hu (p - q) (sub_ne_zero.mpr hn)
  have hz : (p - q).eval₂ PowerSeries.C u = 0 := by
    change (Polynomial.eval₂RingHom PowerSeries.C u) (p - q) = 0
    rw [map_sub, he, sub_self]
  rw [hz, PowerSeries.order_zero] at ho
  simp at ho

end

end Lambert
