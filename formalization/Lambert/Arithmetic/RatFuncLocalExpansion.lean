import Lambert.Arithmetic.PowerSeriesLocalParameter
import Lambert.Arithmetic.LaurentSeriesLocalOrder

/-!
# Rational functions in a formal local parameter

A power series with simple displacement defines an injective rational-function
expansion, with the expected numerator-minus-denominator root order.
-/

namespace Lambert

noncomputable section

open PowerSeries WithZero
open scoped WithZero nonZeroDivisors

variable {F K : Type*} [Field F] [Field K]

/-- Polynomial substitution followed by inclusion in Laurent series. -/
def polynomialLocalExpansion (f : F →+* K) (u : PowerSeries K) : Polynomial F →+* LaurentSeries K :=
  ((HahnSeries.ofPowerSeries ℤ K).comp (Polynomial.eval₂RingHom C u)).comp
    (Polynomial.mapRingHom f)

/-- A simple local parameter gives an injective polynomial expansion. -/
theorem polynomialLocalExpansion_injective (f : F →+* K) (u : PowerSeries K)
    (hu : (u - C (constantCoeff u)).order = 1) :
    Function.Injective (polynomialLocalExpansion f u) :=
  (HahnSeries.ofPowerSeries_injective.comp (powerSeries_eval₂_injective u hu)).comp
    (Polynomial.map_injective f f.injective)

/-- Nonzero polynomial denominators remain nonzero under a simple local expansion. -/
theorem polynomialLocalExpansion_regular (f : F →+* K) (u : PowerSeries K)
    (hu : (u - C (constantCoeff u)).order = 1) :
    (Polynomial F)⁰ ≤ (LaurentSeries K)⁰.comap (polynomialLocalExpansion f u) := by
  intro p hp
  exact map_mem_nonZeroDivisors _ (polynomialLocalExpansion_injective f u hu) hp

/-- Rational functions expanded at a simple formal local parameter. -/
def ratFuncLocalExpansion (f : F →+* K) (u : PowerSeries K)
    (hu : (u - C (constantCoeff u)).order = 1) : RatFunc F →+* LaurentSeries K :=
  RatFunc.liftRingHom (polynomialLocalExpansion f u) (polynomialLocalExpansion_regular f u hu)

/-- Local expansion sends the rational-function variable to the chosen parameter. -/
theorem ratFuncLocalExpansion_X (f : F →+* K) (u : PowerSeries K)
    (hu : (u - C (constantCoeff u)).order = 1) :
    ratFuncLocalExpansion f u hu RatFunc.X = (u : LaurentSeries K) := by
  rw [ratFuncLocalExpansion, RatFunc.liftRingHom_X]
  simp [polynomialLocalExpansion]

/-- Polynomial local expansion has the valuation prescribed by root multiplicity. -/
theorem polynomialLocalExpansion_valuation (f : F →+* K) (u : PowerSeries K)
    (hu : (u - C (constantCoeff u)).order = 1) (p : Polynomial F) (hp : p ≠ 0) :
    Valued.v (polynomialLocalExpansion f u p) =
      exp (-((p.map f).rootMultiplicity (constantCoeff u) : ℤ)) :=
  laurentSeries_valuation_eq_of_order _ _
    (powerSeries_eval₂_order_eq_rootMultiplicity u hu (p.map f)
      ((Polynomial.map_ne_zero_iff f.injective).mpr hp))

/-- The local order of a nonzero rational function is numerator root
multiplicity minus denominator root multiplicity. -/
theorem ratFuncLocalExpansion_valuation (f : F →+* K) (u : PowerSeries K)
    (hu : (u - C (constantCoeff u)).order = 1) (g : RatFunc F) (hg : g ≠ 0) :
    Valued.v (ratFuncLocalExpansion f u hu g) =
      exp (((g.denom.map f).rootMultiplicity (constantCoeff u) : ℤ) -
        ((g.num.map f).rootMultiplicity (constantCoeff u) : ℤ)) := by
  rw [ratFuncLocalExpansion, RatFunc.liftRingHom_apply, map_div₀,
    polynomialLocalExpansion_valuation f u hu _ (RatFunc.num_ne_zero hg),
    polynomialLocalExpansion_valuation f u hu _ (RatFunc.denom_ne_zero g), ← exp_sub]
  congr 1
  omega


/-- A local pole bound controls the root multiplicity of the reduced denominator;
coprimality prevents numerator cancellation at that root. -/
theorem ratFuncLocalExpansion_denom_rootMultiplicity_le (f : F →+* K) (u : PowerSeries K)
    (hu : (u - C (constantCoeff u)).order = 1) (g : RatFunc F) (E : ℕ)
    (hv : Valued.v (ratFuncLocalExpansion f u hu g) ≤ exp (E : ℤ)) :
    (g.denom.map f).rootMultiplicity (constantCoeff u) ≤ E := by
  by_cases hg : g = 0
  · simp only [hg, RatFunc.denom_zero, Polynomial.map_one]
    change (Polynomial.C (1 : K)).rootMultiplicity _ ≤ E
    rw [Polynomial.rootMultiplicity_C]
    exact Nat.zero_le _
  by_cases hd : (g.denom.map f).eval (constantCoeff u) = 0
  · have hnum : (g.num.map f).eval (constantCoeff u) ≠ 0 := by
      intro hnum
      obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom g
      have he := congrArg (Polynomial.eval₂ f (constantCoeff u)) hab
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_one] at he
      simp only [Polynomial.eval₂_eq_eval_map, hnum, hd, mul_zero, zero_add] at he
      exact zero_ne_one he
    have hm := Polynomial.rootMultiplicity_eq_zero hnum
    rw [ratFuncLocalExpansion_valuation f u hu g hg, hm, Nat.cast_zero, sub_zero,
      exp_le_exp] at hv
    exact_mod_cast hv
  · rw [Polynomial.rootMultiplicity_eq_zero hd]
    exact Nat.zero_le _

/-- Divisibility by a power of a polynomial forces at least that root
multiplicity at any root after scalar extension. -/
theorem polynomial_pow_dvd_le_rootMultiplicity (f : F →+* K) (a : K)
    (P q : Polynomial F) (hq : q ≠ 0) (hP : (P.map f).eval a = 0)
    (e : ℕ) (he : P ^ e ∣ q) : e ≤ (q.map f).rootMultiplicity a := by
  have hqmap : q.map f ≠ 0 := (Polynomial.map_ne_zero_iff f.injective).mpr hq
  rw [Polynomial.le_rootMultiplicity_iff hqmap]
  have hx : Polynomial.X - Polynomial.C a ∣ P.map f := Polynomial.dvd_iff_isRoot.mpr hP
  have hd := Polynomial.map_dvd f he
  rw [Polynomial.map_pow] at hd
  exact (pow_dvd_pow_of_dvd hx e).trans hd

/-- A local expansion pole bound descends to a power-divisibility bound on
the original rational-function denominator over its original coefficient field. -/
theorem ratFuncLocalExpansion_denominator_power_bound (f : F →+* K) (u : PowerSeries K)
    (hu : (u - C (constantCoeff u)).order = 1) (g : RatFunc F) (E : ℕ)
    (hv : Valued.v (ratFuncLocalExpansion f u hu g) ≤ exp (E : ℤ))
    (P : Polynomial F) (hP : (P.map f).eval (constantCoeff u) = 0)
    (e : ℕ) (he : P ^ e ∣ g.denom) : e ≤ E :=
  (polynomial_pow_dvd_le_rootMultiplicity f _ P g.denom (RatFunc.denom_ne_zero g) hP e he).trans
    (ratFuncLocalExpansion_denom_rootMultiplicity_le f u hu g E hv)

end

end Lambert
