import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Lambert.Determinants.LocalVandermonde
import Lambert.Arithmetic.RatFuncLocalExpansion

/-! # Expansion of the formal Lambert base at an exponential phase -/
namespace Lambert
noncomputable section
open PowerSeries
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Expansion of the formal rational base at a nonzero exponential phase. -/
def lambertLocalMap (ζ : K) (hz : ζ ≠ 0) : RatFunc ℚ →+* LaurentSeries K :=
  ratFuncLocalExpansion (algebraMap ℚ K) (lambertLocalBase ζ)
    (lambertLocalBase_displacement_order ζ hz)

/-- The formal rational base expands to the exponential local base. -/
theorem lambertLocalMap_X (ζ : K) (hz : ζ ≠ 0) :
    lambertLocalMap ζ hz RatFunc.X = (lambertLocalBase ζ : LaurentSeries K) :=
  ratFuncLocalExpansion_X _ _ _


/-- Uniform primitive-root local bounds control the cyclotomic multiplicity in a reduced denominator. -/
theorem lambertLocalMap_denominator_power_bound (f : RatFunc ℚ) (n E : ℕ) (hn : 0<n)
    (hb : ∀ (ζ : ℂ) (hζ : IsPrimitiveRoot ζ n),
      Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne') f) ≤ WithZero.exp (E : ℤ))
    (e : ℕ) (he : Polynomial.cyclotomic n ℚ^e ∣ f.denom) : e ≤ E := by
  let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I/n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  apply ratFuncLocalExpansion_denominator_power_bound (algebraMap ℚ ℂ) (lambertLocalBase ζ)
    (lambertLocalBase_displacement_order ζ (hζ.ne_zero hn.ne')) f E
    (hb ζ hζ) (Polynomial.cyclotomic n ℚ) _ e he
  rw [Polynomial.map_cyclotomic]
  have hc : PowerSeries.constantCoeff (lambertLocalBase ζ)=ζ := by simp [lambertLocalBase]
  rw [hc]
  exact hζ.isRoot_cyclotomic hn


end
end Lambert
