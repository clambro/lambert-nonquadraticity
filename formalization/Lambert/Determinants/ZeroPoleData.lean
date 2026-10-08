import Lambert.Arithmetic.RatFuncLocalExpansion
import Lambert.Determinants.FinitePartLimit

/-! # Zero-place embedding and finite-prefix correction -/
namespace Lambert
noncomputable section
open Polynomial Finset Matrix Filter
open scoped Classical WithZero Topology
variable {K : Type*} [Field K]

/-- Adding a positive-power Lambert prefix preserves the Laurent valuation unit ball. -/
theorem lambertPrefixCorrection_valuation_le_one (z : LaurentSeries K) (hz : Valued.v z ≤ 1) (N : ℕ) :
    Valued.v (z + lambertPositivePrefix (lambertZeroBase K) N) ≤ 1 := by
  apply Valuation.map_add_le Valued.v hz
  have he := laurentSeries_valuation_le_of_order (lambertFormalPrefix K N) 0 (by simp)
  rw [lambertFormalPrefix_laurent] at he
  simpa only [Nat.cast_zero, neg_zero, WithZero.exp_zero, lambertZeroBase] using he

private theorem zeroParameter_order :
    ((PowerSeries.X : PowerSeries ℚ) - PowerSeries.C
      (PowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℚ))).order = 1 := by
  simp

/-- The zero-place embedding expands the formal rational base as the Laurent parameter. -/
def lambertZeroMap : RatFunc ℚ →+* LaurentSeries ℚ :=
  ratFuncLocalExpansion (RingHom.id ℚ) PowerSeries.X zeroParameter_order

/-- The formal rational base maps to the zero-place geometric base. -/
theorem lambertZeroMap_X : lambertZeroMap RatFunc.X = lambertZeroBase ℚ :=
  ratFuncLocalExpansion_X _ _ _

/-- A signed zero-place bound controls the natural multiplicity in the reduced denominator. -/
theorem lambertZeroMap_denominator_power_bound (f : RatFunc ℚ) (E : ℤ)
    (hb : Valued.v (lambertZeroMap f) ≤ WithZero.exp E) (e : ℕ)
    (he : (X : ℚ[X])^e ∣ f.denom) : e ≤ E.toNat := by
  have hv := hb.trans (WithZero.exp_le_exp.mpr (Int.self_le_toNat E))
  exact ratFuncLocalExpansion_denominator_power_bound (RingHom.id ℚ) PowerSeries.X
    (by simp) f E.toNat hv X (by simp) e he

end
end Lambert
