import Lambert.Determinants.FormalSeries

/-!
# Local geometric arithmetic at zero

Distinct powers of the formal parameter have difference order equal to the
smaller exponent. Products retain all complementary-denominator orders.
-/

namespace Lambert
noncomputable section
open PowerSeries Finset
open scoped Classical WithZero
variable {K : Type*} [Field K]

/-- The zero-place geometric base is the Laurent image of the formal parameter. -/
def lambertZeroBase (K : Type*) [Field K] : LaurentSeries K :=
  (PowerSeries.X : PowerSeries K)

/-- Every power of the zero-place base has its prescribed valuation. -/
theorem lambertZeroBase_pow_valuation (m : ℕ) :
    Valued.v (lambertZeroBase K ^ m) = WithZero.exp (-(m : ℤ)) := by
  simpa only [map_pow, lambertZeroBase] using
    laurentSeries_valuation_eq_of_order ((PowerSeries.X : PowerSeries K) ^ m) m (order_X_pow m)

/-- Distinct powers of the formal parameter give distinct Laurent series. -/
theorem lambertZeroBase_pow_injective : Function.Injective (fun m : ℕ => lambertZeroBase K ^ m) := by
  intro i j he
  have hv := congrArg Valued.v he
  rw [lambertZeroBase_pow_valuation, lambertZeroBase_pow_valuation, WithZero.exp_inj] at hv
  omega

/-- The zero-place base is nonzero. -/
theorem lambertZeroBase_ne_zero : lambertZeroBase K ≠ 0 := by
  intro he
  have hv := lambertZeroBase_pow_valuation (K := K) 1
  simp only [he, zero_pow (by omega : (1 : ℕ) ≠ 0), map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

/-- The difference of two distinct geometric nodes has order equal to the
smaller node index. -/
theorem lambertZeroBase_sub_valuation (i j : ℕ) (hij : i ≠ j) :
    Valued.v (lambertZeroBase K ^ i - lambertZeroBase K ^ j) =
      WithZero.exp (-((min i j : ℕ) : ℤ)) := by
  rcases lt_or_gt_of_ne hij with hl | hr
  · rw [Valuation.map_sub_eq_of_lt_left, lambertZeroBase_pow_valuation, min_eq_left hl.le]
    rw [lambertZeroBase_pow_valuation, lambertZeroBase_pow_valuation, WithZero.exp_lt_exp]
    omega
  · rw [Valuation.map_sub_eq_of_lt_right, lambertZeroBase_pow_valuation, min_eq_right hr.le]
    rw [lambertZeroBase_pow_valuation, lambertZeroBase_pow_valuation, WithZero.exp_lt_exp]
    omega

/-- A product of differences from distinct formal nodes has order equal to the sum of the smaller node indices. -/
theorem lambertZeroDifferenceProduct_valuation {ι : Type*} (s : Finset ι) (i : ι → ℕ)
    (j : ℕ) (hi : ∀ v ∈ s, i v ≠ j) :
    Valued.v (∏ v ∈ s, (lambertZeroBase K ^ j - lambertZeroBase K ^ i v)) =
      WithZero.exp (-(∑ v ∈ s, ((min (i v) j : ℕ) : ℤ))) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
    rw [prod_insert hv, sum_insert hv, map_mul,
      lambertZeroBase_sub_valuation j (i v) (hi v (mem_insert_self _ _)).symm,
      min_comm j, ih (fun v hv => hi v (mem_insert_of_mem hv)), neg_add, WithZero.exp_add]

end
end Lambert
