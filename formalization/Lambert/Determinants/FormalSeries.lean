import Lambert.Determinants.FinitePartGenerators
import Lambert.Arithmetic.LaurentSeriesLocalOrder

/-!
# The formal Lambert germ at zero

Finite positive Lambert prefixes stabilize coefficient by coefficient. The
explicit tail-order bound supplies the formal limit used in finite-part sums.
-/

namespace Lambert

noncomputable section

open PowerSeries Finset

variable {K : Type*} [Field K]

/-- A positive formal Lambert term has numerator equal to a positive power
of the local parameter and an invertible geometric denominator. -/
def lambertFormalTerm (K : Type*) [Field K] (m : ℕ) : PowerSeries K :=
  X ^ m * (1 - X ^ m)⁻¹

/-- Every positive formal Lambert term begins exactly at its index. -/
theorem lambertFormalTerm_order (m : ℕ) (hm : 0 < m) :
    (lambertFormalTerm K m).order = m := by
  have hc : constantCoeff (1 - (X : PowerSeries K) ^ m) = 1 := by simp [hm.ne']
  have hi : ((1 - (X : PowerSeries K) ^ m)⁻¹).order = 0 := by
    apply order_eq_nat.mpr
    constructor
    · rw [coeff_zero_eq_constantCoeff, constantCoeff_inv, hc, inv_one]
      exact one_ne_zero
    · intro k hk
      omega
  rw [lambertFormalTerm, order_mul, order_X_pow, hi, add_zero]

/-- A finite formal Lambert prefix contains the terms with positive indices
at most its cutoff. -/
def lambertFormalPrefix (K : Type*) [Field K] (N : ℕ) : PowerSeries K :=
  ∑ k ∈ range N, lambertFormalTerm K (k + 1)

/-- Extending a formal Lambert prefix past a coefficient index leaves that
coefficient unchanged. -/
theorem lambertFormalPrefix_coeff_stable (N M k : ℕ) (hNM : N ≤ M) (hk : k ≤ N) :
    coeff k (lambertFormalPrefix K M) = coeff k (lambertFormalPrefix K N) := by
  obtain ⟨T, rfl⟩ := Nat.exists_eq_add_of_le hNM
  rw [lambertFormalPrefix, sum_range_add, map_add]
  have hz : coeff k (∑ i ∈ range T, lambertFormalTerm K (N + i + 1)) = 0 := by
    rw [map_sum]
    apply sum_eq_zero
    intro i _
    apply coeff_of_lt_order
    rw [lambertFormalTerm_order _ (by omega)]
    exact_mod_cast (show k < N + i + 1 by omega)
  rw [hz, add_zero]
  rfl

/-- The formal Lambert series is defined by the stabilized coefficients of
its finite positive prefixes. -/
def lambertFormalSeries (K : Type*) [Field K] : PowerSeries K :=
  PowerSeries.mk (fun k => coeff k (lambertFormalPrefix K k))

/-- A cutoff at least the coefficient index recovers that coefficient of the
formal Lambert series exactly. -/
theorem lambertFormalSeries_coeff_eq_prefix (N k : ℕ) (hk : k ≤ N) :
    coeff k (lambertFormalSeries K) = coeff k (lambertFormalPrefix K N) := by
  rw [lambertFormalSeries, coeff_mk]
  exact (lambertFormalPrefix_coeff_stable k N k hk le_rfl).symm

/-- The difference between the formal Lambert series and its cutoff-`N`
prefix has order at least `N+1`. -/
theorem lambertFormalSeries_sub_prefix_order (N : ℕ) :
    ((N + 1 : ℕ) : ℕ∞) ≤ (lambertFormalSeries K - lambertFormalPrefix K N).order := by
  apply nat_le_order
  intro k hk
  rw [map_sub, lambertFormalSeries_coeff_eq_prefix N k (by omega), sub_self]

/-- The Laurent image of a formal Lambert term is its intended rational term. -/
theorem lambertFormalTerm_laurent (m : ℕ) (hm : 0 < m) :
    (HahnSeries.ofPowerSeries ℤ K) (lambertFormalTerm K m) =
      ((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ m /
        (1 - ((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ m) := by
  let f := HahnSeries.ofPowerSeries ℤ K
  have hc : constantCoeff (1 - (X : PowerSeries K) ^ m) ≠ 0 := by simp [hm.ne']
  have hi := congrArg f (PowerSeries.inv_mul_cancel (1 - (X : PowerSeries K) ^ m) hc)
  simp only [map_mul, map_sub, map_pow, map_one] at hi
  have hd : 1 - f X ^ m ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hi
    exact zero_ne_one hi
  change f (X ^ m * (1 - X ^ m)⁻¹) = _
  rw [map_mul, map_pow]
  rw [(eq_div_iff hd).mpr hi, one_div, div_eq_mul_inv]

/-- The Laurent image of a finite formal prefix is the corresponding rational
positive Lambert prefix. -/
theorem lambertFormalPrefix_laurent (N : ℕ) :
    (HahnSeries.ofPowerSeries ℤ K) (lambertFormalPrefix K N) =
      lambertPositivePrefix (((PowerSeries.X : PowerSeries K) : LaurentSeries K)) N := by
  simp only [lambertFormalPrefix, map_sum, lambertFormalTerm_laurent _ (Nat.succ_pos _),
    lambertPositivePrefix]

end

end Lambert
