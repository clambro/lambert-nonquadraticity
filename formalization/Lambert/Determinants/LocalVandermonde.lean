import Lambert.Determinants.LocalExpansion
import Lambert.Arithmetic.GeometricCollisionCount
import Lambert.Arithmetic.PowerSeriesLocalParameter

/-!
# Local orders of geometric Vandermonde factors

At an exponential local base, distinct powers have a simple collision precisely
when their constant phases agree.
-/

namespace Lambert

noncomputable section

open PowerSeries Finset
open scoped Classical

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- At a nonzero phase, the exponential displacement is a formal local parameter
of order exactly one. -/
theorem lambertLocalBase_displacement_order (ζ : K) (hζ : ζ ≠ 0) :
    (lambertLocalBase ζ - C (constantCoeff (lambertLocalBase ζ))).order = 1 := by
  apply order_eq_nat.mpr
  constructor
  · simpa [lambertLocalBase, coeff_C_mul, coeff_exp, coeff_C] using hζ
  · intro k hk
    have hk0 : k = 0 := by omega
    simp [hk0]

/-- Two distinct powers of a nonzero exponential base have difference of order
one when their phases coincide, and order zero otherwise. -/
theorem lambertLocalBase_pow_sub_order (ζ : K) (hζ : ζ ≠ 0)
    (i j : ℕ) (hij : i < j) :
    (lambertLocalBase ζ ^ j - lambertLocalBase ζ ^ i).order =
      if ζ ^ j = ζ ^ i then 1 else 0 := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have h0 : coeff 0 (lambertLocalBase ζ ^ j - lambertLocalBase ζ ^ i) = ζ ^ j - ζ ^ i := by
    simp [lambertLocalBase]
  have h1 : coeff 1 (lambertLocalBase ζ ^ j - lambertLocalBase ζ ^ i) =
      ζ ^ j * (j : K) - ζ ^ i * (i : K) := by
    simp only [lambertLocalBase_pow, map_sub, coeff_C_mul, coeff_rescale, coeff_exp]
    simp
  by_cases he : ζ ^ j = ζ ^ i
  · rw [if_pos he]
    apply order_eq_nat.mpr
    constructor
    · rw [h1, he, ← mul_sub]
      exact mul_ne_zero (pow_ne_zero _ hζ) (sub_ne_zero.mpr (by exact_mod_cast hij.ne'))
    · intro k hk
      have hk0 : k = 0 := by omega
      rw [hk0, h0, he, sub_self]
  · rw [if_neg he]
    apply order_eq_nat.mpr
    exact ⟨by rw [h0]; exact sub_ne_zero.mpr he, by intro k hk; omega⟩

/-- Every geometric Vandermonde factor has local order one for a root-order
multiple difference and zero for every other difference. -/
theorem lambertLocalBase_pow_sub_order_primitive (ζ : K) {n : ℕ}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (i j : ℕ) (hij : i < j) :
    (lambertLocalBase ζ ^ j - lambertLocalBase ζ ^ i).order =
      if n ∣ j - i then 1 else 0 := by
  rw [lambertLocalBase_pow_sub_order ζ (hζ.ne_zero (Nat.ne_of_gt hn)) i j hij,
    (hζ.isOfFinOrder (Nat.ne_of_gt hn)).pow_eq_pow_iff_modEq,
    ← hζ.eq_orderOf, Nat.ModEq.comm, Nat.modEq_iff_dvd' hij.le]
  by_cases hd : n ∣ j - i <;> simp only [hd, ↓reduceIte]

/-- The local geometric Vandermonde order counts pairs whose index difference
is divisible by the primitive root order. -/
theorem lambertLocalVandermonde_order (ζ : K) (h n : ℕ)
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    (Matrix.vandermonde (fun i : Fin h => lambertLocalBase ζ ^ i.val)).det.order =
      ∑ i : Fin h, ∑ j ∈ Ioi i, (if n ∣ j.val - i.val then (1 : ℕ∞) else 0) := by
  rw [Matrix.det_vandermonde, order_prod]
  apply sum_congr rfl
  intro i _
  rw [order_prod]
  apply sum_congr rfl
  intro j hj
  have hij : i < j := mem_Ioi.mp hj
  exact lambertLocalBase_pow_sub_order_primitive ζ hn hζ _ _ (Fin.lt_def.mp hij)

/-- The geometric Vandermonde has the exact finite deficit-sum local order. -/
theorem lambertLocalVandermonde_order_deficits (ζ : K) (h n : ℕ)
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    (Matrix.vandermonde (fun i : Fin h => lambertLocalBase ζ ^ i.val)).det.order =
      (↑(∑ k ∈ range h, (h - (k + 1) * n)) : ℕ∞) := by
  rw [lambertLocalVandermonde_order ζ h n hn hζ,
    ← geometricCollisionCount_eq_sum_deficits h n hn]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

end

end Lambert
