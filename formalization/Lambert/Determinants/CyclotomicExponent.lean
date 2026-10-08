import Lambert.Determinants.TaylorFiltration
import Lambert.Determinants.LocalVandermonde
import Lambert.Arithmetic.FiniteDeficitSum

/-!
# The square-window cyclotomic exponent

The exact finite exponent combines the filtered determinant bound, the residue
bound, and the geometric Vandermonde order at every positive root order.
-/

namespace Lambert

open Finset

/-- The square-window cyclotomic pole exponent is a finite positive-part sum. -/
def lambertCyclotomicExponent (h n : ℕ) : ℕ :=
  3 * (h - n) - (h - 2 * n) + ∑ k ∈ range h, (h - (2 * k + 3) * n)

/-- The stronger of the residue and Taylor-filtration lower orders. -/
def lambertLocalDeterminantOrder (h n : ℕ) : ℕ :=
  max (2 * min h n - h) (∑ k ∈ range h, (h - (k + 1) * (2 * n)))

/-- The cyclotomic exponent accounts exactly for regularization, Vandermonde
collisions, and the stronger available determinant cancellation. -/
theorem lambertCyclotomicExponent_accounting (h n : ℕ) (hn : 0 < n) :
    lambertCyclotomicExponent h n + lambertLocalDeterminantOrder h n =
      h + ∑ k ∈ range h, (h - (k + 1) * n) := by
  have hs := sum_deficits_even_odd h n hn
  unfold lambertCyclotomicExponent lambertLocalDeterminantOrder
  by_cases hh : h ≤ 2 * n
  · have hb : (∑ k ∈ range h, (h - (k + 1) * (2 * n))) = 0 := by
      apply sum_eq_zero
      intro k _
      have he : 2 * n ≤ (k + 1) * (2 * n) := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
      omega
    have ht : (∑ k ∈ range h, (h - (2 * k + 3) * n)) = 0 := by
      apply sum_eq_zero
      intro k _
      have he : 2 * n ≤ (2 * k + 3) * n := Nat.mul_le_mul_right n (by omega)
      omega
    rw [hb, ht] at hs ⊢
    by_cases hhn : h ≤ n
    · rw [min_eq_left hhn]
      omega
    · rw [min_eq_right (by omega)]
      omega
  · rw [min_eq_right (by omega)]
    have hz : 2 * n - h = 0 := by omega
    rw [hz, max_eq_right (Nat.zero_le _)]
    omega

/-- Root orders at least the matrix size have zero square-window pole exponent. -/
theorem lambertCyclotomicExponent_eq_zero_of_le (h n : ℕ) (hh : h ≤ n) :
    lambertCyclotomicExponent h n = 0 := by
  unfold lambertCyclotomicExponent
  have ht : (∑ k ∈ range h, (h - (2 * k + 3) * n)) = 0 := by
    apply sum_eq_zero
    intro k _
    have he : n ≤ (2 * k + 3) * n := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [ht]
  omega

end Lambert
