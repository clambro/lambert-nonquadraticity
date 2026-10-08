import Lambert.Determinants.TranslatedInfinity

/-!
# Infinity normalization of the selected Lambert window

Translation of the pole window changes the signed exponent by a linear term.
The selected rectangular window therefore has an exact cubic normalization.
-/
namespace Lambert
noncomputable section
open Finset
open scoped Classical

/-- Translating a pole window changes its signed infinity exponent by the total row-weight imbalance. -/
theorem lambertTranslatedInfinityExponent_translate (h k d s : ℕ) :
    lambertTranslatedInfinityExponent h k d s =
      lambertInfinityExponent h d s + (k : ℤ) * h * ((d : ℤ) - s) := by
  have hs := Equiv.sum_comp (Tuple.sort (lambertAugmentedRowWeight h d s))
    (fun j => (lambertAugmentedRowWeight h d s j : ℤ))
  have hw : (∑ j : Fin (h + d), (j.val : ℤ)) -
      (∑ j : Fin (h + d), (lambertAugmentedRowWeight h d s j : ℤ)) =
      (h : ℤ) * ((d : ℤ) - s) := by
    rw [← sum_sub_distrib, Fin.sum_univ_add]
    simp only [lambertAugmentedRowWeight, Fin.addCases_left, Fin.addCases_right,
      Fin.val_castAdd, Fin.val_natAdd, Nat.cast_add]
    simp_rw [show ∀ j : Fin h, (j.val : ℤ) - (j.val + s) = -(s : ℤ) by intro j; ring,
      show ∀ j : Fin d, (h : ℤ) + j.val - j.val = h by intro j; ring]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  unfold lambertTranslatedInfinityExponent lambertInfinityExponent
  simp_rw [mul_add, add_mul, sum_add_distrib, ← mul_sum, ← sum_mul]
  rw [hs]
  nlinarith [congrArg (fun x : ℤ => (k : ℤ) * x) hw]

/-- Disjoint row ranges give the exact signed normalization for a translated window. -/
theorem lambertTranslatedInfinityExponent_of_le (h k d s : ℕ) (hds : d ≤ s) :
    lambertTranslatedInfinityExponent h k d s =
      -((s : ℤ) - d) * ∑ r : Fin h, ((k : ℤ) + d + r.val) := by
  rw [lambertTranslatedInfinityExponent_translate, lambertInfinityExponent_of_le h d s hds]
  have he : (∑ r : Fin h, ((k : ℤ) + d + r.val)) =
      (h : ℤ) * k + ∑ r : Fin h, ((d : ℤ) + r.val) := by
    simp_rw [add_assoc, sum_add_distrib]
    simp
  rw [he]
  ring

/-- The selected six-presentation family has an exact signed cubic infinity exponent. -/
theorem lambertRefinementFamily_infinity_exponent (N : ℕ) :
    lambertTranslatedInfinityExponent (500*N) (27*N) (16*N) (41*N) =
      -(3662500 : ℤ) * N^3 + 6250 * N^2 := by
  have hl (h : ℕ) : 2 * (∑ r ∈ range h, (r : ℤ)) = (h : ℤ) * (h - 1) := by
    induction h with
    | zero => simp
    | succ h ih => rw [sum_range_succ]; push_cast; nlinarith
  have he := hl (500*N)
  rw [← Fin.sum_univ_eq_sum_range] at he
  rw [lambertTranslatedInfinityExponent_of_le _ _ _ _ (by omega)]
  simp_rw [sum_add_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast at he ⊢
  nlinarith

end
end Lambert
