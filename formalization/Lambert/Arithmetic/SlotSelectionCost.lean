import Lambert.Arithmetic.LaurentDeterminantBound

/-! # Rearrangement bounds for capacity-constrained slot selections -/
namespace Lambert
noncomputable section
open Finset
open scoped Classical

/-- A strictly increasing list of natural numbers has its rth entry at least r. -/
theorem strictMono_fin_nat_lower {h : ℕ} (f : Fin h → ℕ) (hf : StrictMono f) :
    ∀ r, r.val ≤ f r := by
  cases h with
  | zero => exact fun r => Fin.elim0 r
  | succ h =>
    intro r
    induction r using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ r ih =>
      have he := hf (show r.castSucc < r.succ by simp)
      change r.val + 1 ≤ f r.succ
      change r.val ≤ f r.castSucc at ih
      omega

/-- A bound on all capacity-admissible node costs bounds every injective slot selection and row permutation. -/
theorem slotSelection_cost_bound (h M : ℕ) (slot : ℕ → ℕ) (hslot : Monotone slot)
    (w : ℕ → ℤ) (s D : ℤ)
    (hc : ∀ j : Fin h → ℕ, (∀ r, slot r.val ≤ j r) →
      D ≤ ∑ r : Fin h, (2 * (j r : ℤ) * (h - 1 - r.val) + s * j r + w (j r)))
    (f : Fin h → Fin M) (hf : Function.Injective f) (σ : Equiv.Perm (Fin h)) :
    D ≤ ∑ r : Fin h, (((σ r).val : ℤ) * slot (f r).val +
      (slot (f r).val : ℤ) * (r.val + s) + w (slot (f r).val)) := by
  let τ := Tuple.sort f
  let j : Fin h → ℕ := fun r => slot (f (τ r)).val
  have hm := (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
  have hl (r : Fin h) : r.val ≤ (f (τ r)).val :=
    strictMono_fin_nat_lower _ (fun _ _ h => hm h) r
  have hj : Monotone (fun r => (j r : ℤ)) := by
    intro r t hrt
    change (slot (f (τ r)).val : ℤ) ≤ slot (f (τ t)).val
    exact_mod_cast hslot (show (f (τ r)).val ≤ (f (τ t)).val from Tuple.monotone_sort f hrt)
  have h1 := sortedNode_rearrangement (fun r => (j r : ℤ)) hj (τ.trans σ)
  have h2 := sortedNode_rearrangement (fun r => (j r : ℤ)) hj τ
  have hh := hc j (fun r => hslot (hl r))
  have he : (∑ r : Fin h, (((σ r).val : ℤ) * slot (f r).val +
      (slot (f r).val : ℤ) * (r.val + s) + w (slot (f r).val))) =
      ∑ r : Fin h, ((σ (τ r)).val * (j r : ℤ) + (j r : ℤ) * ((τ r).val + s) + w (j r)) :=
    (Equiv.sum_comp τ _).symm
  rw [he]
  simp only [Equiv.trans_apply] at h1
  simp only [mul_add, sum_add_distrib] at hh ⊢
  have heq : (∑ r : Fin h, 2 * (j r : ℤ) * (h - 1 - r.val)) =
      2 * ∑ r : Fin h, (j r : ℤ) * (h - 1 - r.val) := by
    rw [mul_sum]
    apply sum_congr rfl
    intros
    ring
  rw [heq] at hh
  have heq' : (∑ r : Fin h, s * (j r : ℤ)) = ∑ r : Fin h, (j r : ℤ) * s := by
    apply sum_congr rfl
    intros
    ring
  rw [heq'] at hh
  conv at h1 => rhs; arg 2; ext r; rw [mul_comm]
  omega

end
end Lambert
