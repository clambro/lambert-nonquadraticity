import Lambert.Arithmetic.IntegerMinimalPolynomial
import Lambert.Analysis.CubicLogDecay
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Algebraic degree exclusion from integer polynomial sequences

A nonzero integer resultant is bounded through one small distinguished value
and all remaining conjugates. Leading coefficients are retained explicitly.
-/
namespace Lambert
noncomputable section
open Polynomial Filter Topology
open scoped Classical

private theorem multiset_norm_prod_bound (t : Multiset ℂ) (p : ℂ[X]) (G : ℂ → ℝ)
    (hG : ∀ z, ‖p.eval z‖ ≤ Real.exp (G z)) :
    ‖(t.map p.eval).prod‖ ≤ Real.exp ((t.map G).sum) := by
  induction t using Multiset.induction_on with
  | empty => simp
  | @cons z t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, norm_mul, Real.exp_add]
    exact mul_le_mul (hG z) ih (norm_nonneg _) (Real.exp_pos _).le

private theorem multiset_cubic_limit (t : Multiset ℂ) (G : ℕ → ℂ → ℝ) (B : ℝ)
    (hG : ∀ z, Tendsto (fun n : ℕ => G n z / (n : ℝ)^3) atTop (𝓝 B)) :
    Tendsto (fun n : ℕ => ((t.map (G n)).sum) / (n : ℝ)^3) atTop (𝓝 ((t.card : ℝ)*B)) := by
  induction t using Multiset.induction_on with
  | empty => simp
  | @cons z t ih =>
    have he := (hG z).add ih
    simpa [Multiset.map_cons, Multiset.sum_cons, add_div, add_mul, add_comm] using he

/-- An integer polynomial irreducible over the rationals cannot vanish at a distinguished point when positive cubic resultant savings dominate all conjugate growth. -/
theorem integer_polynomial_not_root_of_cubic_bounds (P : ℕ → ℤ[X]) (d : ℕ → ℕ)
    (hd : ∀ n, (P n).natDegree ≤ d n)
    (hdlim : Tendsto (fun n : ℕ => (d n : ℝ)/(n : ℝ)^3) atTop (𝓝 0))
    (α : ℂ) (hne : ∀ n, (P n).eval₂ (Int.castRingHom ℂ) α ≠ 0)
    (A B : ℝ)
    (F : ℕ → ℝ)
    (hF : ∀ n, Real.log ‖(P n).eval₂ (Int.castRingHom ℂ) α‖ ≤ F n)
    (hsmall : Tendsto (fun n : ℕ => F n / (n : ℝ)^3) atTop (𝓝 A))
    (G : ℕ → ℂ → ℝ)
    (hG : ∀ n z, ‖(P n).eval₂ (Int.castRingHom ℂ) z‖ ≤ Real.exp (G n z))
    (hGlim : ∀ z, Tendsto (fun n : ℕ => G n z / (n : ℝ)^3) atTop (𝓝 B))
    (f : ℤ[X]) (hf : Irreducible (f.map (Int.castRingHom ℚ)))
    (hmargin : A + ((f.natDegree - 1 : ℕ) : ℝ) * B < 0) :
    f.eval₂ (Int.castRingHom ℂ) α ≠ 0 := by
  intro hroot
  let fc := f.map (Int.castRingHom ℂ)
  let pc := fun n => (P n).map (Int.castRingHom ℂ)
  have hf0 : f ≠ 0 := by intro he; simp [he] at hf
  have hiC : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hiQ : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have degC (p : ℤ[X]) := natDegree_map_eq_of_injective hiC p
  have degQ (p : ℤ[X]) := natDegree_map_eq_of_injective hiQ p
  have hfc0 : fc ≠ 0 := fun he => hf0 ((Polynomial.map_injective (Int.castRingHom ℂ) hiC) (by simpa using he))
  have hmem : α ∈ fc.roots := (mem_roots hfc0).mpr (by simpa [fc, IsRoot, eval_map] using hroot)
  let t := fc.roots.erase α
  have ht : fc.roots = α ::ₘ t := (Multiset.cons_erase hmem).symm
  have hcard : t.card = f.natDegree - 1 := by
    rw [Multiset.card_erase_of_mem hmem, ← (IsAlgClosed.splits fc).natDegree_eq_card_roots]
    exact congrArg (fun k => k - 1) (degC f)
  have hres (n : ℕ) : f.resultant (P n) ≠ 0 := by
    have hc : IsCoprime (f.map (Int.castRingHom ℚ)) ((P n).map (Int.castRingHom ℚ)) := by
      apply hf.coprime_iff_not_dvd.mpr
      rintro ⟨r, hr⟩
      have he := congrArg (fun p : ℚ[X] => p.eval₂ (Rat.castHom ℂ) α) hr
      simp only [eval₂_mul, eval₂_map] at he
      have hc : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by ext; simp
      rw [hc, hroot, zero_mul] at he
      exact hne n he
    have he := resultant_ne_zero _ _ hc
    simp only [degQ, resultant_map_map] at he
    intro hz
    apply he
    rw [hz, map_zero]
  have hlead : 1 ≤ ‖(f.leadingCoeff : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast (Int.one_le_abs (leadingCoeff_ne_zero.mpr hf0))
  let g : ℕ → ℝ := fun n => (d n : ℝ) * Real.log ‖(f.leadingCoeff : ℂ)‖ +
    F n + (t.map (G n)).sum
  have hg : Tendsto (fun n : ℕ => g n / (n : ℝ)^3) atTop
      (𝓝 (A + ((f.natDegree - 1 : ℕ) : ℝ)*B)) := by
    have he := ((hdlim.mul_const (Real.log ‖(f.leadingCoeff : ℂ)‖)).add hsmall).add
      (multiset_cubic_limit t G B hGlim)
    rw [hcard] at he
    simp only [zero_mul, zero_add] at he
    convert he using 1
    funext n
    dsimp [g]
    ring
  have hbound (n : ℕ) : 1 ≤ Real.exp (g n) := by
    have hr : ‖(f.resultant (P n) : ℂ)‖ =
        ‖(f.leadingCoeff : ℂ)‖ ^ (P n).natDegree *
          (‖(pc n).eval α‖ * ‖(t.map (pc n).eval).prod‖) := by
      change ‖(Int.castRingHom ℂ) (f.resultant (P n))‖ = _
      rw [← resultant_map_map f (P n) f.natDegree (P n).natDegree (Int.castRingHom ℂ)]
      have he := resultant_eq_prod_eval fc (pc n) (P n).natDegree natDegree_map_le (IsAlgClosed.splits fc)
      simp only [fc, degC] at he
      rw [he, ht, Multiset.map_cons, Multiset.prod_cons, norm_mul, norm_mul, norm_pow]
      rw [leadingCoeff_map_of_injective hiC]
      rfl
    have hi : 1 ≤ ‖(f.resultant (P n) : ℂ)‖ := by
      rw [Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs (hres n)
    apply hi.trans
    rw [hr]
    have hp := multiset_norm_prod_bound t (pc n) (G n) (fun z => by simpa [pc, eval_map] using hG n z)
    have hl := pow_le_pow_right₀ hlead (hd n)
    calc
      _ ≤ ‖(f.leadingCoeff : ℂ)‖ ^ d n *
          (‖(pc n).eval α‖ * Real.exp ((t.map (G n)).sum)) :=
        mul_le_mul hl (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) (by positivity) (by positivity)
      _ ≤ ‖(f.leadingCoeff : ℂ)‖ ^ d n *
          (Real.exp (F n) * Real.exp ((t.map (G n)).sum)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have hpos : 0 < ‖(pc n).eval α‖ := norm_pos_iff.mpr (by simpa [pc, eval_map] using hne n)
        calc
          _ = Real.exp (Real.log ‖(pc n).eval α‖) := (Real.exp_log hpos).symm
          _ ≤ _ := Real.exp_le_exp.mpr (by simpa [pc, eval_map] using hF n)
      _ = Real.exp (g n) := by
        dsimp [g]
        rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul,
          Real.exp_log (by linarith : 0 < ‖(f.leadingCoeff : ℂ)‖)]
        ring
  have hz := tendsto_zero_of_cubic_log_upper (fun n => Real.exp (g n)) g
    (fun n => Real.exp_pos _) (fun n => by rw [Real.log_exp]) hmargin hg
  have he := ge_of_tendsto hz (Filter.Eventually.of_forall hbound)
  norm_num at he


/-- Integer polynomial sequences with a positive resultant margin exclude every algebraic degree at most a prescribed bound. -/
theorem algebraic_degree_gt_of_cubic_bounds (P : ℕ → ℤ[X]) (d : ℕ → ℕ)
    (hd : ∀ n, (P n).natDegree ≤ d n)
    (hdlim : Tendsto (fun n : ℕ => (d n : ℝ)/(n : ℝ)^3) atTop (𝓝 0))
    (α : ℂ) (hne : ∀ n, (P n).eval₂ (Int.castRingHom ℂ) α ≠ 0)
    (A B : ℝ) (hB : 0 ≤ B)
    (F : ℕ → ℝ)
    (hF : ∀ n, Real.log ‖(P n).eval₂ (Int.castRingHom ℂ) α‖ ≤ F n)
    (hsmall : Tendsto (fun n : ℕ => F n / (n : ℝ)^3) atTop (𝓝 A))
    (G : ℕ → ℂ → ℝ)
    (hG : ∀ n z, ‖(P n).eval₂ (Int.castRingHom ℂ) z‖ ≤ Real.exp (G n z))
    (hGlim : ∀ z, Tendsto (fun n : ℕ => G n z / (n : ℝ)^3) atTop (𝓝 B))
    (e : ℕ) (hmargin : A + ((e - 1 : ℕ) : ℝ) * B < 0)
    (hα : IsAlgebraic ℚ α) : e < (minpoly ℚ α).natDegree := by
  by_contra! he
  obtain ⟨f, hf, hdg, hroot⟩ := exists_integer_minimal_polynomial α hα
  have hdg' : f.natDegree - 1 ≤ e - 1 := Nat.sub_le_sub_right (hdg.trans_le he) 1
  have hdgR : ((f.natDegree - 1 : ℕ) : ℝ) ≤ ((e - 1 : ℕ) : ℝ) := by
    exact_mod_cast hdg'
  have hm : A + ((f.natDegree - 1 : ℕ) : ℝ) * B < 0 :=
    (add_le_add_right (mul_le_mul_of_nonneg_right hdgR hB) A).trans_lt hmargin
  exact integer_polynomial_not_root_of_cubic_bounds P d hd hdlim α hne A B F hF hsmall G hG hGlim f hf hm hroot

end
end Lambert
