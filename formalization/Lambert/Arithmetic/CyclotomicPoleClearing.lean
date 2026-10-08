import Lambert.Arithmetic.RatFuncPoleSupport
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-! # Exact clearing from zero and cyclotomic pole bounds -/
namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical

/-- A rational function supported at zero and roots of unity has denominator dividing the product prescribed by its local pole bounds and their cutoff. -/
theorem ratFunc_denom_dvd_cyclotomic_clearing (f : RatFunc ℚ) (A N : ℕ) (E : ℕ → ℕ)
    (hsupport : ∀ p : ℚ[X], Irreducible p → p ∣ f.denom →
      Associated p X ∨ ∃ n : ℕ, 0<n ∧ Associated p (cyclotomic n ℚ))
    (hzero : ∀ e, (X : ℚ[X])^e ∣ f.denom → e≤A)
    (hcyclo : ∀ n e, 0<n → cyclotomic n ℚ^e ∣ f.denom → e≤E n)
    (hcut : ∀ n, 0<n → N≤n → E n=0) :
    f.denom ∣ X^A * ∏ n ∈ Ico 1 N, cyclotomic n ℚ^E n := by
  apply (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le f.denom_ne_zero).mpr
  intro p hp
  apply ENat.forall_natCast_le_iff_le.mp
  intro e he
  rw [← pow_dvd_iff_le_emultiplicity] at he ⊢
  by_cases he0 : e=0
  · simp [he0]
  have hpd : p ∣ f.denom := (dvd_pow_self p he0).trans he
  rcases hsupport p hp.irreducible hpd with hx | ⟨n,hn,hc⟩
  · have hex := (hx.pow_pow (n := e)).dvd_iff_dvd_left.mp he
    exact ((hx.pow_pow (n := e)).dvd.trans (pow_dvd_pow X (hzero e hex))).trans (dvd_mul_right _ _)
  · have hec := (hc.pow_pow (n := e)).dvd_iff_dvd_left.mp he
    have heb := hcyclo n e hn hec
    have hnh : n<N := by
      by_contra hh
      rw [hcut n hn (Nat.le_of_not_gt hh)] at heb
      exact he0 (Nat.eq_zero_of_le_zero heb)
    exact ((hc.pow_pow (n := e)).dvd.trans (pow_dvd_pow _ heb)).trans
      ((dvd_prod_of_mem (fun n => cyclotomic n ℚ^E n)
        (mem_Ico.mpr ⟨hn,hnh⟩)).trans (dvd_mul_left _ _))

end
end Lambert
