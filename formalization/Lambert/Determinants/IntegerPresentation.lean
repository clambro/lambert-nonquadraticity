import Lambert.Arithmetic.MonicIntegralRatFunc
import Lambert.Determinants.Determinant

/-!
# Monic integer presentations of Lambert determinant coefficients

The augmented determinant identity gives an integer numerator and monic integer
denominator for every coefficient, before the sharper local bounds are applied.
-/

namespace Lambert
noncomputable section
open Polynomial Matrix Finset

section CoefficientRing
variable (S : Subring (RatFunc ℚ))
private abbrev P := Polynomial.liftsRing S.subtype

private theorem C_mem {f : RatFunc ℚ} (hf : f ∈ S) : C f ∈ P S :=
  Polynomial.C_mem_lifts S.subtype ⟨f, hf⟩

variable (hq : (RatFunc.X : RatFunc ℚ) ∈ S)
  (hr : ∀ n : ℕ, (1 / ((RatFunc.X : RatFunc ℚ) ^ (n + 1) - 1)) ∈ S)
  (hd : ∀ i j : ℕ, i < j → (((RatFunc.X : RatFunc ℚ) ^ j - RatFunc.X ^ i)⁻¹) ∈ S)

include hr in
private theorem prefix_mem (n : ℕ) :
    geometricMomentPrefix (RatFunc.X : RatFunc ℚ) n ∈ S :=
  S.sum_mem fun i _ => hr i

include hq hr in
/-- A coefficient subring containing the formal base and reciprocal moments
contains every simple-pole entry polynomial. -/
theorem lambertPoleEntry_mem_lifts (i j : ℕ) :
    lambertPoleEntry (RatFunc.X : RatFunc ℚ) i j ∈ P S := by
  induction i with
  | zero => exact (P S).sub_mem (Polynomial.X_mem_lifts S.subtype) (C_mem S (prefix_mem S hr j))
  | succ i ih =>
    exact (P S).sub_mem ((P S).mul_mem (C_mem S (S.pow_mem hq j)) ih) (C_mem S (hr i))

include hq hr in
private theorem augmented_mem (h k d s : ℕ) :
    (lambertAugmentedMatrix (RatFunc.X : RatFunc ℚ) h k d s).det ∈ P S := by
  have hm (i j : Fin (h + d)) : lambertAugmentedMatrix (RatFunc.X : RatFunc ℚ) h k d s i j ∈ P S := by
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simpa only [lambertAugmentedMatrix, Fin.addCases_left] using lambertPoleEntry_mem_lifts S hq hr (r.val + s) (k+j.val)
    · simpa only [lambertAugmentedMatrix, Fin.addCases_right] using C_mem S (S.pow_mem hq ((k+j.val) * r.val))
  let A : Matrix (Fin (h + d)) (Fin (h + d)) (P S) := fun i j => ⟨_, hm i j⟩
  have he := (P S).subtype.map_det A
  exact he ▸ (A.det).property

include hd in
private theorem vandermonde_inv_mem (k L : ℕ) :
    ((vandermonde (fun j : Fin L => (RatFunc.X : RatFunc ℚ) ^ (k+j.val))).det)⁻¹ ∈ S := by
  rw [det_vandermonde]
  simp only [← Finset.prod_inv_distrib]
  apply S.prod_mem
  intro i _
  apply S.prod_mem
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  exact hd (k+i.val) (k+j.val) (by omega)

include hq hr hd in
/-- A coefficient subring containing the formal base, reciprocal moments, and
inverse node differences contains every Lambert determinant coefficient. -/
theorem lambertPoleDeterminant_coeff_mem_subring (h k d s a : ℕ) :
    (lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s).coeff a ∈ S := by
  let ε : RatFunc ℚ := (lambertAugmentedSign h d : ℤ)
  let V := (vandermonde (fun j : Fin (h + d) => (RatFunc.X : RatFunc ℚ) ^ (k+j.val))).det
  have hε : ε * ε = 1 := by
    have he := congrArg (Int.castRingHom (RatFunc ℚ)) (lambertAugmentedSign_sq h d)
    simpa [ε, pow_two] using he
  have hV : V ≠ 0 := by
    apply det_vandermonde_ne_zero_iff.mpr
    intro i j he
    exact Fin.ext (Nat.add_left_cancel (ratFunc_X_pow_injective he))
  have he := congrArg (fun p : (RatFunc ℚ)[X] => p.coeff a)
    (lambertAugmentedMatrix_det_formal h k d s)
  rw [coeff_C_mul] at he
  have hc : (lambertAugmentedMatrix (RatFunc.X : RatFunc ℚ) h k d s).det.coeff a ∈ S := by
    obtain ⟨p, hp⟩ := (Polynomial.mem_lifts (f := S.subtype) _).mp (augmented_mem S hq hr h k d s)
    rw [← hp, coeff_map]
    exact (p.coeff a).property
  have heq : (lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s).coeff a =
      ε * V⁻¹ * (lambertAugmentedMatrix (RatFunc.X : RatFunc ℚ) h k d s).det.coeff a := by
    rw [he]
    change _ = ε * V⁻¹ * (ε * V * _)
    rw [show ε * V⁻¹ * (ε * V * (lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s).coeff a) =
      (ε * ε) * (V⁻¹ * V) * (lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s).coeff a by ring]
    rw [hε, inv_mul_cancel₀ hV, one_mul, one_mul]
  rw [heq]
  exact S.mul_mem (S.mul_mem (by exact_mod_cast (intCast_mem S (lambertAugmentedSign h d))) (vandermonde_inv_mem S hd k _)) hc

end CoefficientRing

/-- Every coefficient of every augmented-window Lambert determinant has an
integer polynomial numerator and a monic integer polynomial denominator. -/
theorem lambertPoleDeterminant_coeff_monicIntegral (h k d s a : ℕ) :
    (lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s).coeff a ∈
      monicIntegralRatFunc := by
  apply lambertPoleDeterminant_coeff_mem_subring monicIntegralRatFunc
  · simpa [integerPolynomialRatFunc] using integerPolynomialRatFunc_mem (X : ℤ[X])
  · intro n
    simpa [integerPolynomialRatFunc, one_div] using integerPolynomialRatFunc_inv_mem
      (monic_X_pow_sub_C (1 : ℤ) (Nat.succ_ne_zero n))
  · intro i j hij
    have hm : (X ^ j - X ^ i : ℤ[X]).Monic :=
      monic_X_pow_sub (by rw [degree_X_pow]; exact_mod_cast hij)
    simpa [integerPolynomialRatFunc] using integerPolynomialRatFunc_inv_mem hm

end
end Lambert
