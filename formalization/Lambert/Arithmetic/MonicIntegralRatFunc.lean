import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Integer presentations with monic polynomial denominators

A rational function represented by integer polynomials with monic denominator
cannot acquire fractional coefficients when its poles are cleared. The original
presentation is essential: absence of poles alone only gives a rational polynomial.
-/

namespace Lambert
noncomputable section
open Polynomial

/-- The embedding of integer polynomials into rational functions over the rationals. -/
def integerPolynomialRatFunc : ℤ[X] →+* RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

/-- Integer polynomial embedding is injective. -/
theorem integerPolynomialRatFunc_injective : Function.Injective integerPolynomialRatFunc :=
  (RatFunc.algebraMap_injective ℚ).comp
    (Polynomial.map_injective _ (Int.cast_injective))

/-- Rational functions admitting integer numerators and monic integer denominators
form a subring. -/
def monicIntegralRatFunc : Subring (RatFunc ℚ) where
  carrier := {f | ∃ N D : ℤ[X], D.Monic ∧ f = integerPolynomialRatFunc N /
    integerPolynomialRatFunc D}
  zero_mem' := ⟨0, 1, monic_one, by simp⟩
  one_mem' := ⟨1, 1, monic_one, by simp⟩
  neg_mem' := by
    rintro f ⟨N, D, hD, rfl⟩
    exact ⟨-N, D, hD, by simp [neg_div]⟩
  add_mem' := by
    rintro f g ⟨N, D, hD, rfl⟩ ⟨M, E, hE, rfl⟩
    have hd : integerPolynomialRatFunc D ≠ 0 :=
      fun h => hD.ne_zero (integerPolynomialRatFunc_injective (by simpa using h))
    have he : integerPolynomialRatFunc E ≠ 0 :=
      fun h => hE.ne_zero (integerPolynomialRatFunc_injective (by simpa using h))
    refine ⟨N * E + M * D, D * E, hD.mul hE, ?_⟩
    simp only [map_add, map_mul]
    simpa only [mul_comm] using (div_add_div (integerPolynomialRatFunc N) (integerPolynomialRatFunc M) hd he)
  mul_mem' := by
    rintro f g ⟨N, D, hD, rfl⟩ ⟨M, E, hE, rfl⟩
    exact ⟨N * M, D * E, hD.mul hE, by simp only [map_mul, div_mul_div_comm]⟩

/-- Every integer polynomial has a monic-denominator presentation. -/
theorem integerPolynomialRatFunc_mem (N : ℤ[X]) :
    integerPolynomialRatFunc N ∈ monicIntegralRatFunc :=
  ⟨N, 1, monic_one, by simp⟩

/-- The inverse of a monic integer polynomial has an integer monic-denominator presentation. -/
theorem integerPolynomialRatFunc_inv_mem {D : ℤ[X]} (hD : D.Monic) :
    (integerPolynomialRatFunc D)⁻¹ ∈ monicIntegralRatFunc :=
  ⟨1, D, hD, by simp⟩

/-- A polynomial rational function with an integer monic-denominator presentation
has integer coefficients. -/
theorem monicIntegralRatFunc_polynomial {p : ℚ[X]}
    (hp : algebraMap ℚ[X] (RatFunc ℚ) p ∈ monicIntegralRatFunc) :
    ∃ P : ℤ[X], P.map (Int.castRingHom ℚ) = p := by
  obtain ⟨N, D, hD, he⟩ := hp
  have hd : integerPolynomialRatFunc D ≠ 0 :=
    fun h => hD.ne_zero (integerPolynomialRatFunc_injective (by simpa using h))
  have hm : p * D.map (Int.castRingHom ℚ) = N.map (Int.castRingHom ℚ) := by
    apply RatFunc.algebraMap_injective ℚ
    simpa only [map_mul, integerPolynomialRatFunc, RingHom.comp_apply,
      Polynomial.coe_mapRingHom] using (eq_div_iff hd).mp he
  have hv : D ∣ N := (Polynomial.map_dvd_map (Int.castRingHom ℚ)
    Int.cast_injective hD).mp ⟨p, by rw [mul_comm]; exact hm.symm⟩
  obtain ⟨P, hP⟩ := hv
  refine ⟨P, ?_⟩
  have hd' : D.map (Int.castRingHom ℚ) ≠ 0 := (hD.map _).ne_zero
  apply mul_right_cancel₀ hd'
  rw [hm, hP, Polynomial.map_mul, mul_comm]

/-- Clearing the reduced denominator of a monic-integral rational function by an
integer polynomial produces an integer polynomial, without a constant denominator. -/
theorem monicIntegralRatFunc_clear {f : RatFunc ℚ} (hf : f ∈ monicIntegralRatFunc)
    (T : ℤ[X]) (hT : T ≠ 0)
    (hd : f.denom ∣ T.map (Int.castRingHom ℚ)) :
    ∃ P : ℤ[X], integerPolynomialRatFunc P = integerPolynomialRatFunc T * f := by
  have ht : T.map (Int.castRingHom ℚ) ≠ 0 := by
    exact fun h => hT ((Polynomial.map_injective _ Int.cast_injective) (by simpa using h))
  obtain ⟨p, hp⟩ := (RatFunc.denom_dvd ht).mp hd
  have he : algebraMap ℚ[X] (RatFunc ℚ) p = integerPolynomialRatFunc T * f := by
    rw [hp]
    exact (mul_div_cancel₀ _ (fun h => ht ((RatFunc.algebraMap_injective ℚ)
      (by simpa [integerPolynomialRatFunc] using h)))).symm
  obtain ⟨P, hP⟩ := monicIntegralRatFunc_polynomial
    (he ▸ monicIntegralRatFunc.mul_mem (integerPolynomialRatFunc_mem T) hf)
  exact ⟨P, by simpa only [integerPolynomialRatFunc, RingHom.comp_apply,
    Polynomial.coe_mapRingHom, hP] using he⟩

end
end Lambert
