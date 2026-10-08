import Lambert.Refinement.Transport

/-! # Six coefficient bounds for the selected rectangular Lambert family -/
namespace Lambert
noncomputable section
open scoped Classical WithZero

/-- Six equivalent numerator presentations give six signed pole bounds for the same rank-500N certificate. -/
def lambertRefinementOrbitExponent (N n : ℕ) (j : Fin 6) : ℤ :=
  let h := 500 * N
  let t := lambertRefinementTransportOrder h 0 (16 * N) n
  let u := lambertRefinementTransportOrder h (27 * N) (43 * N) n
  let v := lambertRefinementTransportOrder h (41 * N) (25 * N) n
  ![lambertRefinementCyclotomicExponent h 0 (27 * N) (16 * N) (41 * N) n,
    lambertRefinementCyclotomicExponent h (16 * N) (41 * N) 0 (27 * N) n - t,
    lambertRefinementCyclotomicExponent h (41 * N) (43 * N) (25 * N) 0 n - u,
    lambertRefinementCyclotomicExponent h 0 (25 * N) (16 * N) (43 * N) n - v - u,
    lambertRefinementCyclotomicExponent h (16 * N) (43 * N) 0 (25 * N) n - u - v - t,
    lambertRefinementCyclotomicExponent h (25 * N) (27 * N) (41 * N) (16 * N) n - v - t] j

/-- Each of the six transported bounds applies to every coefficient of the original rectangular determinant. -/
theorem lambertRefinementOrbit_coeff_valuation_le {K : Type*} [Field K] [Algebra ℚ K]
    (ζ : K) (N n i : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (j : Fin 6) :
    Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ)
        (500 * N) (27 * N) (516 * N) (41 * N)).coeff i)) ≤
      WithZero.exp (lambertRefinementOrbitExponent N n j) := by
  have base (A b d s : ℕ) (hab : A ≤ b) :=
    lambertRefinementDeterminant_coeff_valuation_le ζ (500 * N) (A * N) (b * N)
      (d * N) (s * N) n i (Nat.mul_le_mul_right N hab) hn hζ
  have tr (A b d s : ℕ) (E : ℤ) :=
    lambertRefinementDeterminant_coeff_valuation_le_of_transpose ζ (500 * N) (A * N)
      (b * N) (d * N) (s * N) n i hn hζ E
  have sw (A b d s : ℕ) (ha : A ≤ b + d) (E : ℤ) :=
    lambertRefinementDeterminant_coeff_valuation_le_of_swap ζ (500 * N) (A * N)
      (b * N) (d * N) (s * N) n i (by simpa only [Nat.add_mul] using Nat.mul_le_mul_right N ha) hn hζ E
  norm_num only [Nat.zero_mul, ← Nat.add_mul, ← Nat.sub_mul, Nat.reduceAdd, Nat.reduceSub] at base tr sw
  have b0 := base 0 27 16 41 (by decide)
  have b1 := tr 0 27 16 41 _ (base 16 41 0 27 (by decide))
  have b2 := sw 0 27 16 41 (by decide) _
    (tr 27 0 43 41 _ (sw 43 41 27 0 (by decide) _ (base 41 43 25 0 (by decide))))
  have b3 := sw 0 27 16 41 (by decide) _
    (tr 27 0 43 41 _ (sw 43 41 27 0 (by decide) _
      (tr 41 43 25 0 _ (sw 25 0 41 43 (by decide) _ (base 0 25 16 43 (by decide))))))
  have b5 := tr 0 27 16 41 _ (sw 16 41 0 27 (by decide) _
    (tr 41 16 25 27 _ (base 25 27 41 16 (by decide))))
  have b4 := tr 0 27 16 41 _ (sw 16 41 0 27 (by decide) _
    (tr 41 16 25 27 _ (sw 25 27 41 16 (by decide) _
      (tr 27 25 43 16 _ (sw 43 16 27 25 (by decide) _ (base 16 43 0 25 (by decide)))))))
  fin_cases j
  · simpa [lambertRefinementOrbitExponent, lambertRefinementDeterminant_zero] using b0
  · simpa [lambertRefinementOrbitExponent, lambertRefinementDeterminant_zero] using b1
  · simpa [lambertRefinementOrbitExponent, lambertRefinementDeterminant_zero] using b2
  · simpa [lambertRefinementOrbitExponent, lambertRefinementDeterminant_zero] using b3
  · simpa [lambertRefinementOrbitExponent, lambertRefinementDeterminant_zero] using b4
  · simpa [lambertRefinementOrbitExponent, lambertRefinementDeterminant_zero] using b5

/-- The clearing exponent is the nonnegative part of the best of the six transported coefficient bounds. -/
def lambertRefinementClearingExponent (N n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 6)).inf' Finset.univ_nonempty (lambertRefinementOrbitExponent N n)).toNat

/-- Taking the minimum of the six presentations gives a coefficientwise clearing bound. -/
theorem lambertRefinementFamily_coeff_valuation_le {K : Type*} [Field K] [Algebra ℚ K]
    (ζ : K) (N n i : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    Valued.v (lambertLocalMap ζ (hζ.ne_zero hn.ne')
      ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ)
        (500 * N) (27 * N) (516 * N) (41 * N)).coeff i)) ≤
      WithZero.exp (lambertRefinementClearingExponent N n : ℤ) := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin 6)))
    Finset.univ_nonempty (lambertRefinementOrbitExponent N n)
  apply (lambertRefinementOrbit_coeff_valuation_le ζ N n i hn hζ j).trans
  apply WithZero.exp_le_exp.mpr
  unfold lambertRefinementClearingExponent
  rw [hj]
  exact Int.self_le_toNat _

/-- Root orders beyond the original pole and moment windows need no cyclotomic clearing. -/
theorem lambertRefinementClearingExponent_eq_zero (N n : ℕ) (hn : 543 * N ≤ n) :
    lambertRefinementClearingExponent N n = 0 := by
  have hv : (∑ r ∈ Finset.range (516 * N), (516 * N - (r + 1) * n)) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    have he := Nat.mul_le_mul_right n (show 1 ≤ r + 1 by omega)
    omega
  have hf : (∑ r ∈ Finset.range (516 * N), (516 * N - 2 * n * (r + 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    have he := Nat.mul_le_mul_left (2 * n) (show 1 ≤ r + 1 by omega)
    omega
  have hr : lambertRectangularResidualCount (500 * N) (16 * N) (41 * N) n = 0 := by
    unfold lambertRectangularResidualCount
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro r _
    have := r.isLt
    simp only [not_and]
    omega
  have hz : lambertRefinementOrbitExponent N n 0 = 0 := by
    simp [lambertRefinementOrbitExponent, lambertRefinementCyclotomicExponent,
      lambertRefinementLocalOrder, show 500 * N + 16 * N = 516 * N by omega,
      hv, hf, hr, show max (27 * N) n = n by omega, show 27 * N + 516 * N - n = 0 by omega]
  have he : (Finset.univ : Finset (Fin 6)).inf' Finset.univ_nonempty
      (lambertRefinementOrbitExponent N n) ≤ 0 := by
    rw [← hz]
    exact Finset.inf'_le _ (Finset.mem_univ 0)
  exact Int.toNat_eq_zero.mpr he

end
end Lambert
