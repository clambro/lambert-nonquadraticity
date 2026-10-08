import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Polynomial finite sums

Faulhaber's formula supplies polynomial antiderivatives for sums along natural
indices, with the degree increase retained explicitly.
-/

namespace Lambert

noncomputable section

open Polynomial Finset

/-- The power-sum polynomial evaluates to the sum of the indicated powers
strictly below its natural argument. -/
def powerSumPolynomial (d : ℕ) : ℚ[X] :=
  C ((d + 1 : ℚ)⁻¹) * (Polynomial.bernoulli (d + 1) - C (_root_.bernoulli (d + 1)))

/-- Power-sum polynomials evaluate to the exact finite power sum. -/
theorem powerSumPolynomial_eval (d m : ℕ) :
    (powerSumPolynomial d).eval (m : ℚ) = ∑ k ∈ range m, (k : ℚ) ^ d := by
  have he := Polynomial.sum_range_pow_eq_bernoulli_sub m d
  simp only [powerSumPolynomial, eval_mul, eval_C, eval_sub]
  rw [← he, inv_mul_cancel_left₀ (by positivity : (d + 1 : ℚ) ≠ 0)]

/-- The degree of the power-sum polynomial is at most one more than the power. -/
theorem powerSumPolynomial_natDegree_le (d : ℕ) :
    (powerSumPolynomial d).natDegree ≤ d + 1 := by
  have hb : (Polynomial.bernoulli (d + 1)).natDegree ≤ d + 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [Polynomial.coeff_bernoulli, if_neg (by omega)]
  exact (natDegree_mul_le).trans (by
    simpa only [natDegree_C, zero_add] using
      (natDegree_sub_le _ _).trans (max_le hb (by simp)))

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The polynomial prefix sum integrates each monomial by its power-sum polynomial. -/
def polynomialPrefixSum (p : K[X]) : K[X] :=
  ∑ d ∈ p.support, C (p.coeff d) * (powerSumPolynomial d).map (algebraMap ℚ K)

/-- Evaluating a polynomial prefix sum at a natural number equals the sum of
the original polynomial at every smaller natural number. -/
theorem polynomialPrefixSum_eval (p : K[X]) (m : ℕ) :
    (polynomialPrefixSum p).eval (m : K) = ∑ k ∈ range m, p.eval (k : K) := by
  have hs (d : ℕ) : ((powerSumPolynomial d).map (algebraMap ℚ K)).eval (m : K) =
      ∑ k ∈ range m, (k : K) ^ d := by
    rw [show (m : K) = algebraMap ℚ K (m : ℚ) by simp, eval_map_apply,
      powerSumPolynomial_eval, map_sum]
    simp only [map_pow, map_natCast]
  simp only [polynomialPrefixSum, eval_finsetSum, eval_mul, eval_C, hs, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  exact (Polynomial.eval_eq_sum (p := p) (x := (k : K))).symm

/-- Taking a polynomial prefix sum increases the degree by at most one. -/
theorem polynomialPrefixSum_natDegree_le (p : K[X]) :
    (polynomialPrefixSum p).natDegree ≤ p.natDegree + 1 := by
  apply natDegree_sum_le_of_forall_le
  intro d hd
  calc
    (C (p.coeff d) * (powerSumPolynomial d).map (algebraMap ℚ K)).natDegree ≤
        ((powerSumPolynomial d).map (algebraMap ℚ K)).natDegree := by
      simpa only [natDegree_C, zero_add] using (natDegree_mul_le
        (p := C (p.coeff d)) (q := (powerSumPolynomial d).map (algebraMap ℚ K)))
    _ ≤ (powerSumPolynomial d).natDegree := natDegree_map_le
    _ ≤ d + 1 := powerSumPolynomial_natDegree_le d
    _ ≤ p.natDegree + 1 := Nat.add_le_add_right (le_natDegree_of_mem_supp d hd) 1

end

end Lambert
