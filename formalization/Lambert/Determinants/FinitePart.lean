import Lambert.Determinants.FinitePartLimit
namespace Lambert
noncomputable section
open Polynomial Finset Filter
open scoped Classical Topology
variable {K : Type*} [Field K]

/-- The truncated monic nodal functional sums finite parts and subtracts
its common residue correction. -/
def lambertTruncatedNodal (q Z : K) (k L N : ℕ) : K[X] →ₗ[K] K :=
  -(∑ m ∈ range N, (q ^ m) • nodalFiniteValue (fun j : Fin L => q ^ (k+j.val)) (q ^ m)) -
    Z • (∑ j : Fin L, Lagrange.nodalWeight univ (fun v : Fin L => q ^ (k+v.val)) j •
      Polynomial.leval (q ^ (k+j.val)))

/-- The finite-part truncation extends its polynomial truncation with the
exact finite simple-pole values. -/
theorem lambertTruncatedNodal_eq (q Z : K) (k L N : ℕ)
    (hq : Function.Injective (fun m : ℕ => q ^ m)) (p : K[X]) :
    lambertTruncatedNodal q Z k L N p =
      nodalFunctional (fun j : Fin L => q ^ (k+j.val)) (lambertTruncatedPolynomial q N)
        (fun j => -lambertFinitePoleSum q N (k+j.val) - Z) p := by
  have ht (j : Fin L) (c : K) :
      (∑ m ∈ range N, q ^ m * (c * (if q ^ m = q ^ (k+j.val) then 0 else 1 / (q ^ m - q ^ (k+j.val))))) =
        c * lambertFinitePoleSum q N (k+j.val) := by
    rw [lambertFinitePoleSum, mul_neg, mul_sum, ← sum_neg_distrib]
    apply sum_congr rfl
    intro m _
    by_cases hm : m = k+j.val
    · rw [hm]
      simp
    · rw [if_neg (hq.ne hm), if_neg hm, ← neg_sub (q ^ (k+j.val)), div_neg]
      ring
  simp only [lambertTruncatedNodal, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, Polynomial.leval_apply, smul_eq_mul,
    nodalFiniteValue_apply, nodalFunctional_apply, lambertTruncatedPolynomial_apply]
  simp only [mul_add, sum_add_distrib, mul_sum]
  rw [sum_comm]
  simp_rw [ht, mul_sub, mul_neg, sum_sub_distrib, sum_neg_distrib]
  simp only [mul_comm Z]
  ring

/-- Finite nodal finite-part sums converge to the exact monic Lambert functional
for every numerator, with no assumed analytic identification. -/
theorem lambertTruncatedNodal_tendsto (z : LaurentSeries K) (k L : ℕ) (p : (LaurentSeries K)[X]) :
    Tendsto (fun N => lambertTruncatedNodal (lambertZeroBase K)
      (z + lambertPositivePrefix (lambertZeroBase K) N) k L N p) atTop
      (𝓝 (nodalFunctional (fun j : Fin L => lambertZeroBase K ^ (k+j.val))
        ((Polynomial.leval z).comp (lambertPolynomialFunctional (lambertZeroBase K)))
        (fun j => -(z - geometricMomentPrefix (lambertZeroBase K) (k+j.val))) p)) := by
  simp_rw [lambertTruncatedNodal_eq _ _ _ _ _ lambertZeroBase_pow_injective,
    nodalFunctional_apply, smul_eq_mul, LinearMap.comp_apply, Polynomial.leval_apply]
  apply (lambertTruncatedPolynomial_tendsto z _).add
  apply tendsto_finsetSum
  intro j _
  exact tendsto_const_nhds.mul (lambertTruncatedPole_tendsto z (k+j.val))

end
end Lambert
