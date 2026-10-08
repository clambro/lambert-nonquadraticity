import Mathlib.NumberTheory.NumberField.ProductFormula

/-! # Finite-place bounds for integer bivariate polynomial evaluations -/
namespace Lambert
noncomputable section
open Polynomial Finset NumberField
open scoped BigOperators

/-- A nonarchimedean absolute value of a polynomial is bounded by its largest coefficient and the prescribed degree. -/
theorem polynomial_nonarchimedean_bound {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (p : R[X]) (x : K) (D : ℕ) (hD : p.natDegree ≤ D) (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ i, v (f (p.coeff i)) ≤ A) :
    v (p.eval₂ f x) ≤ A * max (v x) 1 ^ D := by
  classical
  rw [eval₂_eq_sum, Polynomial.sum]
  have hterm (i : ℕ) (hi : i ∈ p.support) :
      v (f (p.coeff i)*x^i) ≤ A*max (v x) 1 ^ D := by
    rw [map_mul, map_pow]
    apply mul_le_mul (hc i) ?_ (by positivity) hA
    exact (pow_le_pow_left₀ (by positivity) (le_max_left _ _) _).trans
      (pow_le_pow_right₀ (le_max_right _ _) ((le_natDegree_of_mem_supp i hi).trans hD))
  have hsum (s : Finset ℕ) (hs : s ⊆ p.support) :
      v (∑ i ∈ s, f (p.coeff i)*x^i) ≤ A*max (v x) 1 ^ D := by
    induction s using Finset.induction with
    | empty => simp only [sum_empty, map_zero]; positivity
    | @insert i s hi ih =>
      rw [sum_insert hi]
      exact (hv _ _).trans (max_le (hterm i (hs (mem_insert_self _ _)))
        (ih (fun j hj => hs (mem_insert_of_mem hj))))
  exact hsum _ (Subset.refl _)

/-- At finite places the integer bivariate evaluation costs only the two coordinate heights, with their separate degrees. -/
theorem integerBivariate_nonarchimedean_bound {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (p : (ℤ[X])[X])
    (q x : K) (D h : ℕ) (hh : p.natDegree ≤ h)
    (hD : ∀ i, (p.coeff i).natDegree ≤ D) :
    v ((p.map (eval₂RingHom (Int.castRingHom K) q)).eval x) ≤
      max (v q) 1 ^ D * max (v x) 1 ^ h := by
  rw [eval_map]
  apply polynomial_nonarchimedean_bound _ v hv p x h hh _ (by positivity)
  intro i
  change v ((p.coeff i).eval₂ (Int.castRingHom K) q) ≤ _
  simpa only [one_mul] using polynomial_nonarchimedean_bound (Int.castRingHom K) v hv
    (p.coeff i) q D (hD i) 1 zero_le_one (fun j => hv.apply_intCast_le_one)

/-- The finite-place denominator product of a number-field element. -/
def finitePlaceDenominator {K : Type*} [Field K] [NumberField K] (x : K) : ℝ :=
  ∏ᶠ v : FinitePlace K, max (v x) 1

/-- Only finitely many finite-place maximum factors differ from one. -/
theorem finitePlace_max_hasFiniteMulSupport {K : Type*} [Field K] [NumberField K] (x : K) :
    (fun v : FinitePlace K => max (v x) 1).HasFiniteMulSupport := by
  by_cases hx : x = 0
  · simp [hx, Function.HasFiniteMulSupport]
  · exact (FinitePlace.hasFiniteMulSupport hx).max (by fun_prop)

/-- Finite-place denominator products are at least one. -/
theorem one_le_finitePlaceDenominator {K : Type*} [Field K] [NumberField K] (x : K) :
    1 ≤ finitePlaceDenominator x := one_le_finprod (fun _ => le_max_right _ _)

/-- The finite part of the product formula for a bivariate evaluation is bounded by the coordinate denominator products. -/
theorem integerBivariate_finitePlace_product_bound {K : Type*} [Field K] [NumberField K]
    (p : (ℤ[X])[X]) (q x : K) (D h : ℕ) (hh : p.natDegree ≤ h)
    (hD : ∀ i, (p.coeff i).natDegree ≤ D)
    (hn : ((p.map (eval₂RingHom (Int.castRingHom K) q)).eval x) ≠ 0) :
    (∏ᶠ v : FinitePlace K, v ((p.map (eval₂RingHom (Int.castRingHom K) q)).eval x)) ≤
      finitePlaceDenominator q ^ D * finitePlaceDenominator x ^ h := by
  have hq := finitePlace_max_hasFiniteMulSupport q
  have hx := finitePlace_max_hasFiniteMulSupport x
  rw [finitePlaceDenominator, finitePlaceDenominator, finprod_pow hq, finprod_pow hx,
    ← finprod_mul_distrib (hq.fun_pow D) (hx.fun_pow h)]
  apply finprod_le_finprod (FinitePlace.hasFiniteMulSupport hn) (fun _ => by positivity)
    ((hq.fun_pow D).mul (hx.fun_pow h))
  intro v
  exact integerBivariate_nonarchimedean_bound v.val (FinitePlace.add_le v) p q x D h hh hD
end
end Lambert
