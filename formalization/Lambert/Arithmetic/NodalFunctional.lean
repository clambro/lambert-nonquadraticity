import Lambert.Arithmetic.CauchyDeterminant
import Mathlib.Tactic.LinearCombination

/-!
# Linear functionals on rational functions with prescribed simple poles

A numerator represents a rational function with the fixed monic nodal denominator.
Polynomial division and Lagrange residues extend a polynomial functional to this
space. No value is assigned to rational functions with other poles.
-/

namespace Lambert

open Polynomial Finset

noncomputable section

variable {K : Type*} [Field K]

/-- Division by a fixed monic polynomial is linear in the numerator. -/
def monicQuotientLinear (D : K[X]) (hD : D.Monic) : K[X] →ₗ[K] K[X] where
  toFun p := p /ₘ D
  map_add' p r := by
    apply mul_left_cancel₀ hD.ne_zero
    have hp := modByMonic_add_div p D
    have hr := modByMonic_add_div r D
    have hs := modByMonic_add_div (p + r) D
    rw [add_modByMonic] at hs
    linear_combination hs - hp - hr
  map_smul' c p := by
    refine (div_modByMonic_unique (c • (p /ₘ D)) (c • (p %ₘ D)) hD ?_).1
    constructor
    · simpa only [mul_smul_comm, ← smul_add] using
        congrArg (fun r : K[X] => c • r) (modByMonic_add_div p D)
    · exact (degree_smul_le c _).trans_lt (degree_modByMonic_lt p hD)

/-- The extension to a fixed nodal denominator combines the polynomial quotient
with the prescribed values at its simple poles. -/
def nodalFunctional {M : Type*} [AddCommGroup M] [Module K M]
    {n : ℕ} (x : Fin n → K) (μ : K[X] →ₗ[K] M) (w : Fin n → M) : K[X] →ₗ[K] M :=
  μ.comp (monicQuotientLinear (Lagrange.nodal univ x) Lagrange.nodal_monic) +
    ∑ j : Fin n, (LinearMap.toSpanSingleton K M (w j)).comp
      ((Lagrange.nodalWeight univ x j) • Polynomial.leval (x j))

/-- The nodal extension has the explicit quotient and residue formula. -/
theorem nodalFunctional_apply {M : Type*} [AddCommGroup M] [Module K M]
    {n : ℕ} (x : Fin n → K) (μ : K[X] →ₗ[K] M) (w : Fin n → M) (p : K[X]) :
    nodalFunctional x μ w p = μ (p /ₘ Lagrange.nodal univ x) +
      ∑ j, (Lagrange.nodalWeight univ x j * p.eval (x j)) • w j := by
  simp [nodalFunctional, monicQuotientLinear, LinearMap.toSpanSingleton_apply]

/-- A numerator divisible by the nodal denominator retains its polynomial value. -/
theorem nodalFunctional_nodal_mul {M : Type*} [AddCommGroup M] [Module K M]
    {n : ℕ} (x : Fin n → K) (μ : K[X] →ₗ[K] M) (w : Fin n → M) (p : K[X]) :
    nodalFunctional x μ w (Lagrange.nodal univ x * p) = μ p := by
  rw [nodalFunctional_apply, mul_divByMonic_cancel_left p Lagrange.nodal_monic]
  simp [eval_mul, Lagrange.eval_nodal_at_node (mem_univ _)]

/-- At distinct nodes, the complementary numerator has its prescribed simple-pole value. -/
theorem nodalFunctional_complementary {M : Type*} [AddCommGroup M] [Module K M]
    {n : ℕ} (x : Fin n → K) (hx : Function.Injective x)
    (μ : K[X] →ₗ[K] M) (w : Fin n → M) (j : Fin n) :
    nodalFunctional x μ w (complementaryNodal x j) = w j := by
  rw [nodalFunctional_apply,
    (divByMonic_eq_zero_iff Lagrange.nodal_monic).mpr
      (by simpa using degree_complementaryNodal_lt x j), map_zero, zero_add]
  rw [sum_eq_single j]
  · have hn : (complementaryNodal x j).eval (x j) ≠ 0 := by
      apply Lagrange.eval_nodal_not_at_node
      intro k hk
      exact hx.ne (mem_erase.mp hk).1.symm
    rw [Lagrange.nodalWeight_eq_eval_nodal_erase_inv]
    change (((complementaryNodal x j).eval (x j))⁻¹ *
      (complementaryNodal x j).eval (x j)) • w j = w j
    rw [inv_mul_cancel₀ hn, one_smul]
  · intro k _ hkj
    have hz : (complementaryNodal x j).eval (x k) = 0 :=
      Lagrange.eval_nodal_at_node (by simp [hkj])
    rw [hz, mul_zero, zero_smul]
  · simp

/-- Every polynomial numerator is the sum of its nodal quotient and Lagrange residues. -/
theorem nodal_numerator_decomposition {n : ℕ} (x : Fin n → K)
    (hx : Function.Injective x) (p : K[X]) :
    p = Lagrange.nodal univ x * (p /ₘ Lagrange.nodal univ x) +
      ∑ j, (Lagrange.nodalWeight univ x j * p.eval (x j)) •
        complementaryNodal x j := by
  have hi := Lagrange.eq_interpolate hx.injOn
    (show (p %ₘ Lagrange.nodal univ x).degree < (univ : Finset (Fin n)).card by
      simpa using degree_modByMonic_lt p (Lagrange.nodal_monic (s := univ) (v := x)))
  have he (j : Fin n) : (p %ₘ Lagrange.nodal univ x).eval (x j) = p.eval (x j) := by
    exact eval₂_modByMonic_eq_self_of_root (by
      simpa using Lagrange.eval_nodal_at_node (v := x) (mem_univ j))
  simp only [Lagrange.interpolate_apply, he] at hi
  have hb (j : Fin n) : Lagrange.basis univ x j =
      (Lagrange.nodalWeight univ x j) • complementaryNodal x j := by
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (mem_univ j),
      ← Lagrange.nodal_erase_eq_nodal_div (mem_univ j)]
    exact (smul_eq_C_mul _).symm
  calc
    p = p %ₘ Lagrange.nodal univ x +
        Lagrange.nodal univ x * (p /ₘ Lagrange.nodal univ x) :=
      (modByMonic_add_div p _).symm
    _ = _ := by
      rw [hi, add_comm]
      congr 1
      apply sum_congr rfl
      intro j _
      rw [hb]
      simp only [smul_eq_C_mul, map_mul]
      ring

end

end Lambert
