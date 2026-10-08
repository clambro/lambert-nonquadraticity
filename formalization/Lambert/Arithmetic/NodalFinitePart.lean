import Lambert.Arithmetic.NodalFunctional
import Mathlib.RingTheory.LaurentSeries

/-!
# Finite parts over a monic nodal denominator

The finite part is linear in the numerator. Polynomial division and simple-pole
residues give its exact evaluation at every node, including the omitted self pole.
-/

namespace Lambert

noncomputable section
open Polynomial Finset
open scoped Classical
variable {K : Type*} [Field K] {n : ℕ}

/-- The finite part of a numerator over a monic nodal denominator retains the
first numerator derivative and the complementary denominator derivative. -/
def nodalFinitePart (x : Fin n → K) (j : Fin n) : K[X] →ₗ[K] K :=
  ((complementaryNodal x j).eval (x j))⁻¹ •
      ((Polynomial.leval (x j)).comp (Polynomial.derivative : K[X] →ₗ[K] K[X])) -
    ((complementaryNodal x j).derivative.eval (x j) /
      (complementaryNodal x j).eval (x j) ^ 2) • Polynomial.leval (x j)

/-- The nodal finite part has the rational quotient derivative formula. -/
theorem nodalFinitePart_apply (x : Fin n → K) (j : Fin n) (p : K[X]) :
    nodalFinitePart x j p =
      p.derivative.eval (x j) / (complementaryNodal x j).eval (x j) -
        p.eval (x j) * (complementaryNodal x j).derivative.eval (x j) /
          (complementaryNodal x j).eval (x j) ^ 2 := by
  simp only [nodalFinitePart, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Polynomial.leval_apply, smul_eq_mul]
  ring

private theorem complement_eval_ne_zero (x : Fin n → K) (hx : Function.Injective x) (j : Fin n) :
    (complementaryNodal x j).eval (x j) ≠ 0 := by
  apply Lagrange.eval_nodal_not_at_node
  intro k hk
  exact hx.ne (mem_erase.mp hk).1.symm

private theorem nodal_factor (x : Fin n → K) (j : Fin n) :
    Lagrange.nodal univ x = (X - C (x j)) * complementaryNodal x j :=
  Lagrange.nodal_eq_mul_nodal_erase (mem_univ j)

/-- A numerator divisible by the denominator has its ordinary polynomial
value as its finite part. -/
theorem nodalFinitePart_nodal_mul (x : Fin n → K) (hx : Function.Injective x)
    (j : Fin n) (p : K[X]) :
    nodalFinitePart x j (Lagrange.nodal univ x * p) = p.eval (x j) := by
  rw [nodalFinitePart_apply, nodal_factor x j]
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self,
    zero_mul, add_zero, one_mul, zero_div, sub_zero]
  exact mul_div_cancel_left₀ _ (complement_eval_ne_zero x hx j)

/-- The finite part of the self simple pole is zero. -/
theorem nodalFinitePart_complementary_self (x : Fin n → K) (j : Fin n) :
    nodalFinitePart x j (complementaryNodal x j) = 0 := by
  rw [nodalFinitePart_apply]
  by_cases hd : (complementaryNodal x j).eval (x j) = 0
  · simp [hd]
  · field_simp
    ring

/-- At a different node a simple pole has its ordinary reciprocal value. -/
theorem nodalFinitePart_complementary_ne (x : Fin n → K) (hx : Function.Injective x)
    (j k : Fin n) (hjk : j ≠ k) :
    nodalFinitePart x j (complementaryNodal x k) = 1 / (x j - x k) := by
  have hz : (complementaryNodal x k).eval (x j) = 0 :=
    Lagrange.eval_nodal_at_node (by simp [hjk])
  have hd := congrArg (fun p : K[X] => p.derivative.eval (x j))
    ((nodal_factor x j).symm.trans (nodal_factor x k))
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self,
    zero_mul, add_zero, one_mul, hz, zero_add] at hd
  rw [nodalFinitePart_apply, hz, zero_mul, zero_div, sub_zero]
  have hD := complement_eval_ne_zero x hx j
  have hdiff : x j - x k ≠ 0 := sub_ne_zero.mpr (hx.ne hjk)
  apply (div_eq_div_iff hD hdiff).mpr
  simpa only [one_mul, mul_comm] using hd.symm

/-- Polynomial division and residues reconstruct the finite part at a node,
with the self-pole summand omitted. -/
theorem nodalFinitePart_decomposition (x : Fin n → K) (hx : Function.Injective x)
    (j : Fin n) (p : K[X]) :
    nodalFinitePart x j p = (p /ₘ Lagrange.nodal univ x).eval (x j) +
      ∑ k, (Lagrange.nodalWeight univ x k * p.eval (x k)) *
        (if j = k then 0 else 1 / (x j - x k)) := by
  conv_lhs => rw [nodal_numerator_decomposition x hx p]
  rw [map_add, map_sum, nodalFinitePart_nodal_mul x hx]
  congr 1
  apply sum_congr rfl
  intro k _
  rw [map_smul, smul_eq_mul]
  by_cases hjk : j = k
  · subst k
    rw [if_pos rfl, nodalFinitePart_complementary_self]
  · rw [if_neg hjk, nodalFinitePart_complementary_ne x hx j k hjk]

/-- The finite value of a nodal rational function uses ordinary evaluation
away from its poles and omits the self simple-pole term at a node. -/
def nodalFiniteValue (x : Fin n → K) (a : K) : K[X] →ₗ[K] K :=
  nodalFunctional x (Polynomial.leval a)
    (fun j => if a = x j then 0 else 1 / (a - x j))

/-- The nodal finite value has its quotient and simple-pole residue expansion. -/
theorem nodalFiniteValue_apply (x : Fin n → K) (a : K) (p : K[X]) :
    nodalFiniteValue x a p = (p /ₘ Lagrange.nodal univ x).eval a +
      ∑ j, (Lagrange.nodalWeight univ x j * p.eval (x j)) *
        (if a = x j then 0 else 1 / (a - x j)) := by
  simp only [nodalFiniteValue, nodalFunctional_apply, Polynomial.leval_apply, smul_eq_mul]

/-- At a node the finite value is the constant Laurent coefficient. -/
theorem nodalFiniteValue_at_node (x : Fin n → K) (hx : Function.Injective x)
    (j : Fin n) (p : K[X]) :
    nodalFiniteValue x (x j) p = nodalFinitePart x j p := by
  rw [nodalFiniteValue_apply, nodalFinitePart_decomposition x hx]
  simp only [hx.eq_iff]

/-- Away from all nodes, the finite value is ordinary rational evaluation. -/
theorem nodalFiniteValue_regular (x : Fin n → K) (hx : Function.Injective x)
    (a : K) (ha : ∀ j, a ≠ x j) (p : K[X]) :
    nodalFiniteValue x a p = p.eval a / (Lagrange.nodal univ x).eval a := by
  have hN : (Lagrange.nodal univ x).eval a ≠ 0 :=
    Lagrange.eval_nodal_not_at_node (fun j _ => ha j)
  apply (eq_div_iff hN).mpr
  rw [nodalFiniteValue_apply, add_mul, sum_mul]
  have he := congrArg (Polynomial.eval a) (nodal_numerator_decomposition x hx p)
  simp only [eval_add, eval_mul, eval_finsetSum, eval_smul, smul_eq_mul] at he
  rw [he]
  congr 1
  · ring
  · apply sum_congr rfl
    intro j _
    rw [if_neg (ha j), nodal_factor x j, eval_mul, eval_sub, eval_X, eval_C]
    field_simp [sub_ne_zero.mpr (ha j)]

end
end Lambert
