import Mathlib.LinearAlgebra.Lagrange

/-!
# Recovering coefficient bounds from constant evaluations

Interpolation over the scalar field transfers membership in any scalar
submodule from sufficiently many evaluations to every coefficient.
-/

namespace Lambert

noncomputable section

open Polynomial Finset
open scoped Classical

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Lagrange basis polynomials commute with field embeddings. -/
theorem lagrangeBasis_map {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (v : ι → K) (i : ι) :
    (Lagrange.basis s v i).map (algebraMap K L) =
      Lagrange.basis s (fun j => algebraMap K L (v j)) i := by
  simp [Lagrange.basis, Lagrange.basisDivisor, Polynomial.map_prod]

/-- If a polynomial takes values in a scalar submodule at sufficiently many
distinct scalar points, each of its coefficients belongs to that submodule. -/
theorem polynomial_coeff_mem_of_eval_mem {ι : Type*} [DecidableEq ι]
    (U : Submodule K L) (p : L[X]) (s : Finset ι) (v : ι → K)
    (hv : Set.InjOn v s) (hp : p.degree < s.card)
    (he : ∀ i ∈ s, p.eval (algebraMap K L (v i)) ∈ U) (k : ℕ) :
    p.coeff k ∈ U := by
  have hinj : Set.InjOn (fun i => algebraMap K L (v i)) s :=
    (algebraMap K L).injective.comp_injOn hv
  have hi := Lagrange.eq_interpolate hinj hp
  have hc := congrArg (fun q : L[X] => q.coeff k) hi
  rw [Lagrange.interpolate_apply, finsetSum_coeff] at hc
  rw [hc]
  apply U.sum_mem
  intro i hi
  rw [coeff_C_mul, ← lagrangeBasis_map, coeff_map]
  rw [mul_comm, ← Algebra.smul_def]
  exact U.smul_mem _ (he i hi)

/-- Over an infinite scalar field, membership of every constant evaluation
in a scalar submodule forces membership of every coefficient. -/
theorem polynomial_coeff_mem_of_forall_eval_mem [Infinite K]
    (U : Submodule K L) (p : L[X])
    (he : ∀ x : K, p.eval (algebraMap K L x) ∈ U) (k : ℕ) :
    p.coeff k ∈ U := by
  obtain ⟨s, hs⟩ := Set.Infinite.exists_subset_card_eq (Set.infinite_univ : Set.Infinite (Set.univ : Set K))
    (p.natDegree + 1)
  apply polynomial_coeff_mem_of_eval_mem U p s id Function.injective_id.injOn
  · rw [hs.2]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self p.natDegree)
  · intro i _
    exact he i

end

end Lambert
