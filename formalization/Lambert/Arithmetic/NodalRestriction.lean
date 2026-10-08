import Lambert.Arithmetic.NodalFunctional

/-! # Restricting nodal functionals by cancelling denominator factors -/
namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical
variable {K : Type*} [Field K]

/-- Cancelling a complementary denominator restricts a nodal functional to its remaining nodes. -/
theorem nodalFunctional_restrict {M : Type*} [AddCommGroup M] [Module K M]
    {m n : ℕ} (x : Fin m → K) (y : Fin n → K) (e : Fin m → Fin n)
    (hx : Function.Injective x) (hy : Function.Injective y) (he : ∀ i, y (e i) = x i)
    (R : K[X]) (hR : R * Lagrange.nodal univ x = Lagrange.nodal univ y)
    (μ : K[X] →ₗ[K] M) (w : Fin n → M) (p : K[X]) :
    nodalFunctional y μ w (R * p) = nodalFunctional x μ (fun i => w (e i)) p := by
  have hc (i : Fin m) : R * complementaryNodal x i = complementaryNodal y (e i) := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero (x i))
    calc
      (X - C (x i)) * (R * complementaryNodal x i) =
          R * ((X - C (x i)) * complementaryNodal x i) := by ring
      _ = R * Lagrange.nodal univ x := by
        rw [Lagrange.nodal_eq_mul_nodal_erase (mem_univ i)]
        rfl
      _ = Lagrange.nodal univ y := hR
      _ = (X - C (x i)) * complementaryNodal y (e i) := by
        rw [Lagrange.nodal_eq_mul_nodal_erase (mem_univ (e i)), he]
        rfl
  conv_lhs => rw [nodal_numerator_decomposition x hx p]
  simp only [mul_add, ← mul_assoc, hR, mul_sum, mul_smul_comm, hc, map_add,
    map_sum, map_smul, nodalFunctional_nodal_mul, nodalFunctional_complementary y hy]
  rw [nodalFunctional_apply]

end
end Lambert
