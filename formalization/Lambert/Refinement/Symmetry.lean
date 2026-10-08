import Lambert.Refinement.Moments
import Lambert.Arithmetic.NodalRestriction

/-! # Exchanging the numerator prefix and the pole offset -/
namespace Lambert
noncomputable section
open Polynomial Matrix Finset
open scoped Classical
variable {K : Type*} [Field K]

/-- Cancelling a prefix of the pole denominator gives the functional on the remaining geometric window. -/
theorem lambertNumeratorFunctional_prefix_mul (q : K) (b D : ℕ)
    (hq : Function.Injective (fun i : ℕ => q ^ i)) (p : K[X]) :
    lambertNumeratorFunctional q 0 (b + D)
      (lambertPoleDenominator q 0 b * p) =
        lambertNumeratorFunctional q b D p := by
  let x : Fin D → K := fun j => q ^ (b + j.val)
  let y : Fin (b + D) → K := fun j => q ^ j.val
  let R := Lagrange.nodal univ (fun j : Fin b => q ^ j.val)
  have hx : Function.Injective x := by
    intro i j hij
    exact Fin.ext (Nat.add_left_cancel (hq hij))
  have hy : Function.Injective y := by
    intro i j hij
    exact Fin.ext (hq hij)
  have hR : R * Lagrange.nodal univ x = Lagrange.nodal univ y := by
    simp only [R, x, y, Lagrange.nodal, Fin.prod_univ_add, Fin.val_castAdd, Fin.val_natAdd]
  have he := nodalFunctional_restrict x y (Fin.natAdd b) hx hy (fun _ => rfl)
    R hR (lambertPolynomialFunctional q)
    (fun j => -(X - C (geometricMomentPrefix q j.val))) p
  simp only [lambertNumeratorFunctional, lambertPoleDenominator,
    Nat.zero_add, smul_mul_assoc, map_smul, LinearMap.smul_apply]
  change (-1 : K) ^ b • ((-1 : K) ^ (b + D) •
    nodalFunctional y (lambertPolynomialFunctional q)
      (fun j => -(X - C (geometricMomentPrefix q j.val))) (R * p)) = _
  rw [he, smul_smul]
  have hs : (-1 : K) ^ b * (-1 : K) ^ (b + D) = (-1 : K) ^ D := by
    rw [pow_add]
    calc
      _ = ((-1 : K) ^ b * (-1 : K) ^ b) * (-1 : K) ^ D := by ring
      _ = _ := by rw [← mul_pow]; simp
  rw [hs]
  rfl

/-- Exchanging the numerator prefix and the pole offset preserves the weighted Lambert functional. -/
theorem lambertNumeratorFunctional_prefix_swap (q : K) (A b c : ℕ)
    (hAc : A ≤ c) (hbc : b ≤ c) (hq : Function.Injective (fun i : ℕ => q ^ i))
    (p : K[X]) :
    lambertNumeratorFunctional q b (c - b) (lambertPoleDenominator q 0 A * p) =
      lambertNumeratorFunctional q A (c - A) (lambertPoleDenominator q 0 b * p) := by
  rw [← lambertNumeratorFunctional_prefix_mul q b (c - b) hq,
    ← lambertNumeratorFunctional_prefix_mul q A (c - A) hq,
    Nat.add_sub_of_le hbc, Nat.add_sub_of_le hAc]
  congr 1
  ring

/-- The numerator-weighted determinant is unchanged when its numerator prefix and pole offset are exchanged. -/
theorem lambertRefinementDeterminant_prefix_swap (q : K) (h A b c s : ℕ)
    (hAc : A ≤ c) (hbc : b ≤ c) (hq : Function.Injective (fun i : ℕ => q ^ i)) :
    lambertRefinementDeterminant q h A b (c - b) s =
      lambertRefinementDeterminant q h b A (c - A) s := by
  unfold lambertRefinementDeterminant
  congr 1
  apply Matrix.ext
  intro i j
  exact lambertNumeratorFunctional_prefix_swap q A b c hAc hbc hq _

end
end Lambert
