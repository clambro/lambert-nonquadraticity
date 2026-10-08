import Lambert.Determinants.Moments
namespace Lambert
noncomputable section
open Polynomial Finset
open scoped Classical
variable {K F : Type*} [Field K] [Field F]

/-- The full nodal Lambert functional commutes with coefficient embeddings. -/
theorem lambertNumeratorFunctional_map (f : K →+* F) (q : K) (k L : ℕ) (p : K[X]) :
    (lambertNumeratorFunctional q k L p).map f =
      lambertNumeratorFunctional (f q) k L (p.map f) := by
  have hn : (Lagrange.nodal univ (fun j : Fin L => q ^ (k+j.val))).map f =
      Lagrange.nodal univ (fun j : Fin L => f q ^ (k+j.val)) := by
    simp [Lagrange.nodal, Polynomial.map_prod]
  have hd := Polynomial.map_divByMonic (p := p) f
    (Lagrange.nodal_monic (s := univ) (v := fun j : Fin L => q ^ (k+j.val)))
  rw [hn] at hd
  simp only [lambertNumeratorFunctional, LinearMap.smul_apply, nodalFunctional_apply,
    smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_add,
    Polynomial.map_sum, lambertPolynomialFunctional_map, hd]
  simp only [map_pow, map_neg, map_one]
  congr 1
  congr 1
  apply sum_congr rfl
  intro j _
  simp only [Polynomial.map_C, Polynomial.map_neg,
    Polynomial.map_sub, Polynomial.map_X, map_mul]
  have hw : f (Lagrange.nodalWeight univ (fun v : Fin L => q ^ (k+v.val)) j) =
      Lagrange.nodalWeight univ (fun v : Fin L => f q ^ (k+v.val)) j := by
    simp [Lagrange.nodalWeight]
  have hp : f (p.eval (q ^ (k+j.val))) = (p.map f).eval (f q ^ (k+j.val)) := by
    rw [← map_pow, Polynomial.eval_map_apply]
  rw [hw, hp]
  congr 2
  simp [geometricMomentPrefix]

/-- Every Lambert moment commutes with coefficient embeddings. -/
theorem lambertPoleMoment_map (f : K →+* F) (q : K) (k L r : ℕ) :
    (lambertPoleMoment q k L r).map f = lambertPoleMoment (f q) k L r := by
  simp only [lambertPoleMoment, lambertNumeratorFunctional_map, Polynomial.map_pow, Polynomial.map_X]

/-- Every shifted Lambert determinant commutes with coefficient embeddings. -/
theorem lambertPoleDeterminant_map (f : K →+* F) (q : K) (h k L s : ℕ) :
    (lambertPoleDeterminant q h k L s).map f = lambertPoleDeterminant (f q) h k L s := by
  unfold lambertPoleDeterminant
  refine ((Polynomial.mapRingHom f).map_det _).trans ?_
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  exact lambertPoleMoment_map f q k L _

end
end Lambert
