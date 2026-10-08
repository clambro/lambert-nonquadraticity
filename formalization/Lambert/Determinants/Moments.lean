import Lambert.Determinants.MomentData

/-! # Lambert moments on movable pole windows -/
namespace Lambert
open Polynomial Finset
noncomputable section
variable {K : Type*} [Field K]

/-- The positive pole denominator is the product of the factors `q^(k+j)-t`
in a finite geometric window. -/
def lambertPoleDenominator (q : K) (k L : ℕ) : K[X] :=
  (-1 : K) ^ L • Lagrange.nodal univ (fun j : Fin L => q ^ (k + j.val))

/-- The signed monic form of the pole denominator equals the positive-factor product. -/
theorem lambertPoleDenominator_eq_prod (q : K) (k L : ℕ) :
    lambertPoleDenominator q k L = ∏ j : Fin L, (C (q ^ (k + j.val)) - X) := by
  simp only [lambertPoleDenominator, Lagrange.nodal, smul_eq_C_mul, map_pow, map_neg,
    map_one]
  conv_rhs =>
    arg 2
    ext j
    rw [show C q ^ (k + j.val) - X = -(X - C q ^ (k + j.val)) by ring]
  rw [prod_neg, card_univ, Fintype.card_fin]

/-- The finite-window Lambert functional evaluates numerators over the positive
pole denominator by polynomial division and prescribed simple-pole values. -/
def lambertNumeratorFunctional (q : K) (k L : ℕ) : K[X] →ₗ[K] K[X] :=
  (-1 : K) ^ L • nodalFunctional (fun j : Fin L => q ^ (k + j.val))
    (lambertPolynomialFunctional q)
    (fun j => -(X - C (geometricMomentPrefix q (k + j.val))))

/-- The Lambert moment of degree `r` uses the indicated finite pole denominator. -/
def lambertPoleMoment (q : K) (k L r : ℕ) : K[X] :=
  lambertNumeratorFunctional q k L (X ^ r)

/-- The shifted Lambert determinant is the Gram-shaped determinant of the
finite-window moments, still polynomial in the unknown value. -/
def lambertPoleDeterminant (q : K) (h k L s : ℕ) : K[X] :=
  (Matrix.of fun i j : Fin h => lambertPoleMoment q k L (i.val + j.val + s)).det

/-- Multiplying a numerator by the monic nodal denominator leaves only its
polynomial moment, with the positive-denominator sign. -/
theorem lambertNumeratorFunctional_nodal_mul (q : K) (k L : ℕ) (p : K[X]) :
    lambertNumeratorFunctional q k L
      (Lagrange.nodal univ (fun j : Fin L => q ^ (k + j.val)) * p) =
        (-1 : K) ^ L • lambertPolynomialFunctional q p := by
  simp only [lambertNumeratorFunctional, LinearMap.smul_apply,
    nodalFunctional_nodal_mul]

/-- Complementary nodal numerators realize the simple-pole recurrence at
every moment index when the geometric nodes are distinct. -/
theorem lambertNumeratorFunctional_complementary (q : K) (k L : ℕ)
    (hq : Function.Injective (fun j : Fin L => q ^ (k + j.val))) (i : ℕ) (j : Fin L) :
    lambertNumeratorFunctional q k L (X ^ i * complementaryNodal (fun v : Fin L => q ^ (k + v.val)) j) =
      (-1 : K) ^ (L + 1) • lambertPoleEntry q i (k + j.val) := by
  induction i with
  | zero =>
    simp only [pow_zero, one_mul, lambertNumeratorFunctional, LinearMap.smul_apply,
      nodalFunctional_complementary _ hq, lambertPoleEntry_zero, pow_succ,
      smul_eq_C_mul, map_mul, map_neg, map_one]
    ring
  | succ i ih =>
    have he : (X : K[X]) ^ (i + 1) * complementaryNodal (fun v : Fin L => q ^ (k + v.val)) j =
        q ^ (k + j.val) • (X ^ i * complementaryNodal (fun v : Fin L => q ^ (k + v.val)) j) +
        Lagrange.nodal univ (fun v : Fin L => q ^ (k + v.val)) * X ^ i := by
      rw [Lagrange.nodal_eq_mul_nodal_erase (mem_univ j)]
      simp only [complementaryNodal, smul_eq_C_mul, pow_succ]
      ring
    rw [he, map_add, map_smul, ih, lambertNumeratorFunctional_nodal_mul,
      lambertPolynomialFunctional_X_pow, lambertPoleEntry_succ]
    simp only [pow_succ, smul_eq_C_mul, map_mul, map_neg, map_one]
    ring

/-- Every finite-window moment is affine in the unknown Lambert value. -/
theorem lambertPoleMoment_affine (q : K) (k L r : ℕ) :
    ∃ a b : K, lambertPoleMoment q k L r = X * C a + C b := by
  let x : Fin L → K := fun j => q ^ (k + j.val)
  let p : K[X] := X ^ r
  let a : K := (-1) ^ L * (-∑ j, Lagrange.nodalWeight univ x j * p.eval (x j))
  let b : K := (-1) ^ L *
    ((p /ₘ Lagrange.nodal univ x).sum (fun r c => c * (1 / (q ^ (r + 1) - 1))) +
      ∑ j, Lagrange.nodalWeight univ x j * p.eval (x j) * geometricMomentPrefix q (k + j.val))
  refine ⟨a, b, ?_⟩
  simp only [lambertPoleMoment, lambertNumeratorFunctional, LinearMap.smul_apply,
    nodalFunctional_apply, lambertPolynomialFunctional_eq_C, smul_eq_C_mul]
  dsimp [a, b, p, x]
  simp only [map_mul, map_neg, map_sum, map_add, mul_neg, neg_sub,
    mul_sub, sum_sub_distrib, ← sum_mul]
  ring

/-- The shifted determinant has degree at most its matrix size in the unknown value. -/
theorem lambertPoleDeterminant_natDegree_le (q : K) (h k L s : ℕ) :
    (lambertPoleDeterminant q h k L s).natDegree ≤ h := by
  classical
  choose a b hab using fun i j : Fin h =>
    lambertPoleMoment_affine q k L (i.val + j.val + s)
  have he : (Matrix.of fun i j : Fin h => lambertPoleMoment q k L (i.val + j.val + s)) =
      (X : K[X]) • (Matrix.of a).map C + (Matrix.of b).map C := by
    apply Matrix.ext
    intro i j
    exact hab i j
  unfold lambertPoleDeterminant
  rw [he]
  simpa using Polynomial.natDegree_det_X_add_C_le (Matrix.of a) (Matrix.of b)

end
end Lambert
