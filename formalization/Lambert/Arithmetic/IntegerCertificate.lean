import Lambert.Arithmetic.MonicIntegralRatFunc
import Lambert.Arithmetic.RatFuncInfinity
import Lambert.Arithmetic.IntegerHomogeneous
import Mathlib.Algebra.Polynomial.OfFn

/-! # Exact assembly of cleared bivariate integer certificates -/
namespace Lambert
noncomputable section
open Polynomial
open scoped Classical

/-- An integer lift of a rational-function coefficient multiplied by a specified clearing polynomial. -/
def clearedIntegerCoefficient (P : (RatFunc ℚ)[X]) (D : ℤ[X])
    (hlift : ∀ i, ∃ c : ℤ[X], integerPolynomialRatFunc c=integerPolynomialRatFunc D * P.coeff i)
    (i : ℕ) : ℤ[X] := (hlift i).choose

/-- Each chosen integer coefficient represents its prescribed cleared rational function exactly. -/
theorem clearedIntegerCoefficient_spec (P : (RatFunc ℚ)[X]) (D : ℤ[X])
    (hlift : ∀ i, ∃ c : ℤ[X], integerPolynomialRatFunc c=integerPolynomialRatFunc D * P.coeff i)
    (i : ℕ) : integerPolynomialRatFunc (clearedIntegerCoefficient P D hlift i) =
      integerPolynomialRatFunc D * P.coeff i := (hlift i).choose_spec

/-- Boundedness at infinity bounds an integral cleared coefficient by the degree of the nonzero clearing polynomial. -/
theorem clearedIntegerCoefficient_natDegree_le (P : (RatFunc ℚ)[X]) (D : ℤ[X])
    (hlift : ∀ i, ∃ c : ℤ[X], integerPolynomialRatFunc c=integerPolynomialRatFunc D * P.coeff i)
    (hD : D ≠ 0) (i : ℕ) (hinfty : RatFunc.inftyValuation ℚ (P.coeff i) ≤ 1) :
    (clearedIntegerCoefficient P D hlift i).natDegree ≤ D.natDegree := by
  have he := ratFunc_cleared_natDegree_le hinfty
    (show D.map (Int.castRingHom ℚ) ≠ 0 from
      fun hz => hD ((Polynomial.map_injective _ Int.cast_injective) (hz.trans (Polynomial.map_zero _).symm)))
    (clearedIntegerCoefficient_spec P D hlift i)
  simpa only [Polynomial.coe_mapRingHom,
    Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective] using he

/-- The bivariate integer certificate assembles the cleared coefficients through a prescribed outer-degree bound. -/
def clearedIntegerPolynomial (P : (RatFunc ℚ)[X]) (D : ℤ[X])
    (hlift : ∀ i, ∃ c : ℤ[X], integerPolynomialRatFunc c=integerPolynomialRatFunc D * P.coeff i)
    (h : ℕ) : (ℤ[X])[X] := ofFn (h+1) (fun i => clearedIntegerCoefficient P D hlift i.val)

/-- The assembled integer certificate has outer degree at most its cutoff. -/
theorem clearedIntegerPolynomial_natDegree_le (P : (RatFunc ℚ)[X]) (D : ℤ[X])
    (hlift : ∀ i, ∃ c : ℤ[X], integerPolynomialRatFunc c=integerPolynomialRatFunc D * P.coeff i)
    (h : ℕ) : (clearedIntegerPolynomial P D hlift h).natDegree ≤ h :=
  Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)

/-- Mapping an assembled integer certificate into rational functions recovers the exact prescribed clearing of its source polynomial. -/
theorem clearedIntegerPolynomial_map (P : (RatFunc ℚ)[X]) (D : ℤ[X])
    (hlift : ∀ i, ∃ c : ℤ[X], integerPolynomialRatFunc c=integerPolynomialRatFunc D * P.coeff i)
    (h : ℕ) (hP : P.natDegree ≤ h) :
    (clearedIntegerPolynomial P D hlift h).map integerPolynomialRatFunc =
      C (integerPolynomialRatFunc D)*P := by
  ext i
  rw [coeff_map, coeff_C_mul]
  by_cases hi : i<h+1
  · rw [clearedIntegerPolynomial, ofFn_coeff_eq_val_of_lt _ hi]
    exact clearedIntegerCoefficient_spec P D hlift i
  · rw [clearedIntegerPolynomial, ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi), map_zero,
      coeff_eq_zero_of_natDegree_lt (hP.trans_lt (by omega)), mul_zero]

/-- Homogenizing every chosen coefficient at the clearing degree gives the rational-coordinate integer certificate. -/
def clearedSpecializedIntegerPolynomial (P : (RatFunc ℚ)[X]) (D : ℤ[X])
    (hlift : ∀ i, ∃ c : ℤ[X], integerPolynomialRatFunc c=integerPolynomialRatFunc D * P.coeff i)
    (h : ℕ) (a b : ℤ) : ℤ[X] := ofFn (h+1) (fun i =>
      MvPolynomial.eval ![a,b] ((clearedIntegerCoefficient P D hlift i.val).homogenize D.natDegree))

/-- Homogeneous integer specialization retains the prescribed outer-degree bound. -/
theorem clearedSpecializedIntegerPolynomial_natDegree_le (P : (RatFunc ℚ)[X]) (D : ℤ[X])
    (hlift : ∀ i, ∃ c : ℤ[X], integerPolynomialRatFunc c=integerPolynomialRatFunc D * P.coeff i)
    (h : ℕ) (a b : ℤ) : (clearedSpecializedIntegerPolynomial P D hlift h a b).natDegree ≤ h :=
  Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)

/-- Each homogeneous specialized coefficient equals its rational evaluation times the common denominator power. -/
theorem clearedSpecializedIntegerPolynomial_coeff (P : (RatFunc ℚ)[X]) (D : ℤ[X])
    (hlift : ∀ i, ∃ c : ℤ[X], integerPolynomialRatFunc c=integerPolynomialRatFunc D * P.coeff i)
    (h i : ℕ) (hi : i ≤ h) (hdeg : (clearedIntegerCoefficient P D hlift i).natDegree ≤ D.natDegree)
    (a b : ℤ) (hb : b ≠ 0) :
    ((clearedSpecializedIntegerPolynomial P D hlift h a b).coeff i : ℚ) =
      ((clearedIntegerCoefficient P D hlift i).map (Int.castRingHom ℚ)).eval ((a : ℚ)/b)*(b : ℚ)^D.natDegree := by
  rw [clearedSpecializedIntegerPolynomial, ofFn_coeff_eq_val_of_lt _ (by omega)]
  exact integerPolynomial_homogeneous_eval _ _ hdeg a b hb

/-- A homogeneous integer coefficient equals the clearing value times the specialized rational-function coefficient, provided that clearing value is nonzero. -/
theorem clearedSpecializedIntegerPolynomial_coeff_eval
    (P : (RatFunc ℚ)[X]) (D : ℤ[X])
    (hlift : ∀ i, ∃ c : ℤ[X], integerPolynomialRatFunc c=integerPolynomialRatFunc D * P.coeff i)
    (h i : ℕ) (hi : i ≤ h)
    (hdeg : (clearedIntegerCoefficient P D hlift i).natDegree ≤ D.natDegree)
    (hdiv : (P.coeff i).denom ∣ D.map (Int.castRingHom ℚ))
    (a b : ℤ) (hb : b ≠ 0)
    (hD : (D.map (Int.castRingHom ℚ)).eval ((a : ℚ)/b) ≠ 0) :
    ((clearedSpecializedIntegerPolynomial P D hlift h a b).coeff i : ℚ) =
      ((D.map (Int.castRingHom ℚ)).eval ((a : ℚ)/b)*(b : ℚ)^D.natDegree) *
        RatFunc.eval (RingHom.id ℚ) ((a : ℚ)/b) (P.coeff i) := by
  let q : ℚ := (a : ℚ)/b
  have hf : (P.coeff i).denom.eval₂ (RingHom.id ℚ) q ≠ 0 := by
    intro hz
    apply hD
    simpa only [eval₂_id] using
      Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℚ) q hdiv hz
  have he := congrArg (RatFunc.eval (RingHom.id ℚ) q)
    (clearedIntegerCoefficient_spec P D hlift i)
  have hpoly : (integerPolynomialRatFunc D).denom.eval₂ (RingHom.id ℚ) q ≠ 0 := by
    simp [integerPolynomialRatFunc]
  rw [RatFunc.eval_mul (RingHom.id ℚ) q hpoly hf] at he
  simp only [integerPolynomialRatFunc, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    RatFunc.eval_algebraMap, Algebra.algebraMap_self, RingHom.id_apply, eval₂_id] at he
  rw [clearedSpecializedIntegerPolynomial_coeff P D hlift h i hi hdeg a b hb, he]
  ring

/-- Exact coefficient specialization of a rational-function polynomial determines the whole homogeneous integer certificate, including its clearing scale. -/
theorem clearedSpecializedIntegerPolynomial_map
    (P : (RatFunc ℚ)[X]) (D : ℤ[X])
    (hlift : ∀ i, ∃ c : ℤ[X], integerPolynomialRatFunc c=integerPolynomialRatFunc D * P.coeff i)
    (h : ℕ) (hP : P.natDegree ≤ h)
    (hdeg : ∀ i, (clearedIntegerCoefficient P D hlift i).natDegree ≤ D.natDegree)
    (hdiv : ∀ i, (P.coeff i).denom ∣ D.map (Int.castRingHom ℚ))
    (a b : ℤ) (hb : b ≠ 0)
    (hD : (D.map (Int.castRingHom ℚ)).eval ((a : ℚ)/b) ≠ 0)
    (Q : ℚ[X]) (hs : ∀ i, RatFunc.eval (RingHom.id ℚ) ((a : ℚ)/b) (P.coeff i)=Q.coeff i) :
    (clearedSpecializedIntegerPolynomial P D hlift h a b).map (Int.castRingHom ℚ) =
      C ((D.map (Int.castRingHom ℚ)).eval ((a : ℚ)/b)*(b : ℚ)^D.natDegree)*Q := by
  ext i
  rw [coeff_map, coeff_C_mul]
  by_cases hi : i ≤ h
  · rw [show (Int.castRingHom ℚ) _ = ((_ : ℤ) : ℚ) from rfl,
      clearedSpecializedIntegerPolynomial_coeff_eval P D hlift h i hi (hdeg i) (hdiv i) a b hb hD, hs]
  · rw [coeff_eq_zero_of_natDegree_lt
      ((clearedSpecializedIntegerPolynomial_natDegree_le P D hlift h a b).trans_lt (Nat.lt_of_not_ge hi)),
      map_zero, ← hs, coeff_eq_zero_of_natDegree_lt (hP.trans_lt (Nat.lt_of_not_ge hi)),
      RatFunc.eval_zero, mul_zero]

end
end Lambert
