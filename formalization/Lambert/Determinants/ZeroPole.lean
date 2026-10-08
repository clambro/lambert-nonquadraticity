import Lambert.Determinants.ZeroBlockIdentity
import Lambert.Determinants.MomentsMap
import Lambert.Determinants.ZeroPoleData

/-! # Coefficientwise zero-place bounds from finite translated moment blocks -/
namespace Lambert
noncomputable section
open Polynomial Finset Matrix Filter
open scoped Classical WithZero Topology
variable {K : Type*} [Field K]

/-- The monic finite-window functional specializes its polynomial moments and prescribed simple-pole values in the zero-place Laurent field. -/
def lambertZeroMonicMoment (z : LaurentSeries K) (k h r : ℕ) : LaurentSeries K :=
  nodalFunctional (fun j : Fin h => lambertZeroBase K ^ (k+j.val))
    ((Polynomial.leval z).comp (lambertPolynomialFunctional (lambertZeroBase K)))
    (fun j => -(z - geometricMomentPrefix (lambertZeroBase K) (k+j.val))) (X ^ r)

/-- Specializing a Lambert moment at the zero place differs from its monic functional by the positive-denominator sign. -/
theorem lambertPoleMoment_zero_eval (z : LaurentSeries K) (k h r : ℕ) :
    (lambertPoleMoment (lambertZeroBase K) k h r).eval z =
      (-1 : LaurentSeries K) ^ h * lambertZeroMonicMoment z k h r := by
  simp only [lambertPoleMoment, lambertNumeratorFunctional, LinearMap.smul_apply,
    nodalFunctional_apply, lambertZeroMonicMoment, eval_smul, eval_add, eval_finsetSum,
    eval_neg, eval_sub, eval_X, eval_C, smul_eq_mul, LinearMap.comp_apply,
    Polynomial.leval_apply]

/-- A uniform bound on finite translated moment blocks passes to every unit-ball specialization of the pole determinant. -/
theorem lambertPoleDeterminant_zero_eval_valuation_of_blocks
    (h k L s : ℕ) (E : ℤ)
    (hb : ∀ (Z : LaurentSeries K), Valued.v Z ≤ 1 → ∀ N, k+L ≤ N →
      Valued.v (Matrix.of (fun i j : Fin h =>
        lambertZeroBlockMoment Z k L N (i.val+j.val+s))).det ≤ WithZero.exp E)
    (z : LaurentSeries K) (hz : Valued.v z ≤ 1) :
    Valued.v ((lambertPoleDeterminant (lambertZeroBase K) h k L s).eval z) ≤
      WithZero.exp E := by
  let A : Matrix (Fin h) (Fin h) (LaurentSeries K) := fun i j =>
    lambertZeroMonicMoment z k L (i.val+j.val+s)
  let M : ℕ → Matrix (Fin h) (Fin h) (LaurentSeries K) := fun N i j =>
    lambertTruncatedNodal (lambertZeroBase K)
      (z+lambertPositivePrefix (lambertZeroBase K) N) k L N (X^(i.val+j.val+s))
  have hl : Tendsto M atTop (𝓝 A) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact lambertTruncatedNodal_tendsto z k L (X^(i.val+j.val+s))
  have hd := (continuous_id.matrix_det.tendsto A).comp hl
  have hbound : ∀ᶠ N in atTop, Valued.v (M N).det ≤ WithZero.exp E := by
    filter_upwards [eventually_ge_atTop (k+L)] with N hN
    have he : M N = Matrix.of (fun i j : Fin h => lambertZeroBlockMoment
        (z+lambertPositivePrefix (lambertZeroBase K) N) k L N (i.val+j.val+s)) := by
      apply Matrix.ext
      intro i j
      exact (lambertZeroBlockMoment_eq_truncated _ k L N _ hN).symm
    rw [he]
    exact hb _ (lambertPrefixCorrection_valuation_le_one z hz N) N hN
  have hA : Valued.v A.det ≤ WithZero.exp E := by
    simpa only [neg_neg] using laurent_valuation_le_of_tendsto
      (fun N => (M N).det) A.det (-E) hd (by simpa only [neg_neg] using hbound)
  have hm : (Polynomial.evalRingHom z).mapMatrix
      (Matrix.of fun i j : Fin h => lambertPoleMoment (lambertZeroBase K) k L (i.val+j.val+s)) =
      (-1 : LaurentSeries K)^L • A := by
    apply Matrix.ext
    intro i j
    exact lambertPoleMoment_zero_eval z k L _
  have he := (Polynomial.evalRingHom z).map_det
    (Matrix.of fun i j : Fin h => lambertPoleMoment (lambertZeroBase K) k L (i.val+j.val+s))
  rw [hm, Matrix.det_smul, Fintype.card_fin] at he
  unfold lambertPoleDeterminant
  change Valued.v ((Polynomial.evalRingHom z) _) ≤ _
  rw [he, map_mul, map_pow, map_pow, Valuation.map_neg, map_one, one_pow, one_pow, one_mul]
  exact hA

/-- A uniform zero-place evaluation bound controls every coefficient of a translated pole determinant. -/
theorem lambertPoleDeterminant_zero_coeff_valuation_of_eval
    (h k L s : ℕ) (E : ℤ)
    (hb : ∀ z : LaurentSeries ℚ, Valued.v z ≤ 1 →
      Valued.v ((lambertPoleDeterminant (lambertZeroBase ℚ) h k L s).eval z) ≤ WithZero.exp E)
    (i : ℕ) :
    Valued.v (lambertZeroMap ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k L s).coeff i)) ≤
      WithZero.exp E := by
  have he := laurentSeries_coeff_valuation_le_of_eval
    ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k L s).map lambertZeroMap)
    (-E) (fun x : ℚ => by
      rw [lambertPoleDeterminant_map, lambertZeroMap_X]
      simpa only [neg_neg] using hb (algebraMap ℚ (LaurentSeries ℚ) x) (laurentConstant_valuation_le x)) i
  simpa only [Polynomial.coeff_map, neg_neg] using he

/-- Every nonnegative-order specialization of a shifted Lambert determinant satisfies the signed zero-place bound. -/
theorem lambertPoleDeterminant_zero_eval_valuation (z : LaurentSeries K)
    (hz : Valued.v z ≤ 1) (h k : ℕ) :
    Valued.v ((lambertPoleDeterminant (lambertZeroBase K) h k h k).eval z) ≤
      WithZero.exp (lambertZeroExponent h k) := by
  apply lambertPoleDeterminant_zero_eval_valuation_of_blocks h k h k
    (lambertZeroExponent h k) ?_ z hz
  intro Z hZ N hN
  have he := lambertZeroBlock_det_valuation Z hZ h k (N-k)
  rw [lambertZeroBlock_mul, show k+(N-k)=N by omega] at he
  exact he

/-- Every coefficient of a shifted Lambert determinant satisfies the signed zero-place bound. -/
theorem lambertPoleDeterminant_zero_coeff_valuation (h k i : ℕ) :
    Valued.v (lambertZeroMap ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k h k).coeff i)) ≤
      WithZero.exp (lambertZeroExponent h k) := by
  exact lambertPoleDeterminant_zero_coeff_valuation_of_eval h k h k
    (lambertZeroExponent h k)
    (fun z hz => lambertPoleDeterminant_zero_eval_valuation z hz h k) i

end
end Lambert
