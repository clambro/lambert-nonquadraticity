import Lambert.Determinants.MomentData
import Lambert.Arithmetic.ExponentialReciprocal
import Lambert.Arithmetic.PeriodicPolynomialSpace
import Lambert.Arithmetic.FilteredDeterminant
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Formal local Lambert expansions

The local base is `ζ exp(ε)`. Exact reciprocal identities identify the
regularized power-series recurrence with the algebraic Lambert entries.
-/

namespace Lambert

noncomputable section

open Finset
open scoped Classical

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The formal exponential base has constant term equal to its specified phase. -/
def lambertLocalBase (ζ : K) : PowerSeries K :=
  PowerSeries.C ζ * PowerSeries.exp K

/-- A positive power of the local base is the scaled exponential at that exponent. -/
theorem lambertLocalBase_pow (ζ : K) (h : ℕ) :
    lambertLocalBase ζ ^ h = PowerSeries.C (ζ ^ h) *
      PowerSeries.rescale (h : K) (PowerSeries.exp K) := by
  simp only [lambertLocalBase, mul_pow, map_pow, PowerSeries.exp_pow_eq_rescale_exp]

/-- Multiplication by the formal parameter removes every reciprocal pole in
the positive-exponent local Lambert moments. -/
theorem lambertLocalReciprocal_mul (ζ : K) (h : ℕ) (hh : h ≠ 0) :
    exponentialReciprocal (ζ ^ h) (h : K) * (lambertLocalBase ζ ^ h - 1) =
      PowerSeries.X := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  rw [lambertLocalBase_pow]
  exact exponentialReciprocal_mul _ _ (Nat.cast_ne_zero.mpr hh)

/-- The local Lambert entry is the power-series recurrence after multiplication
by the formal parameter. -/
def lambertLocalEntry (ζ x : K) : ℕ → ℕ → PowerSeries K
  | 0, j => PowerSeries.X * PowerSeries.C x -
      ∑ k ∈ range j, exponentialReciprocal (ζ ^ (k + 1)) ((k + 1 : ℕ) : K)
  | i + 1, j => lambertLocalBase ζ ^ j * lambertLocalEntry ζ x i j -
      exponentialReciprocal (ζ ^ (i + 1)) ((i + 1 : ℕ) : K)

/-- In any field containing the power-series ring, the regularized local
reciprocal equals the actual reciprocal times the formal parameter. -/
theorem lambertLocalReciprocal_map {F : Type*} [Field F]
    (f : PowerSeries K →+* F) (hf : Function.Injective f) (ζ : K) (h : ℕ) (hh : h ≠ 0) :
    f (exponentialReciprocal (ζ ^ h) (h : K)) =
      f PowerSeries.X * (1 / (f (lambertLocalBase ζ) ^ h - 1)) := by
  have he := congrArg f (lambertLocalReciprocal_mul ζ h hh)
  simp only [map_mul, map_sub, map_pow, map_one] at he
  have hx : f PowerSeries.X ≠ 0 := by
    rw [ne_eq, ← map_zero f, hf.eq_iff]
    exact PowerSeries.X_ne_zero
  have hd : f (lambertLocalBase ζ) ^ h - 1 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact hx he.symm
  exact (eq_div_iff hd).mpr he |>.trans (by rw [div_eq_mul_inv, one_div])

/-- The local power-series construction is exactly the algebraic Lambert entry
times the formal parameter in any containing field. -/
theorem lambertLocalEntry_map {F : Type*} [Field F]
    (f : PowerSeries K →+* F) (hf : Function.Injective f) (ζ x : K) (i j : ℕ) :
    f (lambertLocalEntry ζ x i j) = f PowerSeries.X *
      (lambertPoleEntry (f (lambertLocalBase ζ)) i j).eval (f (PowerSeries.C x)) := by
  induction i with
  | zero =>
    simp only [lambertLocalEntry, map_sub, map_mul, map_sum, lambertPoleEntry_zero,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum, geometricMomentPrefix,
      lambertLocalReciprocal_map f hf _ _ (Nat.succ_ne_zero _), mul_sub, mul_sum]
  | succ i ih =>
    simp only [lambertLocalEntry, map_sub, map_mul, map_pow, ih,
      lambertLocalReciprocal_map f hf _ _ (Nat.succ_ne_zero _), lambertPoleEntry_succ,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]
    simp only [Nat.succ_eq_add_one]
    ring

/-- In the fraction field of the power-series ring, the local recurrence
recovers the actual Lambert polynomial evaluation without an embedding hypothesis. -/
theorem lambertLocalEntry_fractionRing (ζ x : K) (i j : ℕ) :
    algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (lambertLocalEntry ζ x i j) =
      algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X *
      (lambertPoleEntry
        (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (lambertLocalBase ζ)) i j).eval
        (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (PowerSeries.C x)) :=
  lambertLocalEntry_map _ (IsFractionRing.injective _ _) ζ x i j

/-- Regularized local Lambert entries are symmetric in their two moment indices. -/
theorem lambertLocalEntry_symm (ζ x : K) (i j : ℕ) :
    lambertLocalEntry ζ x i j = lambertLocalEntry ζ x j i := by
  apply (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  rw [lambertLocalEntry_fractionRing, lambertLocalEntry_fractionRing]
  congr 2
  apply lambertPoleEntry_symm
  intro n hn
  have he := congrArg (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))
    (lambertLocalReciprocal_mul ζ (n + 1) (Nat.succ_ne_zero n))
  simp only [map_mul, map_sub, map_pow, map_one, hn, sub_self, mul_zero] at he
  have hx := (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))).eq_iff.mp
    (he.symm.trans (map_zero _).symm)
  exact PowerSeries.X_ne_zero hx

/-- The residue prefix sums the reciprocals at indices where the phase is one. -/
def lambertResiduePrefix (ζ : K) (i : ℕ) : K :=
  ∑ k ∈ range i, if ζ ^ (k + 1) = 1 then ((k + 1 : ℕ) : K)⁻¹ else 0

/-- Every local Lambert entry has the symmetric residue prescribed by its two
finite phase-one reciprocal prefixes. -/
theorem lambertLocalEntry_coeff_zero (ζ x : K) (i j : ℕ) :
    PowerSeries.coeff 0 (lambertLocalEntry ζ x i j) =
      -(ζ ^ (i * j) * (lambertResiduePrefix ζ i + lambertResiduePrefix ζ j)) := by
  have hr (z a : K) : PowerSeries.constantCoeff (exponentialReciprocal z a) =
      if z = 1 then a⁻¹ else 0 := by
        simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using exponentialReciprocal_coeff_zero z a
  induction i with
  | zero =>
    simp [lambertLocalEntry, lambertResiduePrefix, hr]
  | succ i ih =>
    have hp : lambertResiduePrefix ζ (i + 1) = lambertResiduePrefix ζ i +
        (if ζ ^ (i + 1) = 1 then ((i + 1 : ℕ) : K)⁻¹ else 0) := sum_range_succ _ _
    have he : ζ ^ ((i + 1) * j) *
        (if ζ ^ (i + 1) = 1 then ((i + 1 : ℕ) : K)⁻¹ else 0) =
        (if ζ ^ (i + 1) = 1 then ((i + 1 : ℕ) : K)⁻¹ else 0) := by
      split_ifs with hz
      · rw [pow_mul, hz, one_pow, one_mul]
      · rw [mul_zero]
    have hi := ih
    simp only [PowerSeries.coeff_zero_eq_constantCoeff] at hi ⊢
    simp only [lambertLocalEntry, map_sub, map_mul, map_pow, lambertLocalBase,
      PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_exp, mul_one, hi]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      exponentialReciprocal_coeff_zero, hp]
    simp only [Nat.add_mul, one_mul, pow_add, pow_one] at he ⊢
    linear_combination he

/-- At a primitive root, the residue prefix is a scaled harmonic number. -/
theorem lambertResiduePrefix_eq_harmonic (ζ : K) {n : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (i : ℕ) :
    lambertResiduePrefix ζ i = (n : K)⁻¹ * algebraMap ℚ K (harmonic (i / n)) := by
  induction i with
  | zero => simp [lambertResiduePrefix]
  | succ i ih =>
    rw [lambertResiduePrefix, sum_range_succ]
    change lambertResiduePrefix ζ i + _ = _
    rw [ih, hζ.pow_eq_one_iff_dvd]
    by_cases hd : n ∣ i + 1
    · rw [if_pos hd, Nat.succ_div_of_dvd hd, harmonic_succ, map_add, map_inv₀,
        map_natCast, mul_add]
      congr 1
      have he : ((i + 1 : ℕ) : K) = (n : K) * ((i / n : ℕ) + 1 : K) := by
        have hnat : i + 1 = n * (i / n + 1) := by
          rw [← Nat.succ_div_of_dvd hd, Nat.mul_div_cancel' hd]
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using congrArg (fun m : ℕ => (m : K)) hnat
      rw [he, mul_inv]
      simp only [Nat.cast_add, Nat.cast_one]
    · rw [if_neg hd, add_zero, Nat.succ_div_of_not_dvd hd]

/-- The Lambert coefficient filtration uses the constant weight and the
harmonic number at the quotient of the row index by the root order. -/
def lambertCoefficientSpace (h n r : ℕ) : Submodule K (Fin h → K) :=
  periodicPolynomialSpace h n r (fun b : Bool => if b then
    fun i => algebraMap ℚ K (harmonic (i / n)) else fun _ => 1)

/-- The Lambert coefficient spaces are nested in the Taylor degree. -/
theorem lambertCoefficientSpace_mono (h n : ℕ) :
    Monotone (fun r => lambertCoefficientSpace (K := K) h n r) :=
  periodicPolynomialSpace_mono _ _ _

/-- The Lambert coefficient space at order `r` has dimension at most `2n(r+1)`. -/
theorem lambertCoefficientSpace_finrank_le (h n r : ℕ) :
    Module.finrank K (lambertCoefficientSpace (K := K) h n r) ≤ 2 * n * (r + 1) := by
  simpa only [Fintype.card_bool, lambertCoefficientSpace] using!
    periodicPolynomialSpace_finrank_le h n r
      (fun b : Bool => if b then fun i => algebraMap ℚ K (harmonic (i / n)) else fun _ => 1)

/-- The residue vanishes when both indices are below the order of the primitive root. -/
theorem lambertLocalEntry_coeff_zero_of_lt (ζ x : K) {n i j : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (hi : i < n) (hj : j < n) :
    PowerSeries.coeff 0 (lambertLocalEntry ζ x i j) = 0 := by
  rw [lambertLocalEntry_coeff_zero, lambertResiduePrefix_eq_harmonic ζ hζ,
    lambertResiduePrefix_eq_harmonic ζ hζ]
  simp [Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj]

end

end Lambert
