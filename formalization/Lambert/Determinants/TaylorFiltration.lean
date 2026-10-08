import Lambert.Determinants.LocalExpansion
import Lambert.Arithmetic.PeriodicPolynomial

/-!
# Higher Taylor coefficients of Lambert entries

Removing the exponential factor leaves a harmonic residue and finite sums of
periodic polynomials in every positive coefficient order.
-/

namespace Lambert

noncomputable section

open Finset PowerSeries
open scoped Classical

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The normalized local Lambert entry removes its row-column exponential factor. -/
def lambertLocalNormalizedEntry (ζ x : K) (i j : ℕ) : PowerSeries K :=
  X * C x - (∑ k ∈ range j, exponentialReciprocal (ζ ^ (k + 1)) ((k + 1 : ℕ) : K)) -
    ∑ k ∈ range i, rescale ((k + 1 : ℕ) : K) (exponentialInversePower (ζ ^ (k + 1)) j) *
      exponentialReciprocal (ζ ^ (k + 1)) ((k + 1 : ℕ) : K)

private theorem local_inversePower_mul (ζ : K) (hz : ζ ≠ 0) (h j : ℕ) :
    rescale (h : K) (exponentialInversePower (ζ ^ h) j) * lambertLocalBase ζ ^ (h * j) = 1 := by
  have he := congrArg (rescale (h : K)) (exponentialInversePower_mul (ζ ^ h) (pow_ne_zero _ hz) j)
  have hC (z : K) : rescale (h : K) (C z) = C z := by
    ext r
    simp [coeff_rescale, coeff_C]
    split_ifs <;> simp_all
  have hb : rescale (h : K) (C (ζ ^ h) * exp K) = lambertLocalBase ζ ^ h := by
    rw [map_mul, hC, lambertLocalBase_pow]
  rw [map_mul, map_pow, hb, map_one, ← pow_mul] at he
  exact he

/-- Restoring the exponential factor recovers the exact regularized Lambert entry. -/
theorem lambertLocalEntry_eq_normalized (ζ x : K) (hz : ζ ≠ 0) (i j : ℕ) :
    lambertLocalEntry ζ x i j = lambertLocalBase ζ ^ (i * j) *
      lambertLocalNormalizedEntry ζ x i j := by
  induction i with
  | zero => simp [lambertLocalEntry, lambertLocalNormalizedEntry]
  | succ i ih =>
    rw [lambertLocalEntry, ih]
    have hn : lambertLocalNormalizedEntry ζ x (i + 1) j = lambertLocalNormalizedEntry ζ x i j -
        rescale ((i + 1 : ℕ) : K) (exponentialInversePower (ζ ^ (i + 1)) j) *
          exponentialReciprocal (ζ ^ (i + 1)) ((i + 1 : ℕ) : K) := by
      simp only [lambertLocalNormalizedEntry, sum_range_succ]
      ring
    rw [hn]
    have he := local_inversePower_mul ζ hz (i + 1) j
    have hp : lambertLocalBase ζ ^ ((i + 1) * j) =
        lambertLocalBase ζ ^ j * lambertLocalBase ζ ^ (i * j) := by
      rw [Nat.add_mul, one_mul, pow_add, mul_comm]
    rw [hp] at he ⊢
    linear_combination exponentialReciprocal (ζ ^ (i + 1)) ((i + 1 : ℕ) : K) * he

/-- The residue of a normalized entry is the negative sum of the two harmonic prefixes. -/
theorem lambertLocalNormalizedEntry_coeff_zero (ζ x : K) {n : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (i j : ℕ) :
    coeff 0 (lambertLocalNormalizedEntry ζ x i j) =
      -((n : K)⁻¹ * algebraMap ℚ K (harmonic (i / n)) +
        (n : K)⁻¹ * algebraMap ℚ K (harmonic (j / n))) := by
  have he : coeff 0 (lambertLocalNormalizedEntry ζ x i j) =
      -(lambertResiduePrefix ζ i + lambertResiduePrefix ζ j) := by
    simp only [lambertLocalNormalizedEntry, map_sub, map_sum, coeff_zero_X_mul,
      exponentialReciprocal_coeff_zero, exponentialReciprocal_inversePower_coeff_zero,
      lambertResiduePrefix]
    ring
  rw [he, lambertResiduePrefix_eq_harmonic ζ hζ, lambertResiduePrefix_eq_harmonic ζ hζ]

/-- Every positive coefficient of a normalized Lambert entry is a periodic
polynomial of degree at most its coefficient order in the row index. -/
theorem lambertLocalNormalizedEntry_coeff_succ_periodic (ζ x : K) {n : ℕ}
    (hn : 0 < n) (hζ : ζ ^ n = 1) (j r : ℕ) :
    HasPeriodicPolynomialDegree n (r + 1)
      (fun i => coeff (r + 1) (lambertLocalNormalizedEntry ζ x i j)) := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let A : K → K := fun z => if z = 1 then
    coeff (r + 1) (exponentialInversePower z j * bernoulliPowerSeries K)
    else coeff r (exponentialInversePower z j * (C z * exp K - 1)⁻¹)
  have hf : HasPeriodicPolynomialDegree n r (fun h => (h : K) ^ r * A (ζ ^ h)) := by
    simpa only [Nat.add_zero] using
      (hasPeriodicPolynomialDegree_pow (K := K) n r).mul
        (hasPeriodicPolynomialDegree_root n ζ hζ A)
  have hs := hf.positivePrefix hn
  let b := coeff (r + 1)
    (X * C x - ∑ k ∈ range j, exponentialReciprocal (ζ ^ (k + 1)) ((k + 1 : ℕ) : K))
  have hc := (hasPeriodicPolynomialDegree_const n b).mono (Nat.zero_le (r + 1))
  have he : (fun i => coeff (r + 1) (lambertLocalNormalizedEntry ζ x i j)) =
      (fun i => b + -(∑ k ∈ range i, ((k + 1 : ℕ) : K) ^ r * A (ζ ^ (k + 1)))) := by
    funext i
    change coeff (r + 1) (_ - _) = _
    rw [map_sub, map_sum]
    change b - _ = b + -_
    rw [sub_eq_add_neg]
    congr 2
    apply sum_congr rfl
    intro k _
    exact exponentialReciprocal_twisted_coeff_succ _ _
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)) _ r
  rw [he]
  exact hc.add hs.neg

/-- Each coefficient of the row-column exponential factor has periodic
polynomial degree at most its coefficient order in the row index. -/
theorem lambertLocalBase_coeff_periodic (ζ : K) {n : ℕ} (hζ : ζ ^ n = 1) (j r : ℕ) :
    HasPeriodicPolynomialDegree n r (fun i => coeff r (lambertLocalBase ζ ^ (i * j))) := by
  have hp := (hasPeriodicPolynomialDegree_root n ζ hζ (fun z => z ^ j)).mul
    (hasPeriodicPolynomialDegree_pow (K := K) n r)
  have hs := hp.smul ((j : K) ^ r * algebraMap ℚ K (1 / r.factorial))
  have he : (fun i => coeff r (lambertLocalBase ζ ^ (i * j))) =
      (fun i : ℕ => ((j : K) ^ r * algebraMap ℚ K (1 / r.factorial)) *
        ((ζ ^ i) ^ j * (i : K) ^ r)) := by
    funext i
    rw [lambertLocalBase_pow, coeff_C_mul, coeff_rescale, coeff_exp]
    simp only [Nat.cast_mul, mul_pow, pow_mul]
    ring
  rw [he]
  simpa only [zero_add] using hs

/-- Periodic polynomials of degree at most `r` belong to the Lambert coefficient space. -/
theorem lambertCoefficientSpace_periodic_mem {n r : ℕ} {f : ℕ → K}
    (hn : 0 < n) (hf : HasPeriodicPolynomialDegree n r f) (h : ℕ) :
    (fun i : Fin h => f i.val) ∈ lambertCoefficientSpace (K := K) h n r := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  unfold lambertCoefficientSpace
  convert hf.mem_weightedSpace hn h
    (fun b : Bool => if b then fun i => algebraMap ℚ K (harmonic (i / n)) else fun _ => 1) false using 1
  ext i
  simp

/-- A periodic polynomial of degree at most `r` times the harmonic weight
belongs to the Lambert coefficient space. -/
theorem lambertCoefficientSpace_harmonic_mem {n r : ℕ} {f : ℕ → K}
    (hn : 0 < n) (hf : HasPeriodicPolynomialDegree n r f) (h : ℕ) :
    (fun i : Fin h => f i.val * algebraMap ℚ K (harmonic (i.val / n))) ∈
      lambertCoefficientSpace (K := K) h n r := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  exact hf.mem_weightedSpace hn h
    (fun b : Bool => if b then fun i => algebraMap ℚ K (harmonic (i / n)) else fun _ => 1) true

/-- Every Taylor coefficient column of the actual regularized Lambert matrix
belongs to the harmonic-periodic space of the same degree. -/
theorem lambertLocalEntry_coeff_mem (ζ x : K) (h n : ℕ)
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (j r : ℕ) :
    (fun i : Fin h => coeff r (lambertLocalEntry ζ x i.val j)) ∈
      lambertCoefficientSpace (K := K) h n r := by
  have hz := hζ.ne_zero (Nat.ne_of_gt hn)
  have he : (fun i : Fin h => coeff r (lambertLocalEntry ζ x i.val j)) =
      ∑ ab ∈ antidiagonal r, (fun i : Fin h => coeff ab.1 (lambertLocalBase ζ ^ (i.val * j)) *
        coeff ab.2 (lambertLocalNormalizedEntry ζ x i.val j)) := by
    funext i
    rw [lambertLocalEntry_eq_normalized ζ x hz, coeff_mul]
    simp only [Finset.sum_apply]
  rw [he]
  apply Submodule.sum_mem
  rintro ⟨a, b⟩ hab
  have hab' : a + b = r := mem_antidiagonal.mp hab
  cases b with
  | zero =>
    have har : a = r := by omega
    subst a
    have hp := lambertLocalBase_coeff_periodic ζ hζ.pow_eq_one j r
    have hplain := lambertCoefficientSpace_periodic_mem hn hp h
    have hharm := lambertCoefficientSpace_harmonic_mem hn hp h
    have hm := (lambertCoefficientSpace (K := K) h n r).neg_mem
      ((lambertCoefficientSpace (K := K) h n r).add_mem
        ((lambertCoefficientSpace (K := K) h n r).smul_mem (n : K)⁻¹ hharm)
        ((lambertCoefficientSpace (K := K) h n r).smul_mem
          ((n : K)⁻¹ * algebraMap ℚ K (harmonic (j / n))) hplain))
    convert hm using 1
    funext i
    rw [lambertLocalNormalizedEntry_coeff_zero ζ x hζ]
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  | succ b =>
    have hp := (lambertLocalBase_coeff_periodic ζ hζ.pow_eq_one j a).mul
      (lambertLocalNormalizedEntry_coeff_succ_periodic ζ x hn hζ.pow_eq_one j b)
    have hpr : HasPeriodicPolynomialDegree n r (fun i =>
        coeff a (lambertLocalBase ζ ^ (i * j)) * coeff (b + 1) (lambertLocalNormalizedEntry ζ x i j)) := by
      simpa only [← hab', Nat.succ_eq_add_one] using hp
    exact lambertCoefficientSpace_periodic_mem hn hpr h

end

end Lambert
