import Lambert.Determinants.TaylorFiltration

/-!
# Harmonic correction for bordered Lambert matrices

Removing the row harmonic term leaves a periodic polynomial in each Taylor
coefficient. This separates the two weights shared by pole and evaluation
rows of a bordered determinant.
-/

namespace Lambert
noncomputable section
open Finset PowerSeries
open scoped Classical

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Adding back the row harmonic residue makes every coefficient of a normalized Lambert entry periodic polynomial of the same degree. -/
theorem lambertLocalNormalizedEntry_corrected_coeff_periodic (ζ x : K) {n : ℕ}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (j r : ℕ) :
    HasPeriodicPolynomialDegree n r (fun i => coeff r
      (lambertLocalNormalizedEntry ζ x i j +
        C ((n : K)⁻¹ * algebraMap ℚ K (harmonic (i / n))))) := by
  cases r with
  | zero =>
    have he : (fun i => coeff 0
        (lambertLocalNormalizedEntry ζ x i j +
          C ((n : K)⁻¹ * algebraMap ℚ K (harmonic (i / n))))) =
        (fun _ : ℕ => -((n : K)⁻¹ * algebraMap ℚ K (harmonic (j / n)))) := by
      funext i
      rw [map_add, coeff_zero_C, lambertLocalNormalizedEntry_coeff_zero ζ x hζ]
      ring
    rw [he]
    exact hasPeriodicPolynomialDegree_const n _
  | succ r =>
    simpa only [map_add, coeff_C, Nat.succ_ne_zero, if_false, add_zero] using
      lambertLocalNormalizedEntry_coeff_succ_periodic ζ x hn hζ.pow_eq_one j r

/-- Each Taylor coefficient of a Lambert entry plus its row harmonic exponential has periodic polynomial degree at most its order. -/
theorem lambertLocalEntry_corrected_coeff_periodic (ζ x : K) {n : ℕ}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (j r : ℕ) :
    HasPeriodicPolynomialDegree n r (fun i =>
      coeff r (lambertLocalEntry ζ x i j) +
        ((n : K)⁻¹ * algebraMap ℚ K (harmonic (i / n))) *
          coeff r (lambertLocalBase ζ ^ (i * j))) := by
  have he (i : ℕ) :
      coeff r (lambertLocalEntry ζ x i j) +
        ((n : K)⁻¹ * algebraMap ℚ K (harmonic (i / n))) *
          coeff r (lambertLocalBase ζ ^ (i * j)) =
      ∑ ab ∈ antidiagonal r,
        coeff ab.1 (lambertLocalBase ζ ^ (i * j)) *
          coeff ab.2 (lambertLocalNormalizedEntry ζ x i j +
            C ((n : K)⁻¹ * algebraMap ℚ K (harmonic (i / n)))) := by
    rw [← coeff_mul, mul_add, map_add, coeff_mul_C,
      ← lambertLocalEntry_eq_normalized ζ x (hζ.ne_zero hn.ne')]
    ring
  simp_rw [he]
  apply HasPeriodicPolynomialDegree.finset_sum
  rintro ⟨a, b⟩ hab
  have hab' : a + b = r := mem_antidiagonal.mp hab
  simpa only [hab'] using
    (lambertLocalBase_coeff_periodic ζ hζ.pow_eq_one j a).mul
      (lambertLocalNormalizedEntry_corrected_coeff_periodic ζ x hn hζ j b)

private def borderedWeights (b n : ℕ) : Bool → ℕ → K := fun a i =>
  if a then
    if i < b then -1 else (n : K)⁻¹ * algebraMap ℚ K (harmonic (i / n))
  else if i < b then 0 else 1

private def borderedIndex (D A b : ℕ) : Fin (D + A) → Fin (b + D + A) :=
  Fin.addCases (fun j : Fin D => ⟨b + j.val, by omega⟩)
    (fun j : Fin A => ⟨j.val, by omega⟩)

private def borderedRestriction (D A b : ℕ) :
    (Fin (b + D + A) → K) →ₗ[K] (Fin (D + A) → K) where
  toFun f i := f (borderedIndex D A b i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The bordered coefficient space uses the same two periodic weights on pole rows and evaluation rows. -/
def lambertBorderedCoefficientSpace (D A b n r : ℕ) : Submodule K (Fin (D + A) → K) :=
  (periodicPolynomialSpace (b + D + A) n r (borderedWeights (K := K) b n)).map
    (borderedRestriction D A b)

/-- The bordered coefficient space has dimension at most twice the period times one more than the Taylor order. -/
theorem lambertBorderedCoefficientSpace_finrank_le (D A b n r : ℕ) :
    Module.finrank K (lambertBorderedCoefficientSpace (K := K) D A b n r) ≤
      2 * n * (r + 1) := by
  apply (Submodule.finrank_map_le _ _).trans
  simpa using periodicPolynomialSpace_finrank_le (b + D + A) n r
    (borderedWeights (K := K) b n)

/-- Bordered coefficient spaces increase with the Taylor order. -/
theorem lambertBorderedCoefficientSpace_mono (D A b n : ℕ) :
    Monotone (lambertBorderedCoefficientSpace (K := K) D A b n) := by
  intro r s hrs
  exact Submodule.map_mono (periodicPolynomialSpace_mono _ _ _ hrs)

/-- A local bordered Lambert column has regularized pole entries and unregularized evaluation entries. -/
def lambertBorderedLocalColumn (ζ x : K) (D A b j : ℕ) : Fin (D + A) → PowerSeries K :=
  Fin.addCases (fun i => lambertLocalEntry ζ x (b + i.val) j)
    (fun i => lambertLocalBase ζ ^ (i.val * j))

/-- A local polynomial column has geometric powers on pole rows and zero on evaluation rows. -/
def lambertBorderedPolynomialColumn (ζ : K) (D A b j : ℕ) : Fin (D + A) → PowerSeries K :=
  Fin.addCases (fun i => lambertLocalBase ζ ^ ((b + i.val) * j)) (fun _ => 0)

/-- Every Taylor coefficient of a bordered Lambert column lies in the shared two-weight space when its evaluation nodes precede the pole window. -/
theorem lambertBorderedLocalColumn_coeff_mem (ζ x : K) (D A b n j r : ℕ)
    (hAb : A ≤ b) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    (fun i => coeff r (lambertBorderedLocalColumn ζ x D A b j i)) ∈
      lambertBorderedCoefficientSpace (K := K) D A b n r := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let f := fun i => coeff r (lambertLocalEntry ζ x i j) +
    ((n : K)⁻¹ * algebraMap ℚ K (harmonic (i / n))) *
      coeff r (lambertLocalBase ζ ^ (i * j))
  let g := fun i => coeff r (lambertLocalBase ζ ^ (i * j))
  have hf := (lambertLocalEntry_corrected_coeff_periodic ζ x hn hζ j r).mem_weightedSpace
    hn (b + D + A) (borderedWeights (K := K) b n) false
  have hg := (lambertLocalBase_coeff_periodic ζ hζ.pow_eq_one j r).mem_weightedSpace
    hn (b + D + A) (borderedWeights (K := K) b n) true
  refine ⟨(fun i => f i.val * borderedWeights b n false i.val) -
    (fun i => g i.val * borderedWeights b n true i.val), Submodule.sub_mem _ hf hg, ?_⟩
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro v
    simp only [borderedRestriction, borderedIndex, LinearMap.coe_mk, AddHom.coe_mk, Fin.addCases_left,
      Pi.sub_apply, lambertBorderedLocalColumn, borderedWeights, Bool.false_eq_true,
      if_false, if_true, show ¬b + v.val < b by omega]
    dsimp only [f, g]
    ring
  · intro v
    have hv : v.val < b := by omega
    simp [borderedRestriction, borderedIndex, lambertBorderedLocalColumn, borderedWeights, hv, g]

/-- Every Taylor coefficient of a bordered polynomial column lies in the same coefficient space. -/
theorem lambertBorderedPolynomialColumn_coeff_mem (ζ : K) (D A b n j r : ℕ)
    (hAb : A ≤ b) (hn : 0 < n) (hζ : ζ ^ n = 1) :
    (fun i => coeff r (lambertBorderedPolynomialColumn ζ D A b j i)) ∈
      lambertBorderedCoefficientSpace (K := K) D A b n r := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hf := (lambertLocalBase_coeff_periodic ζ hζ j r).mem_weightedSpace
    hn (b + D + A) (borderedWeights (K := K) b n) false
  refine ⟨_, hf, ?_⟩
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro v
    simp [borderedRestriction, borderedIndex, lambertBorderedPolynomialColumn, borderedWeights,
      show ¬b + v.val < b by omega]
  · intro v
    have hv : v.val < b := by omega
    simp [borderedRestriction, borderedIndex, lambertBorderedPolynomialColumn, borderedWeights, hv]

/-- The local bordered matrix consists of Lambert columns followed by polynomial columns on the union of pole and evaluation nodes. -/
def lambertBorderedLocalMatrix (ζ x : K) (h A b d s : ℕ) :
    Matrix (Fin (h + d + A)) (Fin (h + d + A)) (PowerSeries K) := fun i j =>
  if j.val < h + A then lambertBorderedLocalColumn ζ x (h + d) A b (s + j.val) i
  else lambertBorderedPolynomialColumn ζ (h + d) A b (j.val - (h + A)) i

/-- The bordered local determinant satisfies the full filtered order bound without adding a third weight for evaluation rows. -/
theorem lambertBorderedLocalMatrix_order_ge_filtration (ζ x : K) (h A b d s n T : ℕ)
    (hAb : A ≤ b) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    (↑(∑ r ∈ range T, (h + d + A - 2 * n * (r + 1))) : ℕ∞) ≤
      (lambertBorderedLocalMatrix ζ x h A b d s).det.order := by
  have hmem : ∀ r j, (fun i => coeff r (lambertBorderedLocalMatrix ζ x h A b d s i j)) ∈
      lambertBorderedCoefficientSpace (K := K) (h + d) A b n r := by
    intro r j
    by_cases hj : j.val < h + A
    · simpa only [lambertBorderedLocalMatrix, if_pos hj] using
        lambertBorderedLocalColumn_coeff_mem ζ x (h + d) A b n (s + j.val) r hAb hn hζ
    · simpa only [lambertBorderedLocalMatrix, if_neg hj] using
        lambertBorderedPolynomialColumn_coeff_mem ζ (h + d) A b n (j.val - (h + A)) r
          hAb hn hζ.pow_eq_one
  simpa only [Fintype.card_fin] using
    powerSeries_det_order_ge_profile (lambertBorderedLocalMatrix ζ x h A b d s)
      (lambertBorderedCoefficientSpace (K := K) (h + d) A b n)
      (lambertBorderedCoefficientSpace_mono (h + d) A b n) hmem
      (fun r => 2 * n * (r + 1))
      (lambertBorderedCoefficientSpace_finrank_le (h + d) A b n) T

end
end Lambert
