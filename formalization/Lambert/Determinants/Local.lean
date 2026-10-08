import Lambert.Determinants.TaylorFiltration
import Lambert.Determinants.LocalVandermonde

/-! # Local determinant cancellation on translated Lambert windows -/
namespace Lambert
noncomputable section
open PowerSeries Matrix Finset
open scoped Classical WithZero
variable {K : Type*} [Field K] [Algebra ℚ K]

private def restrictWindow (k h : ℕ) : (Fin (k+h) → K) →ₗ[K] (Fin h → K) where
  toFun f i := f ⟨k+i.val, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coefficient filtration on a translated window is the restriction of the harmonic-periodic filtration to that window. -/
def lambertTranslatedCoefficientSpace (h k n r : ℕ) : Submodule K (Fin h → K) :=
  (lambertCoefficientSpace (K := K) (k+h) n r).map (restrictWindow k h)

/-- Restriction to a translated window preserves the bound of 2n(r+1) on the coefficient-space dimension. -/
theorem lambertTranslatedCoefficientSpace_finrank_le (h k n r : ℕ) :
    Module.finrank K (lambertTranslatedCoefficientSpace (K := K) h k n r) ≤ 2*n*(r+1) :=
  (Submodule.finrank_map_le _ _).trans (lambertCoefficientSpace_finrank_le (k+h) n r)

/-- Translated harmonic-periodic coefficient spaces increase with the Taylor order. -/
theorem lambertTranslatedCoefficientSpace_mono (h k n : ℕ) :
    Monotone (lambertTranslatedCoefficientSpace (K := K) h k n) := by
  intro r s hrs
  exact Submodule.map_mono (lambertCoefficientSpace_mono (k+h) n hrs)

/-- Every local Lambert column restricted to a translated window lies in its restricted coefficient filtration. -/
theorem lambertTranslatedLocalEntry_coeff_mem (ζ x : K) (h k n : ℕ)
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (j r : ℕ) :
    (fun i : Fin h => coeff r (lambertLocalEntry ζ x (k+i.val) j)) ∈
      lambertTranslatedCoefficientSpace (K := K) h k n r := by
  exact ⟨_, lambertLocalEntry_coeff_mem ζ x (k+h) n hn hζ j r, rfl⟩

/-- Translating both index windows preserves the full filtered lower bound on the regularized determinant order. -/
theorem lambertLocalEntry_det_order_ge_filtration (ζ x : K) (h k s n T : ℕ)
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    (↑(∑ r ∈ range T, (h-2*n*(r+1))) : ℕ∞) ≤
      (Matrix.det (fun i j : Fin h => lambertLocalEntry ζ x (k+i.val) (s+j.val))).order := by
  simpa only [Fintype.card_fin] using powerSeries_det_order_ge_profile
    (fun i j : Fin h => lambertLocalEntry ζ x (k+i.val) (s+j.val))
    (lambertTranslatedCoefficientSpace (K := K) h k n)
    (lambertTranslatedCoefficientSpace_mono h k n)
    (fun r j => lambertTranslatedLocalEntry_coeff_mem ζ x h k n hn hζ (s+j.val) r)
    (fun r => 2*n*(r+1)) (lambertTranslatedCoefficientSpace_finrank_le h k n) T

/-- A regularized translated Lambert determinant has the order supplied by its square block of zero residues. -/
theorem lambertLocalEntry_det_order_ge_residue (ζ x : K) (h k n : ℕ)
    (hζ : IsPrimitiveRoot ζ n) :
    (↑(2*min h (n-k)-h) : ℕ∞) ≤
      (Matrix.det (fun i j : Fin h => lambertLocalEntry ζ x (k+i.val) (k+j.val))).order := by
  let rows := univ.filter (fun i : Fin h => i.val < n-k)
  have hz : ∀ i ∈ rows, ∀ j ∈ rows,
      coeff 0 (lambertLocalEntry ζ x (k+i.val) (k+j.val)) = 0 := by
    intro i hi j hj
    have hi := (mem_filter.mp hi).2
    have hj := (mem_filter.mp hj).2
    exact lambertLocalEntry_coeff_zero_of_lt ζ x hζ (by omega) (by omega)
  have he := powerSeries_det_order_ge_rectangular_zero_block
    (fun i j : Fin h => lambertLocalEntry ζ x (k+i.val) (k+j.val)) rows rows hz
  have hc : rows.card = min h (n-k) := Fin.card_filter_val_lt
  simpa only [hc, Fintype.card_fin, two_mul] using he

/-- Translating all geometric nodes does not change their cyclotomic collision order. -/
theorem lambertTranslatedLocalVandermonde_order (ζ : K) (h k n : ℕ)
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    (Matrix.vandermonde (fun i : Fin h => lambertLocalBase ζ ^ (k+i.val))).det.order =
      (↑(∑ r ∈ range h, (h-(r+1)*n)) : ℕ∞) := by
  have he : (Matrix.vandermonde (fun i : Fin h => lambertLocalBase ζ ^ (k+i.val))).det.order =
      (Matrix.vandermonde (fun i : Fin h => lambertLocalBase ζ ^ i.val)).det.order := by
    simp only [Matrix.det_vandermonde, order_prod]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j hj
    have hij : i.val < j.val := Fin.lt_def.mp (mem_Ioi.mp hj)
    rw [lambertLocalBase_pow_sub_order_primitive ζ hn hζ _ _ (by omega),
      lambertLocalBase_pow_sub_order_primitive ζ hn hζ _ _ hij]
    simp only [Nat.add_sub_add_left]
  rw [he, lambertLocalVandermonde_order_deficits ζ h n hn hζ]

end
end Lambert
