import Lambert.Determinants.BorderedFiltration
import Lambert.Determinants.RectangularResidues

/-! # Residue cancellation in bordered Lambert determinants -/
namespace Lambert
noncomputable section
open PowerSeries Matrix Finset
open scoped Classical
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Reordering the size expression exposes the polynomial tail of the bordered local matrix. -/
def lambertBorderedTailMatrix (ζ x : K) (h A b d s : ℕ) :
    Matrix (Fin (h + A + d)) (Fin (h + A + d)) (PowerSeries K) :=
  (lambertBorderedLocalMatrix ζ x h A b d s).submatrix
    (finCongr (by omega)) (finCongr (by omega))

/-- Reordering the size expression preserves the bordered determinant. -/
theorem lambertBorderedTailMatrix_det (ζ x : K) (h A b d s : ℕ) :
    (lambertBorderedTailMatrix ζ x h A b d s).det =
      (lambertBorderedLocalMatrix ζ x h A b d s).det :=
  det_submatrix_equiv_self _ _

/-- The corrected bordered matrix cancels represented harmonic residues using its polynomial tail. -/
def lambertBorderedCorrectedMatrix (ζ x : K) (h A b d s n : ℕ) :
    Matrix (Fin (h + A + d)) (Fin (h + A + d)) (PowerSeries K) := fun i j =>
  Fin.addCases (fun r => lambertBorderedTailMatrix ζ x h A b d s i (Fin.castAdd d r) +
    ∑ k : Fin d, lambertBorderedTailMatrix ζ x h A b d s i (Fin.natAdd (h + A) k) *
      (if k.val = (s + r.val) % n then C (lambertResiduePrefix ζ (s + r.val)) else 0))
    (fun k => lambertBorderedTailMatrix ζ x h A b d s i (Fin.natAdd (h + A) k)) j

/-- The residue correction preserves the original bordered determinant exactly. -/
theorem lambertBorderedCorrectedMatrix_det (ζ x : K) (h A b d s n : ℕ) :
    (lambertBorderedCorrectedMatrix ζ x h A b d s n).det =
      (lambertBorderedLocalMatrix ζ x h A b d s).det := by
  rw [← lambertBorderedTailMatrix_det]
  exact det_add_tail_columns (h + A) d (lambertBorderedTailMatrix ζ x h A b d s)
    (fun k r => if k.val = (s + r.val) % n then C (lambertResiduePrefix ζ (s + r.val)) else 0)

/-- At a pole node below the period, a represented or absent harmonic residue vanishes after correction. -/
theorem lambertBorderedCorrectedMatrix_coeff_zero (ζ x : K) (h A b d s n : ℕ)
    (hζ : IsPrimitiveRoot ζ n) (i : Fin (h + A + d)) (r : Fin (h + A))
    (hip : i.val < h + d) (hi : b + i.val < n)
    (hr : ¬(n ≤ s + r.val ∧ d ≤ (s + r.val) % n)) :
    coeff 0 (lambertBorderedCorrectedMatrix ζ x h A b d s n i (Fin.castAdd d r)) = 0 := by
  have hm (j : Fin (h + A)) :
      lambertBorderedTailMatrix ζ x h A b d s i (Fin.castAdd d j) =
        lambertLocalEntry ζ x (b + i.val) (s + j.val) := by
    simp [lambertBorderedTailMatrix, lambertBorderedLocalMatrix,
      lambertBorderedLocalColumn, Fin.addCases, hip]
  have hp (j : Fin d) :
      lambertBorderedTailMatrix ζ x h A b d s i (Fin.natAdd (h + A) j) =
        lambertLocalBase ζ ^ ((b + i.val) * j.val) := by
    simp [lambertBorderedTailMatrix, lambertBorderedLocalMatrix,
      lambertBorderedPolynomialColumn, Fin.addCases, hip]
  simp only [lambertBorderedCorrectedMatrix, Fin.addCases_left, hm, hp]
  by_cases ht : (s + r.val) % n < d
  · let k : Fin d := ⟨(s + r.val) % n, ht⟩
    rw [sum_eq_single k]
    · simp only [k, ite_true, map_add, coeff_mul_C, lambertLocalEntry_coeff_zero]
      have hc : coeff 0 (lambertLocalBase ζ ^ ((b + i.val) * ((s + r.val) % n))) =
          ζ ^ ((b + i.val) * ((s + r.val) % n)) := by
        simp [coeff_zero_eq_constantCoeff, lambertLocalBase]
      rw [hc, lambertResiduePrefix_eq_harmonic ζ hζ (b + i.val), Nat.div_eq_of_lt hi]
      simp only [harmonic_zero, map_zero, mul_zero, zero_add]
      have he : ζ ^ ((b + i.val) * (s + r.val)) =
          ζ ^ ((b + i.val) * ((s + r.val) % n)) := by
        rw [Nat.mul_comm (b + i.val), pow_mul, pow_eq_pow_mod (s + r.val) hζ.pow_eq_one,
          ← pow_mul, Nat.mul_comm]
      rw [he]
      ring
    · intro j _ hj
      have hne : j.val ≠ (s + r.val) % n := fun he => hj (Fin.ext he)
      simp [hne]
    · simp
  · have hz : ∀ j : Fin d, j.val ≠ (s + r.val) % n := by intro j; omega
    simp only [hz, if_false, mul_zero, sum_const_zero, add_zero]
    exact lambertLocalEntry_coeff_zero_of_lt ζ x hζ hi (by omega)

/-- Small pole nodes and cancelled harmonic columns give the bordered residue order bound. -/
theorem lambertBorderedLocalMatrix_order_ge_residue (ζ x : K) (h A b d s n : ℕ)
    (hζ : IsPrimitiveRoot ζ n) :
    (↑(h - lambertRectangularResidualCount (h + A) d s n - (b + (h + d) - max b n)) : ℕ∞) ≤
      (lambertBorderedLocalMatrix ζ x h A b d s).det.order := by
  let rows := univ.filter (fun i : Fin (h + A + d) => i.val < h + d ∧ b + i.val < n)
  let good := univ.filter (fun r : Fin (h + A) => ¬(n ≤ r.val + s ∧ d ≤ (r.val + s) % n))
  let cols := good.map (Fin.castAddEmb d)
  have hz : ∀ i ∈ rows, ∀ j ∈ cols,
      coeff 0 (lambertBorderedCorrectedMatrix ζ x h A b d s n i j) = 0 := by
    intro i hi j hj
    obtain ⟨r, hr, rfl⟩ := mem_map.mp hj
    obtain ⟨_, hip, hin⟩ := mem_filter.mp hi
    apply lambertBorderedCorrectedMatrix_coeff_zero ζ x h A b d s n hζ i r hip hin
    simpa only [Nat.add_comm s] using (mem_filter.mp hr).2
  have he := powerSeries_det_order_ge_rectangular_zero_block
    (lambertBorderedCorrectedMatrix ζ x h A b d s n) rows cols hz
  rw [lambertBorderedCorrectedMatrix_det] at he
  have hc : good.card + lambertRectangularResidualCount (h + A) d s n = h + A := by
    have hh := card_filter_add_card_filter_not (s := (univ : Finset (Fin (h + A))))
      (p := fun r => n ≤ r.val + s ∧ d ≤ (r.val + s) % n)
    simpa only [card_univ, Fintype.card_fin, good, lambertRectangularResidualCount, add_comm] using hh
  have hrows : rows = univ.filter (fun i : Fin (h + A + d) => i.val < min (h + d) (n - b)) := by
    ext i
    simp only [rows, mem_filter, mem_univ, true_and]
    omega
  have hrow : rows.card = min (h + d) (n - b) := by
    rw [hrows, Fin.card_filter_val_lt]
    omega
  have hcol : cols.card = good.card := card_map _
  rw [hrow, hcol, Fintype.card_fin] at he
  have ha : min (h + d) (n - b) + good.card - (h + A + d) =
      h - lambertRectangularResidualCount (h + A) d s n - (b + (h + d) - max b n) := by omega
  rwa [ha] at he

end
end Lambert
