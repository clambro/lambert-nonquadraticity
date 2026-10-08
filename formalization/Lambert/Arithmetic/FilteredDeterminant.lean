import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Determinants with filtered coefficient columns

Dimension bounds on nested coefficient spaces force low determinant coefficients
to vanish. The dimension profile is arbitrary and the zero series has infinite order.
-/

namespace Lambert

open Finset Matrix

noncomputable section

/-- A determinant coefficient is the sum of determinants formed by choosing one
coefficient order per column with the prescribed total order. -/
theorem powerSeries_coeff_det {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (PowerSeries R)) (k : ℕ) :
    PowerSeries.coeff k A.det =
      ∑ r ∈ finsuppAntidiag (univ : Finset ι) k,
        Matrix.det (fun i j => PowerSeries.coeff (r j) (A i j)) := by
  simp only [Matrix.det_apply, Units.smul_def, map_sum, map_zsmul, PowerSeries.coeff_prod,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro r _
  exact (Matrix.det_apply (fun i j => PowerSeries.coeff (r j) (A i j))).symm

private theorem sum_high_counts_le {ι : Type*} [Fintype ι]
    (r : ι → ℕ) (T : ℕ) :
    ∑ s ∈ range T, (univ.filter (fun j => s < r j)).card ≤ ∑ j, r j := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  calc
    ∑ s ∈ range T, (if s < r j then 1 else 0) =
        ((range T).filter (fun s => s < r j)).card := by simp
    _ ≤ (range (r j)).card := Finset.card_le_card (by simp +contextual [Finset.subset_iff])
    _ = r j := card_range _

/-- Independent vectors in a nested filtration have total assigned order at least
the sum of the dimension deficits at any finite set of initial levels. -/
theorem filtered_independent_sum_orders {K ι : Type*} [Field K] [Fintype ι]
    (U : ℕ → Submodule K (ι → K)) (hU : Monotone U)
    (v : ι → ι → K) (r : ι → ℕ) (hv : LinearIndependent K v)
    (hmem : ∀ j, v j ∈ U (r j)) (T : ℕ) :
    (∑ s ∈ range T, (Fintype.card ι - Module.finrank K (U s))) ≤ ∑ j, r j := by
  classical
  have hc (s : ℕ) : (univ.filter (fun j => r j ≤ s)).card ≤ Module.finrank K (U s) := by
    let S := univ.filter (fun j => r j ≤ s)
    let w : S → U s := fun j => ⟨v j, hU (mem_filter.mp j.property).2 (hmem j)⟩
    have hw : LinearIndependent K w :=
      LinearIndependent.of_comp (U s).subtype (hv.comp (fun j : S => j.val) Subtype.val_injective)
    simpa only [Fintype.card_coe] using hw.fintype_card_le_finrank
  calc
    _ ≤ ∑ s ∈ range T, (univ.filter (fun j => s < r j)).card := by
      apply sum_le_sum
      intro s _
      have hp := Finset.card_filter_add_card_filter_not
        (s := (univ : Finset ι)) (p := fun j => r j ≤ s)
      simp only [not_le, card_univ] at hp
      have := hc s
      omega
    _ ≤ _ := sum_high_counts_le r T

/-- Nested spaces containing all coefficient columns give a determinant order
bound equal to the sum of their dimension deficits. -/
theorem powerSeries_det_order_ge_filtration {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι (PowerSeries K))
    (U : ℕ → Submodule K (ι → K)) (hU : Monotone U)
    (hmem : ∀ r j, (fun i => PowerSeries.coeff r (A i j)) ∈ U r) (T : ℕ) :
    (↑(∑ s ∈ range T, (Fintype.card ι - Module.finrank K (U s))) : ℕ∞) ≤
      A.det.order := by
  apply PowerSeries.nat_le_order
  intro k hk
  rw [powerSeries_coeff_det]
  apply sum_eq_zero
  intro r hr
  by_contra hn
  have hi := Matrix.linearIndependent_cols_of_det_ne_zero hn
  have hb := filtered_independent_sum_orders U hU
    (fun j i => PowerSeries.coeff (r j) (A i j)) r hi (fun j => hmem (r j) j) T
  have he : (∑ j, r j) = k := (mem_finsuppAntidiag.mp hr).1
  exact (not_le_of_gt hk) (he ▸ hb)

/-- Any upper bounds for the dimensions of nested coefficient spaces give the
corresponding sum-of-deficits lower bound for determinant order. -/
theorem powerSeries_det_order_ge_profile {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι (PowerSeries K))
    (U : ℕ → Submodule K (ι → K)) (hU : Monotone U)
    (hmem : ∀ r j, (fun i => PowerSeries.coeff r (A i j)) ∈ U r)
    (d : ℕ → ℕ) (hd : ∀ r, Module.finrank K (U r) ≤ d r) (T : ℕ) :
    (↑(∑ s ∈ range T, (Fintype.card ι - d s)) : ℕ∞) ≤ A.det.order := by
  refine le_trans ?_ (powerSeries_det_order_ge_filtration A U hU hmem T)
  exact_mod_cast (sum_le_sum fun s _ => Nat.sub_le_sub_left (hd s) _)

/-- Adding arbitrary combinations of the last columns to the first columns preserves a determinant. -/
theorem det_add_tail_columns {R : Type*} [CommRing R] (h d : ℕ)
    (A : Matrix (Fin (h + d)) (Fin (h + d)) R) (c : Matrix (Fin d) (Fin h) R) :
    (Matrix.of fun i j => Fin.addCases
      (fun r => A i (Fin.castAdd d r) + ∑ k : Fin d, A i (Fin.natAdd h k) * c k r)
      (fun r => A i (Fin.natAdd h r)) j).det = A.det := by
  let U := (Matrix.fromBlocks (1 : Matrix (Fin h) (Fin h) R) 0 c
    (1 : Matrix (Fin d) (Fin d) R)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  have hu : U.det = 1 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]
    simp
  have he : (Matrix.of fun i j => Fin.addCases
      (fun r => A i (Fin.castAdd d r) + ∑ k : Fin d, A i (Fin.natAdd h k) * c k r)
      (fun r => A i (Fin.natAdd h r)) j) = A * U := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    refine Fin.addCases ?_ ?_ j
    · intro r
      simp [U, Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.one_apply]
    · intro r
      simp [U, Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.one_apply]
  rw [he, Matrix.det_mul, hu, mul_one]

/-- A rectangular zero residue block forces determinant order at least the sum of its side lengths minus the matrix size. -/
theorem powerSeries_det_order_ge_rectangular_zero_block {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι (PowerSeries K)) (s c : Finset ι)
    (hz : ∀ i ∈ s, ∀ j ∈ c, PowerSeries.coeff 0 (A i j) = 0) :
    (↑(s.card + c.card - Fintype.card ι) : ℕ∞) ≤ A.det.order := by
  classical
  apply PowerSeries.nat_le_order
  intro k hk
  rw [powerSeries_coeff_det]
  apply sum_eq_zero
  intro r hr
  by_contra hd
  have hd' : (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ •
      ∏ j, PowerSeries.coeff (r j) (A (σ j) j)) ≠ 0 := by
    intro he
    apply hd
    exact (Matrix.det_apply (fun i j => PowerSeries.coeff (r j) (A i j))).trans he
  obtain ⟨σ, _, hσ⟩ := exists_ne_zero_of_sum_ne_zero hd'
  have hp : (∏ j, PowerSeries.coeff (r j) (A (σ j) j)) ≠ 0 := by
    intro he
    rw [he, smul_zero] at hσ
    exact hσ rfl
  let t := s.map σ.symm.toEmbedding
  have ht : t.card = s.card := card_map _
  have hmem (j : ι) : j ∈ t ↔ σ j ∈ s := by simp [t]
  have hpos (j : ι) (hj : j ∈ c ∩ t) : 1 ≤ r j := by
    have hj1 := (mem_inter.mp hj).1
    have hj2 := (hmem j).mp (mem_inter.mp hj).2
    by_contra hn
    have hr0 : r j = 0 := by omega
    apply hp
    apply prod_eq_zero (mem_univ j)
    rw [hr0, hz _ hj2 _ hj1]
  have hcount : (c ∩ t).card ≤ ∑ j, r j := by
    calc
      _ = ∑ j ∈ c ∩ t, 1 := by simp
      _ ≤ ∑ j ∈ c ∩ t, r j := sum_le_sum hpos
      _ ≤ ∑ j, r j := sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hcard := card_union_add_card_inter c t
  have hu : (c ∪ t).card ≤ Fintype.card ι := card_le_univ _
  have he : (∑ j, r j) = k := (mem_finsuppAntidiag.mp hr).1
  omega

end

end Lambert
