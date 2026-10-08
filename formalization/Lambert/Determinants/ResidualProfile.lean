import Lambert.Determinants.RectangularResidues
import Lambert.Arithmetic.ResidueIntervalFormula

/-! # Residue-prefix formulas for Lambert window profiles -/
namespace Lambert
noncomputable section
open Finset
open scoped Classical

/-- The harmonic-positive residue prefix counts the unrepresented classes below its endpoint. -/
def lambertResidualPrefix (M d n : ℕ) : ℕ :=
  ∑ v ∈ range M, if n ≤ v ∧ d ≤ v%n then 1 else 0

/-- A translated window's surviving residue count is the difference of its two prefix counts. -/
theorem lambertRectangularResidualCount_prefix (h d s n : ℕ) :
    lambertRectangularResidualCount h d s n + lambertResidualPrefix s d n =
      lambertResidualPrefix (s+h) d n := by
  rw [lambertRectangularResidualCount, card_eq_sum_ones, sum_filter]
  rw [lambertResidualPrefix, lambertResidualPrefix, sum_range_add]
  rw [Fin.sum_univ_eq_sum_range (fun r => if n ≤ r+s ∧ d ≤ (r+s)%n then 1 else 0)]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro r _
  rw [Nat.add_comm s]

/-- A prefix ending in the initial harmonic period contributes no surviving residues. -/
theorem lambertResidualPrefix_eq_zero_of_le (M d n : ℕ) (hM : M ≤ n) :
    lambertResidualPrefix M d n=0 := by
  apply sum_eq_zero
  intro v hv
  simp [show ¬n ≤ v by have := mem_range.mp hv; omega]

/-- Representing every residue class leaves no residual prefix. -/
theorem lambertResidualPrefix_eq_zero_of_le_offset (M d n : ℕ) (hn : 0 < n) (hd : n ≤ d) :
    lambertResidualPrefix M d n=0 := by
  apply sum_eq_zero
  intro v _
  have hm := Nat.mod_lt v hn
  simp [show ¬d ≤ v%n by omega]

/-- Within a positive harmonic period, the residue prefix has an explicit affine part and one positive part. -/
theorem lambertResidualPrefix_cell (M d n m : ℕ) (hn : 0 < n) (hd : d ≤ n)
    (hm : 0 < m) (hlo : m*n ≤ M) (hhi : M ≤ (m+1)*n) :
    (lambertResidualPrefix M d n : ℝ) =
      ((m : ℝ)-1)*((n : ℝ)-d)+max ((M : ℝ)-m*n-d) 0 :=
  sum_positive_residue_tail_cell M n d m hn hd hm hlo hhi

end
end Lambert
