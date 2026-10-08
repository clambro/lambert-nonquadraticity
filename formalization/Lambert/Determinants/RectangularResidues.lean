import Lambert.Determinants.LocalMap
import Lambert.Determinants.Determinant
import Lambert.Determinants.TaylorFiltration

/-!
# Residue cancellation by the polynomial columns

Adding multiples of the unregularized polynomial columns cancels the harmonic
row residue whenever its residue class is represented among those columns.
-/
namespace Lambert
noncomputable section
open PowerSeries Matrix Finset
open scoped Classical
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The surviving shifted rows have positive harmonic index and an unrepresented residue class. -/
def lambertRectangularResidualCount (h d s n : ℕ) : ℕ :=
  (univ.filter (fun r : Fin h => n ≤ r.val + s ∧ d ≤ (r.val + s) % n)).card

end
end Lambert
