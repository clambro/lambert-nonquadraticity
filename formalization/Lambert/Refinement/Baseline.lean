import Lambert.Refinement.Orbit
import Lambert.Determinants.ExponentAsymptotics

/-! # Filtration baseline for the six-presentation pole envelope -/
namespace Lambert
noncomputable section
open Finset Filter Topology
open scoped Classical

/-- The original presentation gives a nonnegative odd-deficit baseline for all six-presentation clearing exponents. -/
def lambertRefinementBaseline (N n : ℕ) : ℕ :=
  500*N + (516*N-n) + ∑ r ∈ range (516*N), (516*N-(2*r+3)*n)

/-- The minimum transported clearing exponent never exceeds the original filtration baseline. -/
theorem lambertRefinementClearingExponent_le_baseline (N n : ℕ) (hn : 0 < n) :
    lambertRefinementClearingExponent N n ≤ lambertRefinementBaseline N n := by
  have hi := Finset.inf'_le (lambertRefinementOrbitExponent N n)
    (Finset.mem_univ (0 : Fin 6))
  have hf := le_max_left
    (∑ r ∈ range (516*N), (516*N-2*n*(r+1)))
    (500*N-lambertRectangularResidualCount (500*N) (16*N) (41*N) n-
      (27*N+516*N-max (27*N) n))
  have hs := sum_deficits_even_odd (516*N) n hn
  have he : (∑ r ∈ range (516*N), (516*N-2*n*(r+1))) =
      ∑ r ∈ range (516*N), (516*N-(r+1)*(2*n)) := by
    apply sum_congr rfl
    intro r _
    rw [Nat.mul_comm (2*n)]
  rw [he] at hf
  have ho : lambertRefinementOrbitExponent N n 0 =
      (500*N : ℕ) + (∑ r ∈ range (516*N), (516*N-(r+1)*n) : ℕ) -
      max (∑ r ∈ range (516*N), (516*N-(r+1)*(2*n)))
        (500*N-lambertRectangularResidualCount (500*N) (16*N) (41*N) n-
          (27*N+516*N-max (27*N) n)) := by
    simp only [lambertRefinementOrbitExponent, Matrix.cons_val_zero,
      lambertRefinementCyclotomicExponent, lambertRefinementLocalOrder,
      sum_range_zero, Nat.cast_zero, add_zero,
      show 500*N+16*N=516*N by omega, he]
  rw [ho] at hi
  unfold lambertRefinementClearingExponent lambertRefinementBaseline
  omega

/-- The filtration baseline differs from the square-window exponent by two elementary tent corrections and the rank. -/
theorem lambertRefinementBaseline_eq_square (N n : ℕ) :
    (lambertRefinementBaseline N n : ℝ) = 500*N+
      (lambertCyclotomicExponent (516*N) n : ℝ)-2*((516*N-n : ℕ) : ℝ)+
        ((516*N-2*n : ℕ) : ℝ) := by
  have he : 516*N-2*n ≤ 3*(516*N-n) := by omega
  simp only [lambertRefinementBaseline, lambertCyclotomicExponent,
    Nat.cast_add, Nat.cast_sub he, Nat.cast_mul, Nat.cast_ofNat]
  ring

end
end Lambert
