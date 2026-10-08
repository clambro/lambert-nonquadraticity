import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Maximum modulus for polynomial families in two variables -/
namespace Lambert
noncomputable section
open Polynomial Metric

/-- For a fixed second argument, evaluating an integer bivariate polynomial is an entire function of its first argument. -/
theorem integerBivariate_differentiable (p : (ℤ[X])[X]) (z : ℂ) :
    Differentiable ℂ (fun u : ℂ => (p.map (eval₂RingHom (Int.castRingHom ℂ) u)).eval z) := by
  simp only [eval_map, eval₂_eq_sum, Polynomial.sum, coe_eval₂RingHom]
  apply Differentiable.fun_sum
  intro i hi
  apply Differentiable.mul_const
  simpa only [eval_map, eval₂_eq_sum, Polynomial.sum] using ((p.coeff i).map (Int.castRingHom ℂ)).differentiable

/-- A uniform circle bound for an integer bivariate polynomial controls every base in the enclosed disk. -/
theorem integerBivariate_norm_le_on_disk (p : (ℤ[X])[X]) (z : ℂ)
    (R : ℝ) (hR : 0 < R) (B : ℝ)
    (hB : ∀ u : ℂ, ‖u‖ = R →
      ‖(p.map (eval₂RingHom (Int.castRingHom ℂ) u)).eval z‖ ≤ B)
    (u : ℂ) (hu : ‖u‖ ≤ R) :
    ‖(p.map (eval₂RingHom (Int.castRingHom ℂ) u)).eval z‖ ≤ B := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := (0 : ℂ)) (r := R))
    (integerBivariate_differentiable p z).diffContOnCl
  · intro v hv
    rw [frontier_ball (0 : ℂ) hR.ne'] at hv
    exact hB v (by simpa only [mem_sphere, dist_zero_right] using hv)
  · rw [closure_ball (0 : ℂ) hR.ne']
    simpa only [mem_closedBall, dist_zero_right] using hu
end
end Lambert
