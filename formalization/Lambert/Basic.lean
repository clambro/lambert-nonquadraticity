import Lambert.Analysis.GeometricMarkov

/-! # The Lambert series and its convergence -/
namespace Lambert
noncomputable section
/-- The real Lambert value at a base greater than one is the reciprocal power-difference series. -/
def lambertValue (q : ℝ) : ℝ := ∑' n : ℕ, 1 / (q ^ (n + 1) - 1)

/-- The Lambert reciprocal series converges at every real base greater than one. -/
theorem summable_lambertValue (q : ℝ) (hq : 1 < q) :
    Summable (fun n : ℕ => 1 / (q ^ (n + 1) - 1)) := by
  have hu : 0 < q⁻¹ := inv_pos.mpr (zero_lt_one.trans hq)
  have hu1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hs := summable_geometricMarkov q⁻¹ 1 hu.le hu1 hu1
  have he (n : ℕ) : q⁻¹ ^ (n + 1) / (1 - q⁻¹ ^ (n + 1)) = 1 / (q ^ (n + 1) - 1) := by
    simpa only [inv_inv, one_div] using geometricReciprocalMoment_inverse_base q⁻¹ hu.ne' (n + 1)
  simpa only [he] using hs

end
end Lambert
