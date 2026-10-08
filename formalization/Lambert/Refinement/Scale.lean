import Lambert.Refinement.ProfileMass
import Lambert.Refinement.EndpointLimit
import Lambert.Refinement.ScaleLog
import Mathlib.Analysis.Real.Pi.Bounds

/-! # A certified cubic majorant for the six-presentation integer scale -/
namespace Lambert
noncomputable section
open Finset Filter Topology

/-- The rationally certified arithmetic constant is the endpoint cost plus the corrected cyclotomic mass. -/
def lambertRefinementArithmeticConstant : ℝ :=
  80135650/3+517036731039/(2000*Real.pi^2)

/-- The exact finite profile gives an intermediate arithmetic constant before rational rounding. -/
def lambertRefinementProfileConstant : ℝ :=
  80135650/3+(442273500-6*lambertRefinementProfileIntegral)/Real.pi^2

/-- Rounding each interval integral down only increases the advertised arithmetic constant. -/
theorem lambertRefinementProfileConstant_le :
    lambertRefinementProfileConstant ≤ lambertRefinementArithmeticConstant := by
  have hp : (0 : ℝ)<Real.pi^2 := by positivity
  have hi := lambertRefinementProfileIntegral_lower
  unfold lambertRefinementProfileConstant lambertRefinementArithmeticConstant
  have he : 517036731039/(2000*Real.pi^2)=(517036731039/2000)/Real.pi^2 := by ring
  rw [he]
  have hd : (442273500-6*lambertRefinementProfileIntegral)/Real.pi^2 ≤
      (517036731039/2000)/Real.pi^2 := (div_le_div_iff_of_pos_right hp).mpr (by linarith)
  linarith

/-- The corrected finite profile bounds the clearing degree at each scale. -/
def lambertRefinementDegreeMajorant (N : ℕ) : ℝ :=
  lambertRefinementClearingZeroExponent N+
    (∑ n ∈ Icc 1 (543*N), (Nat.totient n : ℝ)*lambertRefinementBaseline N n)-
      lambertRefinementProfileMass N

/-- The corrected clearing-degree majorant has the expected cubic profile limit. -/
theorem lambertRefinementDegreeMajorant_tendsto :
    Tendsto (fun N : ℕ => lambertRefinementDegreeMajorant N/(N : ℝ)^3) atTop
      (𝓝 lambertRefinementProfileConstant) := by
  have he := (lambertRefinementClearingZeroExponent_tendsto.add
    (lambertRefinementBaseline_totient_tendsto)).sub (lambertRefinementProfileMass_tendsto)
  convert he using 1
  · funext N
    simp only [lambertRefinementDegreeMajorant, add_div, sub_div]
  · unfold lambertRefinementProfileConstant
    congr 1
    ring

private theorem clearing_sum_endpoint (w : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ico 1 (543*N), w n*lambertRefinementClearingExponent N n)=
      ∑ n ∈ Icc 1 (543*N), w n*lambertRefinementClearingExponent N n := by
  apply sum_subset
  · intro n hn
    exact mem_Icc.mpr ⟨(mem_Ico.mp hn).1,(mem_Ico.mp hn).2.le⟩
  · intro n hn hnot
    have he : n=543*N := by simp only [mem_Icc,mem_Ico] at hn hnot; omega
    subst n
    rw [lambertRefinementClearingExponent_eq_zero N (543*N) le_rfl, Nat.cast_zero, mul_zero]

/-- The logarithmic scale majorant includes the uniform cyclotomic error and the nonnegative rational-rounding allowance. -/
def lambertRefinementScaleMajorant (a b : ℤ) (N : ℕ) : ℝ :=
  lambertRefinementDegreeMajorant N*Real.log a+
    (1-((a : ℝ)/b)⁻¹)⁻¹^2*(∑ n ∈ Icc 1 (543*N), (lambertRefinementBaseline N n : ℝ))+
    (lambertRefinementArithmeticConstant-lambertRefinementProfileConstant)*Real.log a*(N : ℝ)^3

/-- The explicit majorant bounds the logarithm of the exact integer scale at every positive ordered rational base. -/
theorem lambertRefinementScaleMajorant_bound (a b : ℤ) (hb : 0<b) (hab : b<a) (N : ℕ) :
    Real.log (lambertRefinementIntegerScale N a b : ℝ) ≤ lambertRefinementScaleMajorant a b N := by
  have he := lambertRefinementIntegerScale_log_error N a b hb hab
  have hs := clearing_sum_endpoint (fun n => (Nat.totient n : ℝ)) N
  have h1 := clearing_sum_endpoint (fun _ => (1 : ℝ)) N
  simp only [one_mul] at h1
  rw [hs,h1] at he
  have hm := lambertRefinementProfileMass_bound N
  have hbsl : (∑ n ∈ Icc 1 (543*N), (lambertRefinementClearingExponent N n : ℝ)) ≤
      ∑ n ∈ Icc 1 (543*N), (lambertRefinementBaseline N n : ℝ) := by
    apply sum_le_sum
    intro n hn
    exact_mod_cast lambertRefinementClearingExponent_le_baseline N n (mem_Icc.mp hn).1
  have ha : 0≤Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast (show (1 : ℤ)≤a by omega))
  have hdegree : ((lambertRefinementClearingZeroExponent N : ℝ)+
      ∑ n ∈ Icc 1 (543*N), (Nat.totient n : ℝ)*lambertRefinementClearingExponent N n) ≤
        lambertRefinementDegreeMajorant N := by dsimp [lambertRefinementDegreeMajorant]; linarith
  have hd := mul_le_mul_of_nonneg_right hdegree ha
  have herr := mul_le_mul_of_nonneg_left hbsl (sq_nonneg ((1-((a : ℝ)/b)⁻¹)⁻¹))
  have hpad : 0≤(lambertRefinementArithmeticConstant-lambertRefinementProfileConstant)*Real.log a*(N : ℝ)^3 :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr lambertRefinementProfileConstant_le) ha) (by positivity)
  have hl := (le_abs_self _).trans he
  unfold lambertRefinementScaleMajorant
  linarith

/-- The scale majorant has the advertised cubic coefficient. -/
theorem lambertRefinementScaleMajorant_tendsto (a b : ℤ) :
    Tendsto (fun N : ℕ => lambertRefinementScaleMajorant a b N/(N : ℝ)^3) atTop
      (𝓝 (lambertRefinementArithmeticConstant*Real.log a)) := by
  have he := (((lambertRefinementDegreeMajorant_tendsto).mul_const (Real.log a)).add
    (lambertRefinementBaseline_sum_tendsto.const_mul ((1-((a : ℝ)/b)⁻¹)⁻¹^2))).add
      (tendsto_const_nhds (x := (lambertRefinementArithmeticConstant-lambertRefinementProfileConstant)*Real.log a))
  have hc : lambertRefinementProfileConstant*Real.log a+
      (1-((a : ℝ)/b)⁻¹)⁻¹^2*0+
      (lambertRefinementArithmeticConstant-lambertRefinementProfileConstant)*Real.log a =
        lambertRefinementArithmeticConstant*Real.log a := by ring
  rw [hc] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  unfold lambertRefinementScaleMajorant
  field_simp

/-- The exact certified clearing-to-decay ratio gives an irrationality cutoff strictly exceeding 0.573290. -/
theorem lambertRefinement_cutoff :
    lambertRefinementArithmeticConstant/(371952500/3) < (426710/1000000 : ℝ) := by
  have hp := Real.pi_gt_d20
  have hpos : (0 : ℝ)<Real.pi^2 := by positivity
  unfold lambertRefinementArithmeticConstant
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ)<371952500/3)).mpr
  have he : 517036731039/(2000*Real.pi^2) < (426710/1000000)*(371952500/3)-80135650/3 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ)<2000*Real.pi^2)).mpr
    nlinarith [sq_nonneg (Real.pi-3.14159265358979323846)]
  linarith

end
end Lambert
