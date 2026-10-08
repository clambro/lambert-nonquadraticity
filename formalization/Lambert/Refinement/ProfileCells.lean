import Lambert.Refinement.ProfileExpressions
import Lambert.Arithmetic.TotientAffineInterval

/-! # Certified finite corrections to the Lambert filtration baseline -/
namespace Lambert
noncomputable section
open Finset Filter Topology
open scoped Classical

/-- The uncorrected profile expression is the original rank plus the odd collision deficits. -/
def lambertRefinementBaselineExpression : LambertProfileExpression :=
  .sub (.add (.linear (500,0)) (.deficit 516 1)) (.deficit 516 2)

/-- The baseline expression agrees with the exact nonnegative filtration bound. -/
theorem lambertRefinementBaselineExpression_eval (N n : ℕ) (hn : 0<n) :
    lambertRefinementBaselineExpression.eval N n=(lambertRefinementBaseline N n : ℝ) := by
  have he := sum_deficits_even_odd (516*N) n hn
  have hR : ((∑ r ∈ range (516*N), (516*N-(r+1)*n) : ℕ) : ℝ) =
      (∑ r ∈ range (516*N), (516*N-(r+1)*(2*n) : ℕ) : ℕ)+
      (516*N-n : ℕ)+(∑ r ∈ range (516*N), (516*N-(2*r+3)*n) : ℕ) := by exact_mod_cast he
  simp only [lambertRefinementBaselineExpression, LambertProfileExpression.eval,
    RationalAffine.eval, Rat.cast_ofNat, Rat.cast_zero, zero_mul, add_zero, one_mul,
    lambertRefinementBaseline, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith

/-- A transported presentation supplies a nonnegative-part upper bound on the actual clearing exponent. -/
theorem lambertRefinementClearingExponent_le_expression (N n : ℕ) (j : Fin 6) :
    (lambertRefinementClearingExponent N n : ℝ) ≤
      max ((lambertRefinementOrbitExpression j).eval N n) 0 := by
  rw [lambertRefinementOrbitExpression_eval]
  let E := (univ : Finset (Fin 6)).inf' univ_nonempty (lambertRefinementOrbitExponent N n)
  have hi : E ≤ lambertRefinementOrbitExponent N n j := inf'_le _ (mem_univ j)
  change (E.toNat : ℝ) ≤ _
  by_cases hE : E ≤ 0
  · rw [Int.toNat_eq_zero.mpr hE, Nat.cast_zero]
    exact le_max_right _ _
  · have he : (E.toNat : ℝ)=(E : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (le_of_not_ge hE)
    rw [he]
    exact (show (E : ℝ) ≤ (lambertRefinementOrbitExponent N n j : ℝ) by exact_mod_cast hi).trans
      (le_max_left _ _)

/-- A presentation's improvement is measured relative to the nonnegative filtration baseline. -/
def lambertRefinementCorrectionExpression (j : Fin 6) : LambertProfileExpression :=
  .sub lambertRefinementBaselineExpression (.max (lambertRefinementOrbitExpression j) (.linear (0,0)))

/-- A finite profile cell records an interval, a presentation, its exact correction, and a rounded-down integral certificate. -/
structure LambertRefinementProfileCell where
  lower : ℚ
  upper : ℚ
  presentation : Fin 6
  correction : RationalAffine
  integralNumerator : ℕ
  deriving DecidableEq

/-- The integral of a cell's affine correction is a rational number. -/
def LambertRefinementProfileCell.integral (c : LambertRefinementProfileCell) : ℚ :=
  c.correction.1*(c.upper^2-c.lower^2)/2+c.correction.2*(c.upper^3-c.lower^3)/3

/-- Valid cells certify an exact nonnegative correction inside the root-order cutoff and a lower integral rounded to twelve decimal places. -/
def LambertRefinementProfileCell.Valid (c : LambertRefinementProfileCell) : Prop :=
  0<c.lower ∧ c.lower<c.upper ∧ c.upper≤543 ∧
  (lambertRefinementCorrectionExpression c.presentation).affineOn c.lower c.upper=some c.correction ∧
  0≤c.correction.1+c.correction.2*c.lower ∧
  0≤c.correction.1+c.correction.2*c.upper ∧
  (c.integralNumerator : ℚ)/1000000000000 ≤ c.integral

instance (c : LambertRefinementProfileCell) : Decidable c.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Every valid cell subtracts its certified correction from the clearing-exponent bound throughout its interval. -/
theorem LambertRefinementProfileCell.bound (c : LambertRefinementProfileCell) (hc : c.Valid)
    (N n : ℕ) (hn : 0<n) (hnl : (c.lower : ℝ)*N ≤ n) (hnu : (n : ℝ) ≤ (c.upper : ℝ)*N) :
    (lambertRefinementClearingExponent N n : ℝ)+c.correction.eval N n ≤ lambertRefinementBaseline N n := by
  have he := LambertProfileExpression.affineOn_sound _ c.lower c.upper c.correction hc.2.2.2.1 N n hn hnl hnu
  have hb := lambertRefinementClearingExponent_le_expression N n c.presentation
  simp only [lambertRefinementCorrectionExpression, LambertProfileExpression.eval,
    RationalAffine.eval, Rat.cast_zero, zero_mul, add_zero] at he
  rw [lambertRefinementBaselineExpression_eval N n hn] at he
  dsimp [RationalAffine.eval]
  linarith

/-- A cell contributes its affine correction on its half-open scaled interval and zero elsewhere. -/
def LambertRefinementProfileCell.value (c : LambertRefinementProfileCell) (N n : ℕ) : ℝ :=
  if n ∈ Ioc ⌊(c.lower : ℝ)*N⌋₊ ⌊(c.upper : ℝ)*N⌋₊ then c.correction.eval N n else 0

/-- Membership in a scaled cell supplies the positive root order and its real endpoint inequalities. -/
theorem LambertRefinementProfileCell.mem_bounds (c : LambertRefinementProfileCell) (N n : ℕ)
    (hn : n ∈ Ioc ⌊(c.lower : ℝ)*N⌋₊ ⌊(c.upper : ℝ)*N⌋₊) :
    0<n ∧ (c.lower : ℝ)*N < n ∧ (n : ℝ) ≤ (c.upper : ℝ)*N := by
  obtain ⟨hl,hu⟩ := mem_Ioc.mp hn
  have hn0 : 0<n := by omega
  exact ⟨hn0, (Nat.floor_lt' hn0.ne').mp hl, (Nat.le_floor_iff' hn0.ne').mp hu⟩

/-- Ordered profile cells cannot both contain the same scaled root order. -/
theorem LambertRefinementProfileCell.disjoint (c d : LambertRefinementProfileCell)
    (hcd : c.upper≤d.lower) (N n : ℕ)
    (hc : n ∈ Ioc ⌊(c.lower : ℝ)*N⌋₊ ⌊(c.upper : ℝ)*N⌋₊) :
    n ∉ Ioc ⌊(d.lower : ℝ)*N⌋₊ ⌊(d.upper : ℝ)*N⌋₊ := by
  intro hd
  have hb := (c.mem_bounds N n hc).2.2
  have ha := (d.mem_bounds N n hd).2.1
  have hR : (c.upper : ℝ)≤d.lower := by exact_mod_cast hcd
  have he := mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg N : (0 : ℝ)≤N)
  linarith

/-- Disjoint valid cells subtract their total correction without counting any root order twice. -/
theorem lambertRefinementProfileCells_pointwise (cells : List LambertRefinementProfileCell)
    (hv : ∀ c∈cells, c.Valid) (ho : cells.Pairwise (fun c d => c.upper≤d.lower))
    (N n : ℕ) (hn : 0<n) :
    (lambertRefinementClearingExponent N n : ℝ)+(cells.map (fun c => c.value N n)).sum ≤
      lambertRefinementBaseline N n := by
  induction cells with
  | nil => simpa using (show (lambertRefinementClearingExponent N n : ℝ) ≤
      lambertRefinementBaseline N n by exact_mod_cast lambertRefinementClearingExponent_le_baseline N n hn)
  | cons c cs ih =>
    have hp := List.pairwise_cons.mp ho
    have hc := hv c (by simp)
    have hcs : ∀ d∈cs, d.Valid := fun d hd => hv d (by simp [hd])
    simp only [List.map_cons, List.sum_cons]
    by_cases hmem : n ∈ Ioc ⌊(c.lower : ℝ)*N⌋₊ ⌊(c.upper : ℝ)*N⌋₊
    · have hz : (cs.map (fun d => d.value N n)).sum=0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hx
        exact if_neg (c.disjoint d (hp.1 d hd) N n hmem)
      rw [hz, add_zero, LambertRefinementProfileCell.value, if_pos hmem]
      have hb := c.mem_bounds N n hmem
      exact c.bound hc N n hn hb.2.1.le hb.2.2
    · rw [LambertRefinementProfileCell.value, if_neg hmem, zero_add]
      exact ih hcs hp.2

/-- A valid cell's totient-weighted correction has six times its affine integral as cubic coefficient, divided by pi squared. -/
theorem LambertRefinementProfileCell.weighted_tendsto (c : LambertRefinementProfileCell)
    (hc : c.Valid) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc ⌊(c.lower : ℝ)*N⌋₊ ⌊(c.upper : ℝ)*N⌋₊,
      (Nat.totient n : ℝ)*c.correction.eval N n)/(N : ℝ)^3)
      atTop (𝓝 (6*(c.integral : ℝ)/Real.pi^2)) := by
  have hl : (0 : ℝ)<c.lower := by exact_mod_cast hc.1
  have hlu : (c.lower : ℝ)≤c.upper := by exact_mod_cast hc.2.1.le
  have he := totient_affine_interval_tendsto c.lower c.upper c.correction.1 c.correction.2 hl hlu
  convert he using 1
  · dsimp [RationalAffine.eval]
  · congr 1
    dsimp [integral]
    push_cast
    ring

end
end Lambert
