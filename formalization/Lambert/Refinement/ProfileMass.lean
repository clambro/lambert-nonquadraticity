import Lambert.Refinement.ProfileData
import Lambert.Refinement.BaselineLimit

/-! # Totient-weighted savings of the finite Lambert profile certificate -/
namespace Lambert
noncomputable section
open Finset Filter Topology
open scoped Classical

/-- A cell's weighted correction is summed over its exact half-open scaled interval. -/
def LambertRefinementProfileCell.weightedSum (c : LambertRefinementProfileCell) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc ⌊(c.lower : ℝ)*N⌋₊ ⌊(c.upper : ℝ)*N⌋₊,
    (Nat.totient n : ℝ)*c.correction.eval N n

/-- Every valid cell's weighted sum equals its zero-extended sum over the full pole cutoff. -/
theorem LambertRefinementProfileCell.weightedSum_eq (c : LambertRefinementProfileCell)
    (hc : c.Valid) (N : ℕ) :
    c.weightedSum N=∑ n ∈ Icc 1 (543*N), (Nat.totient n : ℝ)*c.value N n := by
  let s := Ioc ⌊(c.lower : ℝ)*N⌋₊ ⌊(c.upper : ℝ)*N⌋₊
  have hs : s ⊆ Icc 1 (543*N) := by
    intro n hn
    have hb := c.mem_bounds N n hn
    have hu : (c.upper : ℝ)≤543 := by exact_mod_cast hc.2.2.1
    have he := mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg N : (0 : ℝ)≤N)
    have hnn : n≤543*N := by exact_mod_cast (show (n : ℝ)≤543*N by linarith)
    exact mem_Icc.mpr ⟨hb.1,hnn⟩
  have he := sum_subset hs (f := fun n => (Nat.totient n : ℝ)*c.value N n)
    (fun n _ hn => by dsimp [s] at hn; simp only [LambertRefinementProfileCell.value, if_neg hn, mul_zero])
  rw [← he]
  apply sum_congr rfl
  intro n hn
  rw [LambertRefinementProfileCell.value, if_pos hn]

/-- The total finite correction is the sum of the certified cells' weighted arithmetic. -/
def lambertRefinementProfileMass (N : ℕ) : ℝ :=
  (lambertRefinementProfileCells.map (fun c => c.weightedSum N)).sum

/-- The exact integral coefficient of the finite profile correction is the sum of its rational cell integrals. -/
def lambertRefinementProfileIntegral : ℝ :=
  (lambertRefinementProfileCells.map (fun c => (c.integral : ℝ))).sum

/-- The checked rounded integral certificates give the stated rational lower bound on the full correction integral. -/
theorem lambertRefinementProfileIntegral_lower :
    (122503422987/4000 : ℝ) ≤ lambertRefinementProfileIntegral := by
  have hs := List.sum_le_sum (l := lambertRefinementProfileCells)
    (f := fun c => (c.integralNumerator : ℝ)/1000000000000)
    (g := fun c => (c.integral : ℝ)) (fun c hc => by
      have he := (lambertRefinementProfileCells_valid c hc).2.2.2.2.2.2
      have hr : (((c.integralNumerator : ℚ)/1000000000000 : ℚ) : ℝ) ≤ (c.integral : ℝ) :=
        Rat.cast_le.mpr he
      simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hr)
  have he (cs : List LambertRefinementProfileCell) :
      (cs.map (fun c => (c.integralNumerator : ℝ)/1000000000000)).sum =
        ((cs.map LambertRefinementProfileCell.integralNumerator).sum : ℕ)/ (1000000000000 : ℝ) := by
    induction cs with
    | nil => simp
    | cons c cs ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]; ring
  rw [he] at hs
  have hn : (30625855746750000000 : ℝ) ≤
      ((lambertRefinementProfileCells.map LambertRefinementProfileCell.integralNumerator).sum : ℕ) :=
    by exact_mod_cast lambertRefinementProfileCells_integral_numerators
  dsimp [lambertRefinementProfileIntegral]
  linarith

/-- The finite corrected envelope bounds the actual totient-weighted clearing exponents at every scale. -/
theorem lambertRefinementProfileMass_bound (N : ℕ) :
    (∑ n ∈ Icc 1 (543*N), (Nat.totient n : ℝ)*lambertRefinementClearingExponent N n)+
      lambertRefinementProfileMass N ≤
        ∑ n ∈ Icc 1 (543*N), (Nat.totient n : ℝ)*lambertRefinementBaseline N n := by
  have hsum (cs : List LambertRefinementProfileCell) (hv : ∀ c∈cs, c.Valid) :
      (cs.map (fun c => c.weightedSum N)).sum =
        ∑ n ∈ Icc 1 (543*N), (Nat.totient n : ℝ)*(cs.map (fun c => c.value N n)).sum := by
    induction cs with
    | nil => simp
    | cons c cs ih =>
      rw [List.map_cons, List.sum_cons, c.weightedSum_eq (hv c (by simp)) N,
        ih (fun d hd => hv d (by simp [hd]))]
      simp only [List.map_cons, List.sum_cons, mul_add, sum_add_distrib]
  rw [lambertRefinementProfileMass, hsum lambertRefinementProfileCells lambertRefinementProfileCells_valid,
    ← sum_add_distrib]
  apply sum_le_sum
  intro n hn
  have he := lambertRefinementProfileCells_pointwise lambertRefinementProfileCells
    lambertRefinementProfileCells_valid lambertRefinementProfileCells_ordered N n (mem_Icc.mp hn).1
  simpa only [mul_add] using mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (Nat.totient n) : (0 : ℝ)≤Nat.totient n)

/-- The finite correction mass has cubic coefficient six times its exact integral divided by pi squared. -/
theorem lambertRefinementProfileMass_tendsto :
    Tendsto (fun N : ℕ => lambertRefinementProfileMass N/(N : ℝ)^3) atTop
      (𝓝 (6*lambertRefinementProfileIntegral/Real.pi^2)) := by
  have hsum (cs : List LambertRefinementProfileCell) (hv : ∀ c∈cs, c.Valid) :
      Tendsto (fun N : ℕ => (cs.map (fun c => c.weightedSum N)).sum/(N : ℝ)^3)
        atTop (𝓝 (6*(cs.map (fun c => (c.integral : ℝ))).sum/Real.pi^2)) := by
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have he := (c.weighted_tendsto (hv c (by simp)) ).add
        (ih (fun d hd => hv d (by simp [hd])))
      convert he using 1
      · funext N
        simp only [List.map_cons, List.sum_cons, add_div, LambertRefinementProfileCell.weightedSum]
      · simp only [List.map_cons, List.sum_cons]
        congr 1
        ring
  exact hsum lambertRefinementProfileCells lambertRefinementProfileCells_valid

end
end Lambert
