import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Rational affine certificates on homogeneous real intervals -/
namespace Lambert

/-- A rational affine form records the coefficients of a scale and an index. -/
abbrev RationalAffine := ℚ × ℚ

/-- A rational affine form is evaluated homogeneously in the scale and index. -/
def RationalAffine.eval (f : RationalAffine) (N n : ℝ) : ℝ := f.1*N+f.2*n

/-- Nonnegativity at both rational endpoints proves nonnegativity throughout the homogeneous interval. -/
theorem RationalAffine.nonneg_of_endpoints (f : RationalAffine) (l u : ℚ)
    (hl : 0 ≤ f.1+f.2*l) (hu : 0 ≤ f.1+f.2*u)
    (N n : ℝ) (hN : 0 ≤ N) (hnl : (l : ℝ)*N ≤ n) (hnu : n ≤ (u : ℝ)*N) :
    0 ≤ f.eval N n := by
  have hlR : 0 ≤ (f.1 : ℝ)+(f.2 : ℝ)*l := by exact_mod_cast hl
  have huR : 0 ≤ (f.1 : ℝ)+(f.2 : ℝ)*u := by exact_mod_cast hu
  dsimp [eval]
  by_cases hs : 0 ≤ (f.2 : ℝ)
  · nlinarith [mul_nonneg hlR hN, mul_nonneg hs (sub_nonneg.mpr hnl)]
  · nlinarith [mul_nonneg huR hN, mul_nonneg (neg_nonneg.mpr (le_of_not_ge hs))
      (sub_nonneg.mpr hnu)]

/-- Comparing two affine forms at both endpoints controls their ordering on the whole interval. -/
theorem RationalAffine.le_of_endpoints (f g : RationalAffine) (l u : ℚ)
    (hl : f.1+f.2*l ≤ g.1+g.2*l) (hu : f.1+f.2*u ≤ g.1+g.2*u)
    (N n : ℝ) (hN : 0 ≤ N) (hnl : (l : ℝ)*N ≤ n) (hnu : n ≤ (u : ℝ)*N) :
    f.eval N n ≤ g.eval N n := by
  have he := RationalAffine.nonneg_of_endpoints (g.1-f.1,g.2-f.2) l u
    (by dsimp; linarith) (by dsimp; linarith) N n hN hnl hnu
  simp only [eval, Rat.cast_sub] at he ⊢
  linarith

end Lambert
