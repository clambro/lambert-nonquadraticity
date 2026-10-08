import Lambert.Arithmetic.AffineInterval
import Lambert.Arithmetic.DeficitFormula
import Lambert.Determinants.ResidualProfile

/-! # Exact affine certificates for Lambert pole profiles -/
namespace Lambert
noncomputable section
open Finset

/-- A pole-profile expression is assembled from homogeneous affine forms, deficit sums, residue prefixes, and maxima. -/
inductive LambertProfileExpression where
  | linear (f : RationalAffine)
  | deficit (K c : ℕ)
  | residue (M d : ℕ)
  | add (f g : LambertProfileExpression)
  | sub (f g : LambertProfileExpression)
  | max (f g : LambertProfileExpression)
  deriving Inhabited

/-- Profile expressions evaluate the exact finite arithmetic at the chosen scale and root order. -/
def LambertProfileExpression.eval (N n : ℕ) : LambertProfileExpression → ℝ
  | .linear f => f.eval N n
  | .deficit K c => (∑ r ∈ range (K*N), (K*N-(r+1)*(c*n)) : ℕ)
  | .residue M d => (lambertResidualPrefix (M*N) (d*N) n : ℕ)
  | .add f g => f.eval N n+g.eval N n
  | .sub f g => f.eval N n-g.eval N n
  | .max f g => Max.max (f.eval N n) (g.eval N n)

private def affineMax (l u : ℚ) (f g : RationalAffine) : Option RationalAffine :=
  if g.1+g.2*l ≤ f.1+f.2*l ∧ g.1+g.2*u ≤ f.1+f.2*u then some f
  else if f.1+f.2*l ≤ g.1+g.2*l ∧ f.1+f.2*u ≤ g.1+g.2*u then some g
  else none

private theorem affineMax_sound (l u : ℚ) (f g a : RationalAffine)
    (ha : affineMax l u f g=some a) (N n : ℝ) (hN : 0 ≤ N)
    (hnl : (l : ℝ)*N ≤ n) (hnu : n ≤ (u : ℝ)*N) :
    max (f.eval N n) (g.eval N n)=a.eval N n := by
  unfold affineMax at ha
  split at ha
  · rename_i h
    cases Option.some.inj ha
    exact max_eq_left (g.le_of_endpoints f l u h.1 h.2 N n hN hnl hnu)
  · split at ha
    · rename_i h
      cases Option.some.inj ha
      exact max_eq_right (f.le_of_endpoints g l u h.1 h.2 N n hN hnl hnu)
    · contradiction

private def deficitAffine (K c : ℕ) (l u : ℚ) : Option RationalAffine :=
  let m := ⌊(K : ℚ)/(c*((l+u)/2))⌋₊
  if 0<c ∧ (m : ℚ)*c*u ≤ K ∧ (K : ℚ) ≤ (m+1)*c*l then
    some ((m : ℚ)*K, -(m : ℚ)*(m+1)*c/2)
  else none

private theorem deficitAffine_sound (K c : ℕ) (l u : ℚ) (a : RationalAffine)
    (ha : deficitAffine K c l u=some a) (N n : ℕ) (hn : 0<n)
    (hnl : (l : ℝ)*N ≤ n) (hnu : (n : ℝ) ≤ (u : ℝ)*N) :
    LambertProfileExpression.eval N n (.deficit K c)=a.eval N n := by
  unfold deficitAffine at ha
  dsimp only at ha
  split at ha
  · rename_i h
    cases Option.some.inj ha
    let m := ⌊(K : ℚ)/(c*((l+u)/2))⌋₊
    have hL : (m : ℝ)*c*u ≤ K := by exact_mod_cast h.2.1
    have hU : (K : ℝ) ≤ (m+1)*c*l := by exact_mod_cast h.2.2
    have hlo : m*(c*n) ≤ K*N := by
      have he := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      have hf := mul_le_mul_of_nonneg_left hnu (show (0 : ℝ) ≤ m*c by positivity)
      exact_mod_cast (show (m : ℝ)*(c*n) ≤ K*N by nlinarith)
    have hhi : K*N ≤ (m+1)*(c*n) := by
      have he := mul_le_mul_of_nonneg_right hU (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      have hf := mul_le_mul_of_nonneg_left hnl (show (0 : ℝ) ≤ (m+1)*c by positivity)
      exact_mod_cast (show (K : ℝ)*N ≤ (m+1)*(c*n) by nlinarith)
    have he := sum_deficits_affine (K*N) (c*n) m (Nat.mul_pos h.1 hn) hlo hhi
    dsimp [LambertProfileExpression.eval, RationalAffine.eval]
    push_cast at he ⊢
    dsimp [m] at he
    nlinarith
  · contradiction

private def prefixAffine (M d : ℕ) (l u : ℚ) : Option RationalAffine :=
  if u ≤ d then some (0,0)
  else if (M : ℚ) ≤ l then some (0,0)
  else
    let m := ⌊(M : ℚ)/((l+u)/2)⌋₊
    if (d : ℚ) ≤ l ∧ 0<m ∧ (m : ℚ)*u ≤ M ∧ (M : ℚ) ≤ (m+1)*l then
      (affineMax l u ((M : ℚ)-d, -(m : ℚ)) (0,0)).map
        (fun f => (-((m : ℚ)-1)*d+f.1, (m : ℚ)-1+f.2))
    else none

private theorem prefixAffine_sound (M d : ℕ) (l u : ℚ) (a : RationalAffine)
    (ha : prefixAffine M d l u=some a) (N n : ℕ) (hn : 0<n)
    (hnl : (l : ℝ)*N ≤ n) (hnu : (n : ℝ) ≤ (u : ℝ)*N) :
    LambertProfileExpression.eval N n (.residue M d)=a.eval N n := by
  unfold prefixAffine at ha
  split at ha
  · rename_i h
    cases Option.some.inj ha
    have hR : (u : ℝ) ≤ d := by exact_mod_cast h
    have hd : n ≤ d*N := by
      have := mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      exact_mod_cast (show (n : ℝ) ≤ d*N by linarith)
    simp only [LambertProfileExpression.eval, lambertResidualPrefix_eq_zero_of_le_offset _ _ _ hn hd,
      Nat.cast_zero, RationalAffine.eval, Rat.cast_zero, zero_mul, add_zero]
  · split at ha
    · rename_i h
      cases Option.some.inj ha
      have hR : (M : ℝ) ≤ l := by exact_mod_cast h
      have hM : M*N ≤ n := by
        have := mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
        exact_mod_cast (show (M : ℝ)*N ≤ n by linarith)
      simp only [LambertProfileExpression.eval, lambertResidualPrefix_eq_zero_of_le _ _ _ hM,
        Nat.cast_zero, RationalAffine.eval, Rat.cast_zero, zero_mul, add_zero]
    · dsimp only at ha
      split at ha
      · rename_i h
        let m := ⌊(M : ℚ)/((l+u)/2)⌋₊
        have hdR : (d : ℝ) ≤ l := by exact_mod_cast h.1
        have hLR : (m : ℝ)*u ≤ M := by exact_mod_cast h.2.2.1
        have hUR : (M : ℝ) ≤ (m+1)*l := by exact_mod_cast h.2.2.2
        have hd : d*N ≤ n := by
          have := mul_le_mul_of_nonneg_right hdR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
          exact_mod_cast (show (d : ℝ)*N ≤ n by linarith)
        have hlo : m*n ≤ M*N := by
          have := mul_le_mul_of_nonneg_right hLR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
          have := mul_le_mul_of_nonneg_left hnu (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
          exact_mod_cast (show (m : ℝ)*n ≤ M*N by nlinarith)
        have hhi : M*N ≤ (m+1)*n := by
          have := mul_le_mul_of_nonneg_right hUR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
          have := mul_le_mul_of_nonneg_left hnl (show (0 : ℝ) ≤ m+1 by positivity)
          exact_mod_cast (show (M : ℝ)*N ≤ (m+1)*n by nlinarith)
        have he := lambertResidualPrefix_cell (M*N) (d*N) n m hn hd h.2.1 hlo hhi
        cases hb : affineMax l u ((M : ℚ)-d,-(m : ℚ)) (0,0) with
        | none => simp only [show ⌊(M : ℚ)/((l+u)/2)⌋₊=m from rfl, hb, Option.map_none] at ha; contradiction
        | some b =>
          simp only [show ⌊(M : ℚ)/((l+u)/2)⌋₊=m from rfl, hb, Option.map_some, Option.some.injEq] at ha
          rw [← ha]
          have hx := affineMax_sound l u ((M : ℚ)-d,-(m : ℚ)) (0,0) b hb N n
            (Nat.cast_nonneg N) hnl hnu
          simp only [RationalAffine.eval, Rat.cast_sub, Rat.cast_natCast, Rat.cast_neg,
            Rat.cast_zero, zero_mul, add_zero] at hx
          dsimp only [LambertProfileExpression.eval]
          rw [he]
          dsimp [RationalAffine.eval]
          push_cast
          rw [show (M : ℝ)*N-m*n-d*N=((M : ℝ)-d)*N+(-(m : ℝ))*n by ring, hx]
          ring
      · contradiction

/-- Exact endpoint checks either certify an affine profile on an interval or reject that interval. -/
def LambertProfileExpression.affineOn (l u : ℚ) : LambertProfileExpression → Option RationalAffine
  | .linear f => some f
  | .deficit K c => deficitAffine K c l u
  | .residue M d => prefixAffine M d l u
  | .add f g => match f.affineOn l u, g.affineOn l u with
    | some a, some b => some (a.1+b.1,a.2+b.2)
    | _, _ => none
  | .sub f g => match f.affineOn l u, g.affineOn l u with
    | some a, some b => some (a.1-b.1,a.2-b.2)
    | _, _ => none
  | .max f g => match f.affineOn l u, g.affineOn l u with
    | some a, some b => affineMax l u a b
    | _, _ => none

/-- Every accepted interval certificate gives the exact arithmetic profile at every positive root order in that interval. -/
theorem LambertProfileExpression.affineOn_sound (e : LambertProfileExpression)
    (l u : ℚ) (a : RationalAffine) (ha : e.affineOn l u=some a)
    (N n : ℕ) (hn : 0<n) (hnl : (l : ℝ)*N ≤ n) (hnu : (n : ℝ) ≤ (u : ℝ)*N) :
    e.eval N n=a.eval N n := by
  induction e generalizing a with
  | linear f => cases Option.some.inj ha; rfl
  | deficit K c => exact deficitAffine_sound K c l u a ha N n hn hnl hnu
  | residue M d => exact prefixAffine_sound M d l u a ha N n hn hnl hnu
  | add f g ihf ihg =>
    cases hf : f.affineOn l u with
    | none => simp only [affineOn, hf] at ha; contradiction
    | some b =>
      cases hg : g.affineOn l u with
      | none => simp only [affineOn, hf, hg] at ha; contradiction
      | some c =>
        simp only [affineOn, hf, hg, Option.some.injEq] at ha
        rw [eval, ihf b hf, ihg c hg, ← ha]
        simp only [RationalAffine.eval, Rat.cast_add]
        ring
  | sub f g ihf ihg =>
    cases hf : f.affineOn l u with
    | none => simp only [affineOn, hf] at ha; contradiction
    | some b =>
      cases hg : g.affineOn l u with
      | none => simp only [affineOn, hf, hg] at ha; contradiction
      | some c =>
        simp only [affineOn, hf, hg, Option.some.injEq] at ha
        rw [eval, ihf b hf, ihg c hg, ← ha]
        simp only [RationalAffine.eval, Rat.cast_sub]
        ring
  | max f g ihf ihg =>
    cases hf : f.affineOn l u with
    | none => simp only [affineOn, hf] at ha; contradiction
    | some b =>
      cases hg : g.affineOn l u with
      | none => simp only [affineOn, hf, hg] at ha; contradiction
      | some c =>
        simp only [affineOn, hf, hg] at ha
        rw [eval, ihf b hf, ihg c hg]
        exact affineMax_sound l u b c a ha N n (Nat.cast_nonneg N) hnl hnu

end
end Lambert
