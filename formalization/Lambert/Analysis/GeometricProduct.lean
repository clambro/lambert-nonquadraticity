import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.LinearAlgebra.Lagrange

/-!
# Positive lower bounds for finite geometric products

A summable logarithm gives a positive base-dependent lower bound for every
finite product of distinct positive-exponent factors. No bound on the
number or placement of the exponents is needed.
-/

namespace Lambert

open scoped BigOperators

/-- The positive geometric product floor, expressed by the exponential of its logarithmic sum. -/
noncomputable def geometricProductFloor (u : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - u ^ (k + 1)))

/-- The logarithms of the geometric product factors are summable for a ratio strictly between zero and one. -/
theorem summable_log_geometricProduct (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    Summable (fun k : ℕ => Real.log (1 - u ^ (k + 1))) := by
  have hs : Summable (fun k : ℕ => u ^ (k + 1)) :=
    (summable_geometric_of_lt_one hu.le hu1).mul_right u |>.congr
      (fun k => by rw [pow_succ])
  simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs.neg

/-- The geometric product floor is strictly positive. -/
theorem geometricProductFloor_pos (u : ℝ) : 0 < geometricProductFloor u :=
  Real.exp_pos _

/-- Every finite geometric product is at least the positive infinite-product floor and at most one. -/
theorem geometricProductFloor_le_prod (u : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (s : Finset ℕ) :
    geometricProductFloor u ≤ ∏ k ∈ s, (1 - u ^ (k + 1)) ∧
      (∏ k ∈ s, (1 - u ^ (k + 1))) ≤ 1 := by
  have hpos (k : ℕ) : 0 < 1 - u ^ (k + 1) :=
    sub_pos.mpr (pow_lt_one₀ hu.le hu1 (by omega))
  have hlog (k : ℕ) : Real.log (1 - u ^ (k + 1)) ≤ 0 :=
    Real.log_nonpos (hpos k).le (by linarith [pow_pos hu (k + 1)])
  have hs := summable_log_geometricProduct u hu hu1
  have hb := hs.neg.sum_le_tsum s (fun k _ => neg_nonneg.mpr (hlog k))
  rw [Finset.sum_neg_distrib, tsum_neg] at hb
  have he := Real.exp_le_exp.mpr (show
      (∑' k : ℕ, Real.log (1 - u ^ (k + 1))) ≤
        ∑ k ∈ s, Real.log (1 - u ^ (k + 1)) by linarith)
  rw [Real.exp_sum] at he
  simp_rw [Real.exp_log (hpos _)] at he
  refine ⟨he, ?_⟩
  exact Finset.prod_le_one (fun k _ => (hpos k).le)
    (fun k _ => by linarith [pow_pos hu (k + 1)])

/-- Distinct positive exponent factors obey the same geometric product floor regardless of their positions. -/
theorem geometricProductFloor_le_prod_positive_exponents
    (u : ℝ) (hu : 0 < u) (hu1 : u < 1) (s : Finset ℕ)
    (hs : ∀ k ∈ s, 0 < k) :
    geometricProductFloor u ≤ ∏ k ∈ s, (1 - u ^ k) ∧
      (∏ k ∈ s, (1 - u ^ k)) ≤ 1 := by
  have hi : ∀ i ∈ s, ∀ j ∈ s, i - 1 = j - 1 → i = j := by
    intro i his j hjs he
    have hh := hs i his
    have hj := hs j hjs
    omega
  have hp : (∏ k ∈ s.image (fun k => k - 1), (1 - u ^ (k + 1))) =
      ∏ k ∈ s, (1 - u ^ k) := by
    rw [Finset.prod_image hi]
    apply Finset.prod_congr rfl
    intro k hk
    rw [Nat.sub_add_cancel (hs k hk)]
  have hb := geometricProductFloor_le_prod u hu hu1 (s.image (fun k => k - 1))
  rwa [hp] at hb

/-- An injectively indexed finite family of positive-exponent factors has bounds independent of its cardinality and exponent placement. -/
theorem geometricProductFloor_le_prod_of_injOn {ι : Type*} [DecidableEq ι]
    (u : ℝ) (hu : 0 < u) (hu1 : u < 1) (s : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ s, 0 < e i) (hinj : Set.InjOn e s) :
    geometricProductFloor u ≤ ∏ i ∈ s, (1 - u ^ e i) ∧
      (∏ i ∈ s, (1 - u ^ e i)) ≤ 1 := by
  have hp := geometricProductFloor_le_prod_positive_exponents u hu hu1 (s.image e)
    (by intro k hk; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk; exact he i hi)
  rw [Finset.prod_image (fun i hi j hj h => hinj hi hj h)] at hp
  exact hp

/-- A geometric difference above a smaller exponent is its larger power times a positive reciprocal-base factor. -/
theorem geometricDifference_above_eq (q : ℝ) (hq : 0 < q) (i m : ℕ) (hi : i ≤ m) :
    q ^ m - q ^ i = q ^ m * (1 - q⁻¹ ^ (m - i)) := by
  have hm : q ^ m = q ^ i * q ^ (m - i) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  rw [hm, inv_pow]
  field_simp

/-- Distinct geometric factors above a finite exponent set have lower and upper bounds with one base-dependent product floor. -/
theorem geometricDifferenceProduct_above_bounds {ι : Type*} [DecidableEq ι]
    (q : ℝ) (hq : 1 < q) (s : Finset ι) (e : ι → ℕ) (hinj : Set.InjOn e s)
    (m : ℕ) (hm : ∀ i ∈ s, e i < m) :
    geometricProductFloor q⁻¹ * q ^ (m * s.card) ≤ ∏ i ∈ s, (q ^ m - q ^ e i) ∧
      (∏ i ∈ s, (q ^ m - q ^ e i)) ≤ q ^ (m * s.card) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hu : 0 < q⁻¹ := inv_pos.mpr hq0
  have hu1 : q⁻¹ < 1 := (inv_lt_one₀ hq0).mpr hq
  have hgapinj : Set.InjOn (fun i => m - e i) s := by
    intro i hi j hj h
    change m - e i = m - e j at h
    apply hinj hi hj
    have hh := hm i hi
    have hk := hm j hj
    omega
  have hb := geometricProductFloor_le_prod_of_injOn q⁻¹ hu hu1 s
    (fun i => m - e i) (fun i hi => Nat.sub_pos_of_lt (hm i hi)) hgapinj
  have hp : (∏ i ∈ s, (q ^ m - q ^ e i)) =
      q ^ (m * s.card) * ∏ i ∈ s, (1 - q⁻¹ ^ (m - e i)) := by
    calc
      (∏ i ∈ s, (q ^ m - q ^ e i)) =
          ∏ i ∈ s, q ^ m * (1 - q⁻¹ ^ (m - e i)) :=
        Finset.prod_congr rfl (fun i hi => geometricDifference_above_eq q hq0 _ m (hm i hi).le)
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul]
  rw [hp]
  have hpos : 0 ≤ q ^ (m * s.card) := (pow_pos hq0 _).le
  exact ⟨by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb.1 hpos,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.2 hpos⟩

end Lambert
