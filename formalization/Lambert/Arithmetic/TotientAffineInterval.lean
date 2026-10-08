import Lambert.Arithmetic.TotientMeanValues

/-! # Totient-weighted affine profiles on scaled intervals -/
namespace Lambert
noncomputable section
open Finset Filter Topology

/-- The classical totient mean controls a prefix with any fixed positive real scale. -/
theorem totient_scaled_prefix_tendsto (u : ℝ) (hu : 0<u) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 ⌊u*N⌋₊, (Nat.totient n : ℝ))/(N : ℝ)^2)
      atTop (𝓝 (3/Real.pi^2*u^2)) := by
  have ht := tendsto_nat_floor_mul_atTop u hu
  have hr := (tendsto_nat_floor_mul_div_atTop hu.le).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := (totient_summatory_tendsto.comp ht).mul (hr.pow 2)
  apply he.congr'
  filter_upwards [ht.eventually (eventually_ge_atTop 1)] with N hN
  have hn : (⌊u*N⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (show ⌊u*N⌋₊≠0 by omega)
  dsimp only [Function.comp_apply]
  field_simp

/-- The index-weighted totient mean controls a prefix with any fixed positive real scale. -/
theorem totient_scaled_first_prefix_tendsto (u : ℝ) (hu : 0<u) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 ⌊u*N⌋₊, (n : ℝ)*Nat.totient n)/(N : ℝ)^3)
      atTop (𝓝 (2/Real.pi^2*u^3)) := by
  have ht := tendsto_nat_floor_mul_atTop u hu
  have hr := (tendsto_nat_floor_mul_div_atTop hu.le).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := (totient_weighted_summatory_tendsto.comp ht).mul (hr.pow 3)
  apply he.congr'
  filter_upwards [ht.eventually (eventually_ge_atTop 1)] with N hN
  have hn : (⌊u*N⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (show ⌊u*N⌋₊≠0 by omega)
  dsimp only [Function.comp_apply]
  field_simp

/-- The weighted sum of an affine form over a scaled prefix has its exact cubic coefficient. -/
theorem totient_affine_prefix_tendsto (u a b : ℝ) (hu : 0<u) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 ⌊u*N⌋₊, (Nat.totient n : ℝ)*(a*N+b*n))/(N : ℝ)^3)
      atTop (𝓝 ((3*a*u^2+2*b*u^3)/Real.pi^2)) := by
  have he := ((totient_scaled_prefix_tendsto u hu).const_mul a).add
    ((totient_scaled_first_prefix_tendsto u hu).const_mul b)
  convert he using 1
  · funext N
    have hs : (∑ n ∈ Icc 1 ⌊u*N⌋₊, (Nat.totient n : ℝ)*(a*N+b*n)) =
        a*N*(∑ n ∈ Icc 1 ⌊u*N⌋₊, (Nat.totient n : ℝ))+
          b*(∑ n ∈ Icc 1 ⌊u*N⌋₊, (n : ℝ)*Nat.totient n) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro n _
      ring
    rw [hs]
    by_cases hn : (N : ℝ)=0
    · simp [hn]
    · field_simp
  · congr 1
    ring

/-- A scaled interval has the difference of its two affine-prefix cubic coefficients. -/
theorem totient_affine_interval_tendsto (l u a b : ℝ)
    (hl : 0<l) (hlu : l≤u) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc ⌊l*N⌋₊ ⌊u*N⌋₊,
      (Nat.totient n : ℝ)*(a*N+b*n))/(N : ℝ)^3)
      atTop (𝓝 ((3*a*(u^2-l^2)+2*b*(u^3-l^3))/Real.pi^2)) := by
  have he := (totient_affine_prefix_tendsto u a b (hl.trans_le hlu)).sub
    (totient_affine_prefix_tendsto l a b hl)
  convert he using 1
  · funext N
    have hm : ⌊l*N⌋₊ ≤ ⌊u*N⌋₊ := Nat.floor_mono (mul_le_mul_of_nonneg_right hlu (Nat.cast_nonneg N))
    have hs := sum_sdiff_eq_sub (f := fun n : ℕ => (Nat.totient n : ℝ)*(a*N+b*n))
      (show Icc 1 ⌊l*N⌋₊ ⊆ Icc 1 ⌊u*N⌋₊ from Icc_subset_Icc_right hm)
    have hd : Icc 1 ⌊u*N⌋₊ \ Icc 1 ⌊l*N⌋₊=Ioc ⌊l*N⌋₊ ⌊u*N⌋₊ := by
      apply Finset.ext
      intro n
      rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hd] at hs
    rw [hs, sub_div]
  · congr 1
    ring

end
end Lambert
