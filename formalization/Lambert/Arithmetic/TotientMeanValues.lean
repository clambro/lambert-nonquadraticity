import Lambert.Analysis.QuadraticSummatory
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Algebra.Order.Floor.Semifield

/-! # The quadratic asymptotic of the totient summatory function -/
namespace Lambert
noncomputable section
open Filter Topology Finset
open scoped ArithmeticFunction.Moebius

/-- The real Möbius Dirichlet series at two equals six divided by pi squared. -/
theorem moebius_reciprocal_square_tsum :
    (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^2) = 6/Real.pi^2 := by
  have hc : LSeries (fun d => (ArithmeticFunction.moebius d : ℂ)) 2 =
      ((∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    unfold LSeries
    apply tsum_congr
    intro d
    by_cases hd : d=0
    · simp [hd, LSeries.term]
    · simp [LSeries.term, hd, Complex.cpow_ofNat]
  have he := LSeries_one_mul_Lseries_moebius (s := 2) (by norm_num)
  rw [LSeries_one_eq_riemannZeta (by norm_num), riemannZeta_two, hc] at he
  have hr : Real.pi^2/6*(∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^2)=1 := by
    exact_mod_cast he
  have hp : Real.pi^2≠0 := pow_ne_zero _ Real.pi_ne_zero
  apply (eq_div_iff hp).mpr
  nlinarith

/-- Möbius inversion expresses the totient sum through triangular floor sums. -/
theorem sum_totient_eq_moebius_triangular (N : ℕ) :
    (∑ n ∈ Icc 1 N, (Nat.totient n : ℝ)) =
      ∑ d ∈ Icc 1 N, (ArithmeticFunction.moebius d : ℝ)*
        ((N/d : ℕ) : ℝ)*(((N/d : ℕ) : ℝ)+1)/2 := by
  let f : ArithmeticFunction ℝ := ⟨fun n => Nat.totient n, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨fun n => n, by simp⟩
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n => (Nat.totient n : ℝ)) (g := fun n => (n : ℝ))).mp
    (fun n _ => by exact_mod_cast Nat.sum_totient n)
  have hid : (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*g=f := by
    ext n
    by_cases hn : n=0
    · simp [hn]
    · exact hinv n (Nat.pos_of_ne_zero hn)
  have he := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) g N
  rw [hid] at he
  have hi (m : ℕ) : Ioc 0 m=Icc 1 m := by ext i; simp; omega
  simp only [hi, f, g, ArithmeticFunction.coe_mk, ArithmeticFunction.intCoe_apply] at he
  rw [he]
  apply sum_congr rfl
  intro d _
  have hs (m : ℕ) : (∑ i ∈ Icc 1 m, (i : ℝ)) = (m : ℝ)*(m+1)/2 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_Icc_succ_top (by omega), ih]
      push_cast
      ring
  rw [hs]
  ring

/-- Integer quotients divided by their growing numerator converge to the reciprocal divisor. -/
private theorem nat_div_cast_ratio_tendsto (d : ℕ) :
    Tendsto (fun N : ℕ => ((N/d : ℕ) : ℝ)/(N : ℝ)) atTop (𝓝 ((d : ℝ)⁻¹)) := by
  have he := (tendsto_nat_floor_mul_div_atTop (by positivity : (0 : ℝ)≤(d : ℝ)⁻¹)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto (fun N : ℕ => (⌊(d : ℝ)⁻¹*(N : ℝ)⌋₊ : ℝ)/(N : ℝ)) atTop (𝓝 ((d : ℝ)⁻¹)) at he
  simpa only [inv_mul_eq_div, Nat.floor_div_natCast, Nat.floor_natCast] using he

private def totientFloorTerm (N d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ)*((N/d : ℕ) : ℝ)*(((N/d : ℕ) : ℝ)+1)/(2*(N : ℝ)^2)

private theorem totientFloorTerm_bound (N d : ℕ) (hN : 0<N) :
    ‖totientFloorTerm N d‖ ≤ 1/(d : ℝ)^2 := by
  by_cases hd : d=0
  · simp [totientFloorTerm, hd]
  by_cases hm : N/d=0
  · simp [totientFloorTerm, hm]
  have hnR : (0 : ℝ)<N := by exact_mod_cast hN
  have hdR : (0 : ℝ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hmR : (1 : ℝ)≤((N/d : ℕ) : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm)
  have hmul : ((N/d : ℕ) : ℝ)*d≤N := by exact_mod_cast Nat.div_mul_le_self N d
  have hsq := pow_le_pow_left₀ (by positivity) hmul 2
  have hmu : |(ArithmeticFunction.moebius d : ℝ)|≤1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  rw [totientFloorTerm, Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (N/d) : (0 : ℝ)≤((N/d : ℕ) : ℝ)), abs_of_pos (by positivity : (0 : ℝ)<((N/d : ℕ) : ℝ)+1),
    abs_of_pos (by positivity : (0 : ℝ)<2*(N : ℝ)^2)]
  calc
    _ ≤ 1*((N/d : ℕ) : ℝ)*(((N/d : ℕ) : ℝ)+1)/(2*(N : ℝ)^2) := by
      gcongr
    _ ≤ (((N/d : ℕ) : ℝ)^2)/(N : ℝ)^2 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hmR) (Nat.cast_nonneg (N/d) : (0 : ℝ)≤((N/d : ℕ) : ℝ))]
    _ ≤ 1/(d : ℝ)^2 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [hsq]

private theorem totientFloorTerm_tendsto (d : ℕ) :
    Tendsto (fun N => totientFloorTerm N d) atTop
      (𝓝 ((ArithmeticFunction.moebius d : ℝ)/(2*(d : ℝ)^2))) := by
  have hi : Tendsto (fun N : ℕ => (1 : ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have he := ((nat_div_cast_ratio_tendsto d).mul ((nat_div_cast_ratio_tendsto d).add hi)).const_mul
    ((ArithmeticFunction.moebius d : ℝ)/2)
  have hc : (ArithmeticFunction.moebius d : ℝ)/2*((d : ℝ)⁻¹*((d : ℝ)⁻¹+0)) =
      (ArithmeticFunction.moebius d : ℝ)/(2*(d : ℝ)^2) := by ring
  rw [hc] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  unfold totientFloorTerm
  field_simp

private theorem totientFloorTerm_tsum (N : ℕ) :
    (∑' d, totientFloorTerm N d) = (∑ n ∈ Icc 1 N, (Nat.totient n : ℝ))/(N : ℝ)^2 := by
  rw [tsum_eq_sum (s := Icc 1 N)]
  · rw [sum_totient_eq_moebius_triangular, sum_div]
    apply sum_congr rfl
    intro d _
    unfold totientFloorTerm
    ring
  · intro d hd
    by_cases hz : d=0
    · simp [totientFloorTerm, hz]
    have hn : N<d := by simp only [mem_Icc, not_and_or, not_le] at hd; omega
    simp [totientFloorTerm, Nat.div_eq_of_lt hn]

/-- The totient summatory function divided by the square of its cutoff converges to three divided by pi squared. -/
theorem totient_summatory_tendsto :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (Nat.totient n : ℝ))/(N : ℝ)^2)
      atTop (𝓝 (3/Real.pi^2)) := by
  have he := tendsto_tsum_of_dominated_convergence
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1<2)) totientFloorTerm_tendsto
    (by filter_upwards [eventually_ge_atTop 1] with N hN; exact fun d => totientFloorTerm_bound N d (by omega))
  simp only [totientFloorTerm_tsum] at he
  have hs : (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ)/(2*(d : ℝ)^2))=3/Real.pi^2 := by
    have hf (d : ℕ) : (ArithmeticFunction.moebius d : ℝ)/(2*(d : ℝ)^2)=
        (1/2 : ℝ)*((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^2) := by ring
    simp_rw [hf]
    rw [tsum_mul_left, moebius_reciprocal_square_tsum]
    ring
  rwa [hs] at he

/-- The index-weighted totient summatory function has cubic mean `2/π²`. -/
theorem totient_weighted_summatory_tendsto :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, (n : ℝ) * Nat.totient n) / (N : ℝ) ^ 3)
      atTop (𝓝 (2 / Real.pi ^ 2)) := by
  let S : ℕ → ℝ := fun N => ∑ n ∈ Icc 1 N, (Nat.totient n : ℝ)
  have hs := quadratic_summatory_tendsto S totient_summatory_tendsto
  have he (N : ℕ) : (∑ n ∈ Icc 1 N, (n : ℝ) * Nat.totient n) =
      (N : ℝ) * S N - ∑ k ∈ range N, S k := by
    induction N with
    | zero => simp [S]
    | succ N ih =>
      rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, sum_range_succ]
      have hS : S (N + 1) = S N + Nat.totient (N + 1) := by
        dsimp [S]
        rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      rw [hS]
      push_cast
      ring
  have ht := totient_summatory_tendsto.sub hs
  have hc : 3 / Real.pi ^ 2 - (3 / Real.pi ^ 2) / 3 = 2 / Real.pi ^ 2 := by ring
  rw [hc] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < N by omega))
  rw [he]
  change S N / (N : ℝ) ^ 2 - _ = _
  field_simp

end
end Lambert
