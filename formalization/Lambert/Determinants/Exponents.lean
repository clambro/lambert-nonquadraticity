import Mathlib.Analysis.Real.Pi.Bounds
import Lambert.Determinants.Endpoint
import Lambert.Determinants.Normalization
import Lambert.Determinants.ExponentAsymptotics
import Lambert.Analysis.CubicDilation

/-! # Exact exponents and asymptotics for the main determinant family -/
namespace Lambert
noncomputable section
open Finset Filter Topology

/-- Equal row and pole translations have infinity exponent minus k times the sum of the translated node indices. -/
theorem lambertTranslatedInfinityExponent_equal (h k : ℕ) :
    lambertTranslatedInfinityExponent h k 0 k = -(k : ℤ)*∑ j : Fin h, ((k : ℤ)+j.val) := by
  have hw : lambertAugmentedRowWeight h 0 k = fun j => j.val+k := by
    funext j
    simp [lambertAugmentedRowWeight, Fin.addCases]
  have hm : Monotone (fun j : Fin (h+0) => j.val+k) := fun _ _ hij => Nat.add_le_add_right hij _
  rw [lambertTranslatedInfinityExponent, hw, Tuple.sort_eq_refl_iff_monotone.mpr hm]
  simp only [Nat.add_zero, Equiv.refl_apply, Nat.cast_add]
  rw [← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro j _
  ring

/-- The main determinant family's signed infinity normalization is -5940N³+90N². -/
theorem lambertMain_infinity (N : ℕ) :
    lambertTranslatedInfinityExponent (60*N) (3*N) 0 (3*N) = -5940*(N : ℤ)^3+90*N^2 := by
  rw [lambertTranslatedInfinityExponent_equal, sum_add_distrib, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul,
    Fin.sum_univ_eq_sum_range (fun j : ℕ => (j : ℤ))]
  have hs (h : ℕ) : 2*(∑ j ∈ range h, (j : ℤ))=(h : ℤ)*(h-1) := by
    induction h with
    | zero => simp
    | succ h ih => rw [sum_range_succ]; push_cast; nlinarith
  have he := hs (60*N)
  push_cast at he ⊢
  nlinarith

/-- The main determinant family's clearing power at zero is exactly 15963N³-10N. -/
theorem lambertMain_clearingZero (N : ℕ) :
    (lambertCertificateClearingZeroExponent (60*N) (3*N) : ℤ) = 15963*(N : ℤ)^3-10*N := by
  have hn : 0 ≤ 15963*(N : ℤ)^3-10*N := by
    by_cases hz : N=0
    · simp [hz]
    · have hN : (1 : ℤ) ≤ N := by omega
      nlinarith [sq_nonneg ((N : ℤ)-1), mul_nonneg (show (0 : ℤ) ≤ N by omega)
        (sq_nonneg ((N : ℤ)-1))]
  rw [lambertCertificateClearingZeroExponent, lambertMain_zero,
    lambertMain_infinity, Int.toNat_of_nonneg (by nlinarith)]
  ring

/-- The translated main cyclotomic exponent differs from the square exponent by four explicit tents. -/
theorem lambertMain_cyclotomic (N n : ℕ) :
    (lambertTranslatedCyclotomicExponent (60*N) (3*N) n : ℤ) =
      lambertCyclotomicExponent (60*N) n + 2*(63*N-n : ℕ)-2*(33*N-n : ℕ)-
        2*(60*N-n : ℕ)+2*(30*N-n : ℕ) := by
  unfold lambertTranslatedCyclotomicExponent
  split_ifs with hn
  · omega
  · have hz : (∑ r ∈ range (60*N), (60*N-(2*r+3)*n))=0 := by
      apply sum_eq_zero
      intro r _
      have := Nat.mul_le_mul_right n (show 2 ≤ 2*r+3 by omega)
      omega
    rw [lambertCyclotomicExponent, hz]
    omega

private theorem extend_sum (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hf : ∀ n, a ≤ n → f n=0) :
    (∑ n ∈ Ico 1 b, f n)=∑ n ∈ Ico 1 a, f n := by
  symm
  apply sum_subset (Ico_subset_Ico_right hab)
  intro n hn hna
  apply hf
  simp only [mem_Ico] at hn hna
  omega

/-- Weighted exponents of the main determinant family equal the square sum plus its four exact tent corrections. -/
theorem lambertMain_weighted_sum (w : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ico 1 (63*N), w n*lambertTranslatedCyclotomicExponent (60*N) (3*N) n) =
      (∑ n ∈ Ico 1 (60*N), w n*lambertCyclotomicExponent (60*N) n)+
        2*arithmeticTent w (63*N) 1-2*arithmeticTent w (33*N) 1-
        2*arithmeticTent w (60*N) 1+2*arithmeticTent w (30*N) 1 := by
  have he (n : ℕ) : (lambertTranslatedCyclotomicExponent (60*N) (3*N) n : ℝ) =
      lambertCyclotomicExponent (60*N) n+2*((63*N-n : ℕ) : ℝ)-2*((33*N-n : ℕ) : ℝ)-
        2*((60*N-n : ℕ) : ℝ)+2*((30*N-n : ℕ) : ℝ) := by
    exact_mod_cast lambertMain_cyclotomic N n
  simp_rw [he, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  have ht (k : ℕ) (hk : k ≤ 63*N) :
      (∑ n ∈ Ico 1 (63*N), w n*(2*((k-n : ℕ) : ℝ))) = 2*arithmeticTent w k 1 := by
    rw [arithmeticTent_eq_window _ _ _ (by omega)]
    simp only [one_mul]
    have hx := extend_sum (fun n => w n*((k-n : ℕ) : ℝ)) k (63*N) hk
      (fun n hn => by simp [Nat.sub_eq_zero_of_le hn])
    rw [← hx, mul_sum]
    apply sum_congr rfl
    intros
    ring
  simp_rw [mul_add, sum_add_distrib]
  rw [ht (63*N) le_rfl, ht (33*N) (by omega), ht (60*N) (by omega), ht (30*N) (by omega)]
  have hx := extend_sum (fun n => w n * (lambertCyclotomicExponent (60*N) n : ℝ))
    (60*N) (63*N) (by omega) (fun n hn => by
      rw [lambertCyclotomicExponent_eq_zero_of_le _ _ hn]; simp)
  rw [← hx]

/-- The unweighted cyclotomic mass of the two-sided family is subcubic. -/
theorem lambertMain_exponent_sum_tendsto :
    Tendsto (fun N : ℕ => (∑ n ∈ Ico 1 (63*N),
      (lambertTranslatedCyclotomicExponent (60*N) (3*N) n : ℝ))/(N : ℝ)^3) atTop (𝓝 0) := by
  have hs := tendsto_cubic_dilation _ lambertCyclotomicExponent_sum_tendsto_zero 60 (by omega)
  have ht (k : ℕ) (hk : 0 < k) := tendsto_cubic_dilation _ (arithmeticTent_one_tendsto 1 (by omega)) k hk
  have he := (((hs.add ((ht 63 (by omega)).const_mul 2)).sub ((ht 33 (by omega)).const_mul 2)).sub
    ((ht 60 (by omega)).const_mul 2)).add ((ht 30 (by omega)).const_mul 2)
  norm_num at he
  convert he using 1
  funext N
  rw [show (∑ n ∈ Ico 1 (63*N), (lambertTranslatedCyclotomicExponent (60*N) (3*N) n : ℝ)) =
    ∑ n ∈ Ico 1 (63*N), (1 : ℝ)*lambertTranslatedCyclotomicExponent (60*N) (3*N) n by simp,
    lambertMain_weighted_sum]
  simp only [one_mul]
  ring

/-- The two-sided family's weighted cyclotomic mass has cubic coefficient 27000+428220/π². -/
theorem lambertMain_exponent_totient_tendsto :
    Tendsto (fun N : ℕ => (∑ n ∈ Ico 1 (63*N),
      (Nat.totient n : ℝ)*lambertTranslatedCyclotomicExponent (60*N) (3*N) n)/(N : ℝ)^3)
      atTop (𝓝 (27000+428220/Real.pi^2)) := by
  have hs := tendsto_cubic_dilation _ (lambertCyclotomicExponent_totient_tendsto) 60 (by omega)
  have ht (k : ℕ) (hk : 0 < k) := tendsto_cubic_dilation _ (totientTent_tendsto 1 (by omega)) k hk
  have he := (((hs.add ((ht 63 (by omega)).const_mul 2)).sub ((ht 33 (by omega)).const_mul 2)).sub
    ((ht 60 (by omega)).const_mul 2)).add ((ht 30 (by omega)).const_mul 2)
  convert he using 1
  · funext N
    rw [lambertMain_weighted_sum]
    ring
  · norm_num
    ring

/-- The two-sided family's clearing exponent at zero has cubic coefficient 15963. -/
theorem lambertMain_clearingZero_tendsto :
    Tendsto (fun N : ℕ => (lambertCertificateClearingZeroExponent (60*N) (3*N) : ℝ)/(N : ℝ)^3)
      atTop (𝓝 15963) := by
  have hi : Tendsto (fun N : ℕ => (1 : ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have he := (tendsto_const_nhds (x := (15963 : ℝ))).sub ((hi.pow 2).const_mul 10)
  simp only [zero_pow (by omega : 2 ≠ 0), mul_zero, sub_zero] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hx : (lambertCertificateClearingZeroExponent (60*N) (3*N) : ℝ) =
      15963*(N : ℝ)^3-10*N := by exact_mod_cast lambertMain_clearingZero N
  rw [hx]
  field_simp

/-- The two-sided Lambert constants satisfy 2*(42963+428220/π²)<202140. -/
theorem lambert_main_degree_two_margin :
    2*((42963 : ℝ)+428220/Real.pi^2)<202140 := by
  have hp := Real.pi_gt_three
  have hp0 := Real.pi_pos
  have hd : (0 : ℝ)<Real.pi^2 := by positivity
  have he : 428220/Real.pi^2<(202140 : ℝ)/2-42963 := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  linarith


end
end Lambert
