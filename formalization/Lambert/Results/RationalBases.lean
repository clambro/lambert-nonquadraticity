import Lambert.Results.MainTheorem
namespace Lambert
noncomputable section
open Polynomial IntermediateField

private theorem rational_height_le (a b : ℤ) (hb : 0 < b) (hab : b < a) :
    Height.logHeight₁ ((a : ℚ)/b) ≤ Real.log a := by
  let q : ℚ := (a : ℚ)/b
  obtain ⟨c,ha,hb'⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a (ne_of_gt hb)
  have hd : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have hc : 0 < c := by change b = c * (q.den : ℤ) at hb'; nlinarith
  have hn : 0 ≤ q.num := by change a = c * q.num at ha; nlinarith
  have hna : (q.num.natAbs : ℤ) ≤ a := by
    rw [Int.natCast_natAbs, abs_of_nonneg hn]
    change a = c * q.num at ha
    nlinarith
  have hdb : (q.den : ℤ) ≤ b := by
    change b = c * (q.den : ℤ) at hb'
    nlinarith
  change Height.logHeight₁ q ≤ Real.log a
  rw [Rat.logHeight₁_eq_log_max]
  apply Real.log_le_log (by positivity)
  rw [Nat.cast_max]
  exact max_le (by simpa only [Int.cast_natCast] using (Int.cast_le.mpr hna : ((q.num.natAbs : ℤ) : ℝ) ≤ a)) (by exact_mod_cast hdb.trans hab.le)

/-- The main height theorem specialized to a rational base; no coprimality is required. -/
theorem lambertValue_no_polynomial_relation_of_rational_margin
    (a b : ℤ) (hb : 0 < b) (hab : b < a) (e : ℕ)
    (hm : (e : ℝ)*(42963+428220/Real.pi^2)*Real.log a <
      202140*Real.log ((a : ℝ)/b))
    (p : ℚ[X]) (hp : p.natDegree ≤ e)
    (hroot : p.eval₂ (Rat.castHom ℝ) (lambertValue ((a : ℝ)/b)) = 0) : p=0 := by
  let K : IntermediateField ℚ ℝ := ⊥
  let : FiniteDimensional ℚ K := by dsimp [K]; infer_instance
  let : NumberField K := {}
  let q : K := algebraMap ℚ K ((a : ℚ)/b)
  have hq : (q : ℝ) = (a : ℝ)/b := by simp [q]
  have hq1 : 1 < (q : ℝ) := by rw [hq]; exact (one_lt_div (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)
  have hh : Height.logHeight₁ q = Height.logHeight₁ ((a : ℚ)/b) := by
    have h := numberField_logHeight_extension (L := K) ((a : ℚ)/b)
    simpa [K, q, IntermediateField.finrank_bot] using h
  have hm' : (e : ℝ)*(42963+428220/Real.pi^2)*Height.logHeight₁ q <
      202140*Real.log (q : ℝ) := by
    rw [hq, hh]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (rational_height_le a b hb hab) (by positivity)) hm
  have heval : (p.map (algebraMap ℚ K)).eval₂ K.subtype (lambertValue (q : ℝ))=0 := by
    rw [eval₂_map, hq]
    have hc : K.subtype.comp (algebraMap ℚ K) = Rat.castHom ℝ := Subsingleton.elim _ _
    rw [hc]; exact hroot
  have hz := lambertValue_no_relation_of_numberField_height K q hq1 e hm'
    (p.map (algebraMap ℚ K)) (by simpa using hp) heval
  exact (Polynomial.map_injective (f := algebraMap ℚ K) (algebraMap ℚ K).injective)
    (by simpa only [Polynomial.map_zero] using hz)
/-- Corollary 1.2: the main degree-weighted rational region. -/
theorem lambertValue_no_polynomial_relation_of_rational_region
    (a b : ℤ) (hb : 0 < b) (hab : b < a) (e : ℕ)
    (hregion : Real.log b / Real.log a <
      1 - (e : ℝ)*((42963+428220/Real.pi^2)/202140))
    (p : ℚ[X]) (hp : p.natDegree ≤ e)
    (hroot : p.eval₂ (Rat.castHom ℝ) (lambertValue ((a : ℝ)/b))=0) : p=0 := by
  have ha1 : (1 : ℝ) < a := by exact_mod_cast (show (1 : ℤ) < a by omega)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hr := (div_lt_iff₀ (Real.log_pos ha1)).mp hregion
  apply lambertValue_no_polynomial_relation_of_rational_margin a b hb hab e ?_ p hp hroot
  rw [Real.log_div (zero_lt_one.trans ha1).ne' hbR.ne']
  nlinarith

/-- Irrationality in the main rational region. -/
theorem lambertValue_irrational_of_rational_region
    (a b : ℤ) (hb : 0 < b) (hab : b < a)
    (hregion : Real.log b / Real.log a < 1-(42963+428220/Real.pi^2)/202140) :
    Irrational (lambertValue ((a : ℝ)/b)) := by
  rintro ⟨r,hr⟩
  have hp := lambertValue_no_polynomial_relation_of_rational_region a b hb hab 1
    (by simpa using hregion) (X-C r) (by compute_degree) (by simp [← hr])
  have hc := congrArg (fun p : ℚ[X] => p.coeff 1) hp
  simp at hc

/-- The headline rational cutoff 0.5728 follows from the main construction. -/
theorem lambertValue_irrational_of_log_ratio_lt_5728
    (a b : ℤ) (hb : 0 < b) (hab : b < a)
    (hregion : Real.log b / Real.log a < (5728/10000 : ℝ)) :
    Irrational (lambertValue ((a : ℝ)/b)) := by
  apply lambertValue_irrational_of_rational_region a b hb hab
  apply hregion.trans_le
  have hp := Real.pi_gt_d6
  have hsq : (3.141592 : ℝ)^2 < Real.pi^2 := by nlinarith [Real.pi_pos]
  have hd : 428220/Real.pi^2 < (202140 : ℝ)*(1-5728/10000)-42963 := by
    apply (div_lt_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith
  linarith

end
end Lambert
