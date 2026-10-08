import Lambert.Arithmetic.PolynomialPrefixSum
import Lambert.Arithmetic.PeriodicPolynomialSpace

/-!
# Polynomial sequences on residue classes

Polynomial descriptions in the quotient coordinate make finite summation
explicit. All closure results retain the polynomial degree budget.
-/

namespace Lambert

noncomputable section

open Finset Polynomial

variable {K : Type*} [Field K]

/-- A sequence has periodic polynomial degree at most `d` when its restriction
to each residue class is a polynomial of degree at most `d` in the quotient index. -/
def HasPeriodicPolynomialDegree (n d : ℕ) (f : ℕ → K) : Prop :=
  ∃ p : ℕ → K[X], (∀ c < n, (p c).natDegree ≤ d) ∧
    ∀ m c, c < n → f (n * m + c) = (p c).eval (m : K)

/-- A periodic polynomial degree bound remains valid after increasing the bound. -/
theorem HasPeriodicPolynomialDegree.mono {n d e : ℕ} {f : ℕ → K}
    (hf : HasPeriodicPolynomialDegree n d f) (hde : d ≤ e) :
    HasPeriodicPolynomialDegree n e f := by
  obtain ⟨p, hp, he⟩ := hf
  exact ⟨p, fun c hc => (hp c hc).trans hde, he⟩

/-- A constant sequence has periodic polynomial degree zero. -/
theorem hasPeriodicPolynomialDegree_const (n : ℕ) (a : K) :
    HasPeriodicPolynomialDegree n 0 (fun _ => a) := by
  exact ⟨fun _ => C a, by simp, by simp⟩

/-- Multiplication adds periodic polynomial degree bounds. -/
theorem HasPeriodicPolynomialDegree.mul {n d e : ℕ} {f g : ℕ → K}
    (hf : HasPeriodicPolynomialDegree n d f) (hg : HasPeriodicPolynomialDegree n e g) :
    HasPeriodicPolynomialDegree n (d + e) (fun i => f i * g i) := by
  obtain ⟨p, hp, he⟩ := hf
  obtain ⟨q, hq, hqe⟩ := hg
  exact ⟨fun c => p c * q c, fun c hc => natDegree_mul_le.trans
    (Nat.add_le_add (hp c hc) (hq c hc)), by intro m c hc; simp only [eval_mul, he m c hc, hqe m c hc]⟩

/-- Addition preserves a common periodic polynomial degree bound. -/
theorem HasPeriodicPolynomialDegree.add {n d : ℕ} {f g : ℕ → K}
    (hf : HasPeriodicPolynomialDegree n d f) (hg : HasPeriodicPolynomialDegree n d g) :
    HasPeriodicPolynomialDegree n d (fun i => f i + g i) := by
  obtain ⟨p, hp, he⟩ := hf
  obtain ⟨q, hq, hqe⟩ := hg
  exact ⟨fun c => p c + q c, fun c hc => (natDegree_add_le _ _).trans
    (max_le (hp c hc) (hq c hc)), by intro m c hc; simp only [eval_add, he m c hc, hqe m c hc]⟩

/-- Negation preserves a periodic polynomial degree bound. -/
theorem HasPeriodicPolynomialDegree.neg {n d : ℕ} {f : ℕ → K}
    (hf : HasPeriodicPolynomialDegree n d f) :
    HasPeriodicPolynomialDegree n d (fun i => -f i) := by
  obtain ⟨p, hp, he⟩ := hf
  exact ⟨fun c => -p c, by simpa using hp, by intro m c hc; simp only [eval_neg, he m c hc]⟩

/-- Scalar multiplication preserves a periodic polynomial degree bound. -/
theorem HasPeriodicPolynomialDegree.smul {n d : ℕ} {f : ℕ → K}
    (hf : HasPeriodicPolynomialDegree n d f) (a : K) :
    HasPeriodicPolynomialDegree n d (fun i => a * f i) := by
  simpa only [zero_add] using (hasPeriodicPolynomialDegree_const n a).mul hf

/-- A finite sum of sequences with a common periodic polynomial degree bound retains that bound. -/
theorem HasPeriodicPolynomialDegree.finset_sum {ι : Type*} {n d : ℕ}
    (s : Finset ι) (f : ι → ℕ → K)
    (hf : ∀ j ∈ s, HasPeriodicPolynomialDegree n d (f j)) :
    HasPeriodicPolynomialDegree n d (fun i => ∑ j ∈ s, f j i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (hasPeriodicPolynomialDegree_const n (0 : K)).mono (Nat.zero_le d)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self a s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- A natural-index power has periodic polynomial degree at most its exponent. -/
theorem hasPeriodicPolynomialDegree_pow (n d : ℕ) :
    HasPeriodicPolynomialDegree n d (fun i => (i : K) ^ d) := by
  refine ⟨fun c => (C (n : K) * X + C (c : K)) ^ d, ?_, ?_⟩
  · intro c _
    have hb : (C (n : K) * X + C (c : K)).natDegree ≤ 1 := by
      exact (natDegree_add_le _ _).trans (max_le (by simpa using
        (natDegree_mul_le (p := C (n : K)) (q := (X : K[X])))) (by simp))
    simpa using natDegree_pow_le_of_le d hb
  · intro m c _
    simp

/-- A function of powers of an nth root of unity has periodic polynomial degree zero. -/
theorem hasPeriodicPolynomialDegree_root (n : ℕ) (ζ : K) (hζ : ζ ^ n = 1)
    (a : K → K) : HasPeriodicPolynomialDegree n 0 (fun i => a (ζ ^ i)) := by
  refine ⟨fun c => C (a (ζ ^ c)), by simp, ?_⟩
  intro m c _
  simp [pow_add, pow_mul, hζ]

private theorem sum_range_blocks (f : ℕ → K) (n m : ℕ) :
    (∑ i ∈ range (n * m), f i) = ∑ k ∈ range m, ∑ c ∈ range n, f (n * k + c) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

/-- Finite summation of a periodic polynomial sequence raises its degree bound
by at most one. -/
theorem HasPeriodicPolynomialDegree.prefix [Algebra ℚ K] {n d : ℕ} {f : ℕ → K}
    (hf : HasPeriodicPolynomialDegree n d f) :
    HasPeriodicPolynomialDegree n (d + 1) (fun i => ∑ k ∈ range i, f k) := by
  obtain ⟨p, hp, he⟩ := hf
  let Q := fun c => (∑ a ∈ range n, polynomialPrefixSum (p a)) + ∑ a ∈ range c, p a
  refine ⟨Q, ?_, ?_⟩
  · intro c hc
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply natDegree_sum_le_of_forall_le
      intro a ha
      exact (polynomialPrefixSum_natDegree_le _).trans (Nat.add_le_add_right (hp a (mem_range.mp ha)) 1)
    · apply natDegree_sum_le_of_forall_le
      intro a ha
      exact (hp a ((mem_range.mp ha).trans hc)).trans (Nat.le_succ d)
  · intro m c hc
    dsimp only
    rw [sum_range_add, sum_range_blocks]
    simp only [Q, eval_add, eval_finsetSum, polynomialPrefixSum_eval]
    rw [sum_comm]
    congr 1
    · apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro k _
      exact he k a (mem_range.mp ha)
    · apply sum_congr rfl
      intro a ha
      exact he m a ((mem_range.mp ha).trans hc)

/-- Shifting a sequence by one preserves its periodic polynomial degree bound. -/
theorem HasPeriodicPolynomialDegree.shift {n d : ℕ} {f : ℕ → K}
    (hn : 0 < n) (hf : HasPeriodicPolynomialDegree n d f) :
    HasPeriodicPolynomialDegree n d (fun i => f (i + 1)) := by
  obtain ⟨p, hp, he⟩ := hf
  refine ⟨fun c => if c + 1 < n then p (c + 1) else (p 0).comp (X + C 1), ?_, ?_⟩
  · intro c _
    dsimp only
    split_ifs with hc
    · exact hp _ hc
    · exact natDegree_comp_le.trans (by simpa only [natDegree_X_add_C, mul_one] using hp 0 hn)
  · intro m c hc
    dsimp only
    split_ifs with hcs
    · simpa only [Nat.add_assoc] using he m (c + 1) hcs
    · have hcn : c + 1 = n := by omega
      rw [show n * m + c + 1 = n * (m + 1) + 0 by rw [Nat.mul_add, Nat.mul_one]; omega, he _ 0 hn]
      simp

/-- Summation over positive indices raises the periodic polynomial degree bound
by at most one. -/
theorem HasPeriodicPolynomialDegree.positivePrefix [Algebra ℚ K] {n d : ℕ} {f : ℕ → K}
    (hn : 0 < n) (hf : HasPeriodicPolynomialDegree n d f) :
    HasPeriodicPolynomialDegree n (d + 1) (fun i => ∑ k ∈ range i, f (k + 1)) :=
  (hf.shift hn).prefix

/-- A sequence polynomial in the quotient index on each residue class belongs
to the corresponding weighted periodic polynomial space in the original index. -/
theorem HasPeriodicPolynomialDegree.mem_weightedSpace [CharZero K]
    {α : Type*} {n d : ℕ} {f : ℕ → K} (hn : 0 < n)
    (hf : HasPeriodicPolynomialDegree n d f) (h : ℕ) (w : α → ℕ → K) (a : α) :
    (fun i : Fin h => f i.val * w a i.val) ∈ periodicPolynomialSpace h n d w := by
  classical
  obtain ⟨p, hp, he⟩ := hf
  let Q := fun c => (p c).comp (C (n : K)⁻¹ * (X - C (c : K)))
  have hQ (c : ℕ) (hc : c < n) : (Q c).natDegree ≤ d := by
    dsimp only [Q]
    apply natDegree_comp_le.trans
    have hl : (C (n : K)⁻¹ * (X - C (c : K))).natDegree ≤ 1 := by
      apply natDegree_mul_le.trans
      rw [natDegree_C, zero_add]
      exact natDegree_X_sub_C_le _
    exact (Nat.mul_le_mul (hp c hc) hl).trans (by simp)
  have hv (i : ℕ) : f i = (Q (i % n)).eval (i : K) := by
    have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hi := congrArg (fun k : ℕ => (k : K)) (Nat.div_add_mod i n)
    simp only [Nat.cast_add, Nat.cast_mul] at hi
    have hm : (n : K)⁻¹ * ((i : K) - (i % n : ℕ)) = (i / n : ℕ) := by
      have hsub : (i : K) - (i % n : ℕ) = (n : K) * (i / n : ℕ) := by
        linear_combination -hi
      rw [hsub]
      simp [hn0]
    calc
      f i = f (n * (i / n) + i % n) := congrArg f (Nat.div_add_mod i n).symm
      _ = (p (i % n)).eval ((i / n : ℕ) : K) := he _ _ (Nat.mod_lt _ hn)
      _ = (Q (i % n)).eval (i : K) := by
        simp only [Q, eval_comp, eval_mul, eval_C, eval_sub, eval_X, hm]
  have hs : (fun i : Fin h => f i.val * w a i.val) =
      ∑ c : Fin n, (fun i : Fin h => if i.val % n = c.val then
        (Q c.val).eval (i.val : K) * w a i.val else 0) := by
    funext i
    simp only [Finset.sum_apply]
    rw [sum_eq_single (⟨i.val % n, Nat.mod_lt _ hn⟩ : Fin n)]
    · simp [hv]
    · intro c _ hc
      have hc' : i.val % n ≠ c.val := fun he => hc (Fin.ext he.symm)
      simp [hc']
    · simp
  rw [hs]
  exact Submodule.sum_mem _ fun c _ =>
    periodicPolynomialSpace_eval_mem h n d w a c c.isLt (Q c) (hQ c c.isLt)

end

end Lambert
