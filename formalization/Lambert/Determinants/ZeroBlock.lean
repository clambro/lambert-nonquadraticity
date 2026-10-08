import Lambert.Determinants.ZeroCost

/-! # Compressed finite-part determinant blocks for translated windows -/
namespace Lambert
noncomputable section
open Finset Matrix
open scoped Classical WithZero
variable {K : Type*} [Field K]

/-- The compressed left block has one evaluation column below the pole window and evaluation/derivative pairs above it. -/
def lambertZeroBlockLeft (K : Type*) [Field K] (h k N : ℕ) :
    Matrix (Fin h) (Fin (k+2*N)) (LaurentSeries K) := fun i v =>
  (if v.val < k ∨ (v.val-k)%2=0 then 1 else (i.val : LaurentSeries K))*
    lambertZeroBase K ^ (i.val*lambertSlotNode k v.val)

/-- The compressed right block attaches the actual translated finite-part weights to each evaluation or derivative slot. -/
def lambertTranslatedZeroBlockRight (Z : LaurentSeries K) (h k L s N : ℕ) :
    Matrix (Fin (k+2*N)) (Fin h) (LaurentSeries K) := fun v r =>
  (if v.val < k ∨ (v.val-k)%2=0 then
      lambertZeroBlockW Z k L (lambertSlotNode k v.val) +
        ((r.val+s : ℕ) : LaurentSeries K)*lambertZeroBlockC K k L (lambertSlotNode k v.val)
    else lambertZeroBlockC K k L (lambertSlotNode k v.val))*
      lambertZeroBase K ^ ((r.val+s)*lambertSlotNode k v.val)

/-- Each compressed evaluation or derivative entry has the order of its geometric monomial. -/
theorem lambertZeroBlockLeft_valuation (h k N : ℕ) (i : Fin h) (v : Fin (k+2*N)) :
    Valued.v (lambertZeroBlockLeft K h k N i v) ≤
      WithZero.exp (-((i.val : ℤ)*lambertSlotNode k v.val)) := by
  unfold lambertZeroBlockLeft
  rw [map_mul, lambertZeroBase_pow_valuation, Nat.cast_mul]
  have hc : Valued.v (if v.val < k ∨ (v.val-k)%2=0 then 1 else (i.val : LaurentSeries K)) ≤ 1 := by
    split_ifs
    · rw [map_one]
    · exact laurentNatCast_valuation_le i.val
  simpa only [one_mul] using mul_le_mul' hc (le_refl
    (WithZero.exp (-((i.val : ℤ)*lambertSlotNode k v.val))))

/-- Each compressed weighted entry has the combined order of its monomial and finite-part weight. -/
theorem lambertTranslatedZeroBlockRight_valuation (Z : LaurentSeries K) (hZ : Valued.v Z ≤ 1)
    (h k L s N : ℕ) (v : Fin (k+2*N)) (r : Fin h) :
    Valued.v (lambertTranslatedZeroBlockRight Z h k L s N v r) ≤
      WithZero.exp (-((lambertSlotNode k v.val : ℤ)*(r.val+s)+
        lambertZeroWeightOrder k L (lambertSlotNode k v.val))) := by
  have hw := lambertZeroBlock_weights Z hZ k L (lambertSlotNode k v.val)
  have hc : Valued.v (if v.val < k ∨ (v.val-k)%2=0 then
      lambertZeroBlockW Z k L (lambertSlotNode k v.val) +
        ((r.val+s : ℕ) : LaurentSeries K)*lambertZeroBlockC K k L (lambertSlotNode k v.val)
      else lambertZeroBlockC K k L (lambertSlotNode k v.val)) ≤
      WithZero.exp (-lambertZeroWeightOrder k L (lambertSlotNode k v.val)) := by
    split_ifs
    · apply Valuation.map_add_le Valued.v hw.1
      rw [map_mul]
      simpa only [one_mul] using mul_le_mul' (laurentNatCast_valuation_le (K := K) (r.val+s)) hw.2
    · exact hw.2
  unfold lambertTranslatedZeroBlockRight
  rw [map_mul, lambertZeroBase_pow_valuation, Nat.cast_mul]
  calc
    _ ≤ WithZero.exp (-lambertZeroWeightOrder k L (lambertSlotNode k v.val))*
        WithZero.exp (-(((r.val+s : ℕ) : ℤ)*lambertSlotNode k v.val)) := mul_le_mul' hc le_rfl
    _ = _ := by rw [← WithZero.exp_add]; congr 1; push_cast; ring

/-- A compressed translated block obeys any lower bound on all its injective permutation costs. -/
theorem lambertTranslatedZeroBlock_det_valuation (Z : LaurentSeries K) (hZ : Valued.v Z ≤ 1)
    (h k L s N : ℕ) (E : ℤ)
    (hc : ∀ (f : Fin h → Fin (k+2*N)), Function.Injective f →
      ∀ σ : Equiv.Perm (Fin h), -E ≤
        ∑ r : Fin h, (((σ r).val : ℤ)*lambertSlotNode k (f r).val +
          (lambertSlotNode k (f r).val : ℤ)*(r.val+s) +
          lambertZeroWeightOrder k L (lambertSlotNode k (f r).val))) :
    Valued.v (lambertZeroBlockLeft K h k N *
      lambertTranslatedZeroBlockRight Z h k L s N).det ≤ WithZero.exp E := by
  have he := laurentRectangularDeterminant_valuation_le
    (lambertZeroBlockLeft K h k N) (lambertTranslatedZeroBlockRight Z h k L s N)
    (fun i v => (i.val : ℤ)*lambertSlotNode k v.val)
    (fun v r => (lambertSlotNode k v.val : ℤ)*(r.val+s)+
      lambertZeroWeightOrder k L (lambertSlotNode k v.val))
    (-E) (lambertZeroBlockLeft_valuation h k N)
    (lambertTranslatedZeroBlockRight_valuation Z hZ h k L s N)
    (fun f hf σ => by simpa only [add_assoc] using hc f hf σ)
  simpa only [neg_neg] using he

/-- A translated finite block moment sums evaluation and scaled-derivative contributions. -/
def lambertZeroBlockMoment (Z : LaurentSeries K) (k h N r : ℕ) : LaurentSeries K :=
  ∑ j ∈ range N, (lambertZeroBlockW Z k h j+(r : LaurentSeries K)*lambertZeroBlockC K k h j)*
    lambertZeroBase K ^ (r*j)

private theorem sum_pairs {R : Type*} [AddCommMonoid R] (f : ℕ → R) (N : ℕ) :
    (∑ v ∈ range (2*N), f v) = ∑ j ∈ range N, (f (2*j)+f (2*j+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)=2*N+1+1 by omega]
    simp only [sum_range_succ, ih]
    exact add_assoc _ _ _

/-- Multiplication of the compressed blocks gives the actual translated finite-part moment matrix. -/
theorem lambertTranslatedZeroBlock_mul (Z : LaurentSeries K) (h k L s N : ℕ) :
    lambertZeroBlockLeft K h k N * lambertTranslatedZeroBlockRight Z h k L s N =
      Matrix.of (fun i j : Fin h => lambertZeroBlockMoment Z k L (k+N) (i.val+j.val+s)) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  let f : ℕ → LaurentSeries K := fun v =>
    (if v < k ∨ (v-k)%2=0 then 1 else (i.val : LaurentSeries K))*
      lambertZeroBase K ^ (i.val*lambertSlotNode k v)*
      ((if v < k ∨ (v-k)%2=0 then
        lambertZeroBlockW Z k L (lambertSlotNode k v)+
          ((j.val+s : ℕ) : LaurentSeries K)*lambertZeroBlockC K k L (lambertSlotNode k v)
        else lambertZeroBlockC K k L (lambertSlotNode k v))*
        lambertZeroBase K ^ ((j.val+s)*lambertSlotNode k v))
  change (∑ v : Fin (k+2*N), f v.val) = _
  rw [Fin.sum_univ_eq_sum_range f, sum_range_add, sum_pairs]
  simp only [Matrix.of_apply, lambertZeroBlockMoment, sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro v hv
    have hv := mem_range.mp hv
    have hc : lambertZeroBlockC K k L v = 0 := by
      unfold lambertZeroBlockC
      rw [dif_neg (by omega)]
    dsimp [f]
    simp only [lambertSlotNode_of_lt k v hv, if_pos (Or.inl hv), hc]
    simp only [mul_zero, add_zero, one_mul]
    rw [show (i.val+j.val+s)*v = i.val*v+(j.val+s)*v by ring, pow_add]
    ring
  · apply sum_congr rfl
    intro v _
    have ho : ¬k+(2*v+1) < k := by omega
    have he' : (k+2*v-k)%2=0 := by omega
    have ho' : (k+(2*v+1)-k)%2≠0 := by omega
    have ne : lambertSlotNode k (k+2*v) = k+v := by rw [lambertSlotNode_of_le k _ (by omega)]; omega
    have no : lambertSlotNode k (k+(2*v+1)) = k+v := by rw [lambertSlotNode_of_le k _ (by omega)]; omega
    dsimp [f]
    simp only [if_pos (Or.inr he'), if_neg (not_or.mpr ⟨ho, ho'⟩), ne, no]
    simp only [one_mul, Nat.cast_add, Nat.add_mul, pow_add]
    ring

/-- Every injective compressed-slot selection satisfies the translated capacity-constrained endpoint bound. -/
theorem lambertZero_selection_cost_bound (h k M : ℕ)
    (f : Fin h → Fin M) (hf : Function.Injective f) (σ : Equiv.Perm (Fin h)) :
    -lambertZeroExponent h k ≤
      ∑ r : Fin h, (((σ r).val : ℤ)*lambertSlotNode k (f r).val +
        (lambertSlotNode k (f r).val : ℤ)*(r.val+k) +
          lambertZeroWeightOrder k h (lambertSlotNode k (f r).val)) := by
  apply slotSelection_cost_bound h M (lambertSlotNode k) (lambertSlotNode_mono k)
    (lambertZeroWeightOrder k h) k (-lambertZeroExponent h k) ?_ f hf σ
  intro j hj
  unfold lambertZeroExponent
  rw [neg_neg]
  exact sum_le_sum (fun r _ => lambertZeroCost_min h k r.val (j r) r.isLt (hj r))

/-- The compressed right block attaches the actual translated finite-part weights to each evaluation or derivative slot. -/
def lambertZeroBlockRight (Z : LaurentSeries K) (h k N : ℕ) :
    Matrix (Fin (k+2*N)) (Fin h) (LaurentSeries K) :=
  lambertTranslatedZeroBlockRight Z h k h k N

/-- The finite compressed determinant obeys the translated endpoint bound for every natural pole offset and rank. -/
theorem lambertZeroBlock_det_valuation (Z : LaurentSeries K) (hZ : Valued.v Z ≤ 1)
    (h k N : ℕ) :
    Valued.v (lambertZeroBlockLeft K h k N * lambertZeroBlockRight Z h k N).det ≤
      WithZero.exp (lambertZeroExponent h k) := by
  exact lambertTranslatedZeroBlock_det_valuation Z hZ h k h k N
    (lambertZeroExponent h k) (lambertZero_selection_cost_bound h k (k+2*N))

/-- Multiplication of the compressed blocks gives the actual translated finite-part moment matrix. -/
theorem lambertZeroBlock_mul (Z : LaurentSeries K) (h k N : ℕ) :
    lambertZeroBlockLeft K h k N * lambertZeroBlockRight Z h k N =
      Matrix.of (fun i j : Fin h => lambertZeroBlockMoment Z k h (k+N) (i.val+j.val+k)) := by
  exact lambertTranslatedZeroBlock_mul Z h k h k N

end
end Lambert
