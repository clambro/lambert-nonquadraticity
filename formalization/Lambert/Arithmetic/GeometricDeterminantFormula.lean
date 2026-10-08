import Lambert.Arithmetic.CauchyBorderedDeterminant

/-!
# Shifted reciprocal-geometric determinants

Cauchy border quotients retain an arbitrary nonnegative moment shift.
-/
namespace Lambert
open Polynomial Matrix Finset

/-- The quotient of successive reciprocal-geometric Hankel determinants is an exact Cauchy nodal product with the new column weight retained. -/
theorem shiftedGeometricHankel_det_quotient {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] (q : K) (hq : 1 < q) (n s₀ : ℕ) :
    (Matrix.of fun i j : Fin (n + 1) => (q ^ (i.val + j.val + s₀ + 1) - 1)⁻¹).det /
      (Matrix.of fun i j : Fin n => (q ^ (i.val + j.val + s₀ + 1) - 1)⁻¹).det =
    (q ^ n)⁻¹ *
      ((Lagrange.nodal univ (fun i : Fin n => q ^ (i.val + s₀ + 1))).eval (q ^ (n + s₀ + 1)) *
        (Lagrange.nodal univ (fun j : Fin n => (q ^ j.val)⁻¹)).eval ((q ^ n)⁻¹)) /
      ((q ^ (n + s₀ + 1) - (q ^ n)⁻¹) *
        (Lagrange.nodal univ (fun j : Fin n => (q ^ j.val)⁻¹)).eval (q ^ (n + s₀ + 1)) *
        (Lagrange.nodal univ (fun i : Fin n => q ^ (i.val + s₀ + 1))).eval ((q ^ n)⁻¹)) := by
  classical
  let x : Fin n → K := fun i => q ^ (i.val + s₀ + 1)
  let y : Fin n → K := fun j => (q ^ j.val)⁻¹
  let a := q ^ (n + s₀ + 1)
  let b := (q ^ n)⁻¹
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans hq)
  have hcross (r s : ℕ) (hr : 0 < r) : q ^ r ≠ (q ^ s)⁻¹ := by
    intro he
    have hh := congrArg (fun t : K => t * q ^ s) he
    rw [inv_mul_cancel₀ (pow_ne_zero _ hq0), ← pow_add] at hh
    exact (ne_of_gt (one_lt_pow₀ hq (by omega))) hh
  have hx : Function.Injective x := by
    intro i j he
    apply Fin.ext
    have := (pow_right_strictMono₀ hq).injective he
    omega
  have hy : Function.Injective y := by
    intro i j he
    exact Fin.ext ((pow_right_strictMono₀ hq).injective (inv_injective he))
  have hxy : ∀ i j, x i ≠ y j := fun i j => hcross _ _ (by omega)
  have hab : a ≠ b := hcross _ _ (by omega)
  have hay : ∀ j, a ≠ y j := fun j => hcross _ _ (by omega)
  have hbx : ∀ i, b ≠ x i := fun i => (hcross _ _ (by omega)).symm
  have hentry (r s : ℕ) (hr : 0 < r) :
      (q ^ (r + s) - 1)⁻¹ = (q ^ r - (q ^ s)⁻¹)⁻¹ * (q ^ s)⁻¹ := by
    have hd := sub_ne_zero.mpr (hcross r s hr)
    have hp : q ^ r * q ^ s - 1 ≠ 0 := by
      rw [← pow_add]
      exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ hq (by omega)))
    rw [pow_add]
    field_simp
  have hlower : (Matrix.of fun i j : Fin n => (q ^ (i.val + j.val + s₀ + 1) - 1)⁻¹) =
      cauchyMatrix x y * Matrix.diagonal y := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.of_apply, Matrix.mul_diagonal, cauchyMatrix, x, y]
    rw [show i.val + j.val + s₀ + 1 = (i.val + s₀ + 1) + j.val by omega]
    exact hentry _ _ (by omega)
  have hupper : (Matrix.of fun i j : Fin (n + 1) =>
      (q ^ (i.val + j.val + s₀ + 1) - 1)⁻¹).det =
      (Matrix.fromBlocks (cauchyMatrix x y * Matrix.diagonal y)
        (fun i (_ : Unit) => (x i - b)⁻¹ * b)
        (fun (_ : Unit) j => (a - y j)⁻¹ * y j)
        (fun (_ _ : Unit) => (a - b)⁻¹ * b)).det := by
    rw [matrix_det_last_border]
    congr 1
    apply Matrix.ext
    intro i j
    rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
    · change (q ^ (i.val + j.val + s₀ + 1) - 1)⁻¹ =
        (cauchyMatrix x y * Matrix.diagonal y) i j
      rw [Matrix.mul_diagonal]
      change (q ^ (i.val + j.val + s₀ + 1) - 1)⁻¹ =
        (q ^ (i.val + s₀ + 1) - (q ^ j.val)⁻¹)⁻¹ * (q ^ j.val)⁻¹
      rw [show i.val + j.val + s₀ + 1 = (i.val + s₀ + 1) + j.val by omega]
      exact hentry _ _ (by omega)
    · change (q ^ (i.val + n + s₀ + 1) - 1)⁻¹ =
        (q ^ (i.val + s₀ + 1) - (q ^ n)⁻¹)⁻¹ * (q ^ n)⁻¹
      rw [show i.val + n + s₀ + 1 = (i.val + s₀ + 1) + n by omega]
      exact hentry _ _ (by omega)
    · change (q ^ (n + j.val + s₀ + 1) - 1)⁻¹ =
        (q ^ (n + s₀ + 1) - (q ^ j.val)⁻¹)⁻¹ * (q ^ j.val)⁻¹
      rw [show n + j.val + s₀ + 1 = (n + s₀ + 1) + j.val by omega]
      exact hentry _ _ (by omega)
    · change (q ^ (n + n + s₀ + 1) - 1)⁻¹ =
        (q ^ (n + s₀ + 1) - (q ^ n)⁻¹)⁻¹ * (q ^ n)⁻¹
      rw [show n + n + s₀ + 1 = (n + s₀ + 1) + n by omega]
      exact hentry _ _ (by omega)
  rw [hupper, hlower, borderedDeterminant_column_weights _
    (cauchyMatrix_det_ne_zero x y hx hy hxy) _ _ _ _
    (fun j => inv_ne_zero (pow_ne_zero _ hq0))]
  rw [mul_div_assoc, cauchyMatrix_bordered_det_quotient n x y hx hy hxy a b hab hay hbx]
  dsimp only [x, y, a, b]
  ring

/-- The reciprocal-geometric norm quotient is a positive-power square product, including the empty moment matrix case. -/
theorem shiftedGeometricHankel_det_quotient_product {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] (q : K) (hq : 1 < q) (n s₀ : ℕ) :
    (Matrix.of fun i j : Fin (n + 1) => (q ^ (i.val + j.val + s₀ + 1) - 1)⁻¹).det /
      (Matrix.of fun i j : Fin n => (q ^ (i.val + j.val + s₀ + 1) - 1)⁻¹).det =
    (q ^ (2 * n + s₀ + 1) - 1)⁻¹ *
      ∏ i : Fin n, q ^ (2 * i.val + s₀ + 1) *
        ((q ^ (n - i.val) - 1) / (q ^ (n + i.val + s₀ + 1) - 1)) ^ 2 := by
  classical
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans hq)
  have hcross (r s : ℕ) (hr : 0 < r) : q ^ r ≠ (q ^ s)⁻¹ := by
    intro he
    have hh := congrArg (fun t : K => t * q ^ s) he
    rw [inv_mul_cancel₀ (pow_ne_zero _ hq0), ← pow_add] at hh
    exact (ne_of_gt (one_lt_pow₀ hq (by omega))) hh
  let a := q ^ (n + s₀ + 1)
  let b := (q ^ n)⁻¹
  let x : Fin n → K := fun i => q ^ (i.val + s₀ + 1)
  let y : Fin n → K := fun i => (q ^ i.val)⁻¹
  have hform :
      (Matrix.of fun i j : Fin (n + 1) => (q ^ (i.val + j.val + s₀ + 1) - 1)⁻¹).det /
        (Matrix.of fun i j : Fin n => (q ^ (i.val + j.val + s₀ + 1) - 1)⁻¹).det =
      (b / (a - b)) * ∏ i : Fin n,
        ((a - x i) / (a - y i)) * ((b - y i) / (b - x i)) := by
    rw [shiftedGeometricHankel_det_quotient q hq n s₀]
    simp only [Lagrange.eval_nodal]
    rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_div_distrib]
    dsimp only [a, b, x, y]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  have hcorner : b / (a - b) = (q ^ (2 * n + s₀ + 1) - 1)⁻¹ := by
    have hd := sub_ne_zero.mpr (hcross (n + s₀ + 1) n (by omega))
    have hp : q ^ (2 * n + s₀ + 1) - 1 ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ hq (by omega)))
    dsimp only [a, b] at *
    rw [show 2 * n + s₀ + 1 = (n + s₀ + 1) + n by omega, pow_add] at hp ⊢
    field_simp
    simp only [pow_add, pow_succ]
    ring
  have hfactor (i : Fin n) :
      ((a - x i) / (a - y i)) * ((b - y i) / (b - x i)) =
      q ^ (2 * i.val + s₀ + 1) *
        ((q ^ (n - i.val) - 1) / (q ^ (n + i.val + s₀ + 1) - 1)) ^ 2 := by
    have hi : i.val ≤ n := Nat.le_of_lt i.isLt
    have hpn : q ^ n = q ^ i.val * q ^ (n - i.val) := by
      rw [← pow_add, Nat.add_sub_of_le hi]
    have ha : q ^ (n + s₀ + 1) = q ^ (s₀ + 1) * (q ^ i.val * q ^ (n - i.val)) := by
      rw [show n + s₀ + 1 = n + (s₀ + 1) by omega, pow_add, hpn]
      ring
    have hx : q ^ (i.val + s₀ + 1) = q ^ (s₀ + 1) * q ^ i.val := by rw [show i.val + s₀ + 1 = i.val + (s₀ + 1) by omega, pow_add]; ring
    have hpow : q ^ (2 * i.val + s₀ + 1) = q ^ (s₀ + 1) * (q ^ i.val) ^ 2 := by
      rw [show 2 * i.val + s₀ + 1 = 2 * i.val + (s₀ + 1) by omega, pow_add, pow_mul]
      ring
    have hden : q ^ (n + i.val + s₀ + 1) =
        q ^ (s₀ + 1) * (q ^ i.val) ^ 2 * q ^ (n - i.val) := by
      rw [show n + i.val + s₀ + 1 = (2 * i.val + s₀ + 1) + (n - i.val) by omega,
        pow_add, hpow]
    have hd1 := sub_ne_zero.mpr (hcross (n + s₀ + 1) i.val (by omega))
    have hd2 := sub_ne_zero.mpr ((hcross (i.val + s₀ + 1) n (by omega)).symm)
    have hd3 : q ^ (n + i.val + s₀ + 1) - 1 ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ hq (by omega)))
    dsimp only [a, b, x, y]
    simp only [ha, hx, hpn, hpow, hden] at hd1 hd2 hd3 ⊢
    have ht := pow_ne_zero i.val hq0
    have hz := pow_ne_zero (n - i.val) hq0
    generalize q ^ i.val = t at ht hd1 hd2 hd3 ⊢
    generalize q ^ (n - i.val) = z at hz hd1 hd2 hd3 ⊢
    have hneg : 1 - q ^ (s₀ + 1) * t ^ 2 * z ≠ 0 := by
      intro he
      apply hd3
      linear_combination -he
    field_simp [ht, hz, hd1, hd2, hd3, hneg]
    ring
  rw [hform, hcorner]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => hfactor i)


end Lambert
