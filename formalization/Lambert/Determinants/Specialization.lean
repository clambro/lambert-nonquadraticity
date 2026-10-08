import Lambert.Arithmetic.RatFuncSpecialization
import Lambert.Determinants.DenominatorSupport

/-!
# Extension-field specialization of translated Lambert determinants

Injectivity of the powers ensures that every denominator in the augmented
identity is regular. Evaluation is performed only on that regular subring.
-/
namespace Lambert
noncomputable section
open Polynomial Matrix Finset
open scoped Classical
variable {K : Type} [Field K] [CharZero K]

private abbrev S (q : K) := ratFuncRegularAt₂ (Rat.castHom K) q
private abbrev P (q : K) := Polynomial.liftsRing (S q).subtype
private abbrev φ (q : K) := ratFuncSpecialization₂ (Rat.castHom K) q
private abbrev ψ (q : K) := polynomialSubringMap (S q) (φ q)

private theorem qmem (q : K) : (RatFunc.X : RatFunc ℚ) ∈ S q :=
  ratFuncRegularAt₂_polynomial (Rat.castHom K) q X

private theorem rmem (q : K) (hq : Function.Injective (fun n : ℕ => q^n)) (n : ℕ) :
    1 / ((RatFunc.X : RatFunc ℚ) ^ (n + 1) - 1) ∈ S q := by
  have hn : q ^ (n + 1) - 1 ≠ 0 := sub_ne_zero.mpr
    (by intro he; have hh := hq (he.trans (pow_zero q).symm); omega)
  have he := ratFuncRegularAt₂_inverse (Rat.castHom K) q (X ^ (n + 1) - 1) (by simpa using hn)
  change ((algebraMap ℚ[X] (RatFunc ℚ)) (X ^ (n + 1) - 1))⁻¹ ∈ S q at he
  rw [map_sub, map_pow, RatFunc.algebraMap_X, map_one] at he
  simpa only [one_div] using he

private theorem dmem (q : K) (hq : Function.Injective (fun n : ℕ => q^n)) (i j : ℕ) (hij : i < j) :
    ((RatFunc.X : RatFunc ℚ) ^ j - RatFunc.X ^ i)⁻¹ ∈ S q := by
  have hn : q ^ j - q ^ i ≠ 0 := sub_ne_zero.mpr (by intro he; have := hq he; omega)
  have he := ratFuncRegularAt₂_inverse (Rat.castHom K) q (X ^ j - X ^ i) (by simpa using hn)
  change ((algebraMap ℚ[X] (RatFunc ℚ)) (X ^ j - X ^ i))⁻¹ ∈ S q at he
  rwa [map_sub, map_pow, map_pow, RatFunc.algebraMap_X] at he

private def Q (q : K) : S q := ⟨RatFunc.X, qmem q⟩
private theorem Q_eval (q : K) : φ q (Q q) = q := RatFunc.eval_X _ _

private theorem reciprocal_eval (q : K) (hq : Function.Injective (fun n : ℕ => q^n)) (n : ℕ) :
    φ q ⟨1 / ((RatFunc.X : RatFunc ℚ) ^ (n + 1) - 1), rmem q hq n⟩ =
      1 / (q ^ (n + 1) - 1) := by
  let R : S q := ⟨1 / ((RatFunc.X : RatFunc ℚ) ^ (n + 1) - 1), rmem q hq n⟩
  have he : ((Q q) ^ (n + 1) - 1) * R = 1 := by
    apply Subtype.ext
    exact mul_one_div_cancel (ratFunc_X_pow_sub_one_ne_zero n)
  have hm := congrArg (φ q) he
  rw [map_mul, map_sub, map_pow, map_one, Q_eval] at hm
  exact (eq_div_iff (sub_ne_zero.mpr (by intro he; have hh := hq (he.trans (pow_zero q).symm); omega))).mpr
    (by simpa only [mul_comm] using hm)

private def entry (q : K) (hq : Function.Injective (fun n : ℕ => q^n)) (i j : ℕ) : P q :=
  ⟨lambertPoleEntry RatFunc.X i j,
    lambertPoleEntry_mem_lifts (S q) (qmem q) (rmem q hq) i j⟩

private theorem entry_eval (q : K) (hq : Function.Injective (fun n : ℕ => q^n)) (i j : ℕ) :
    ψ q (entry q hq i j) = lambertPoleEntry q i j := by
  have hp : geometricMomentPrefix (RatFunc.X : RatFunc ℚ) j ∈ S q :=
    (S q).sum_mem fun n _ => rmem q hq n
  have hprefix : φ q ⟨geometricMomentPrefix (RatFunc.X : RatFunc ℚ) j, hp⟩ =
      geometricMomentPrefix q j := by
    have he : (⟨geometricMomentPrefix (RatFunc.X : RatFunc ℚ) j, hp⟩ : S q) =
        ∑ n ∈ range j, ⟨1 / (RatFunc.X ^ (n + 1) - 1), rmem q hq n⟩ := by
      apply Subtype.ext
      simp [geometricMomentPrefix]
    rw [he, map_sum]
    exact sum_congr rfl (fun n _ => reciprocal_eval q hq n)
  induction i with
  | zero =>
    have he : entry q hq 0 j =
        (⟨X, Polynomial.X_mem_lifts (S q).subtype⟩ : P q) -
        ⟨C (geometricMomentPrefix RatFunc.X j), Polynomial.C_mem_lifts (S q).subtype ⟨_, hp⟩⟩ := rfl
    rw [he, map_sub, polynomialSubringMap_X]
    have hc := polynomialSubringMap_C (S q) (φ q) ⟨_, hp⟩
    change ψ q ⟨C (geometricMomentPrefix RatFunc.X j), _⟩ = C (φ q ⟨_, hp⟩) at hc
    rw [hc, hprefix, lambertPoleEntry_zero]
  | succ i ih =>
    let c : S q := (Q q) ^ j
    let r : S q := ⟨1 / (RatFunc.X ^ (i + 1) - 1), rmem q hq i⟩
    have he : entry q hq (i + 1) j =
        (⟨C c.val, Polynomial.C_mem_lifts (S q).subtype c⟩ : P q) * entry q hq i j -
        ⟨C r.val, Polynomial.C_mem_lifts (S q).subtype r⟩ := rfl
    rw [he, map_sub, map_mul, polynomialSubringMap_C, polynomialSubringMap_C, ih]
    have hc : φ q c = q ^ j := by dsimp [c]; rw [map_pow, Q_eval]
    rw [hc, show φ q r = 1 / (q ^ (i + 1) - 1) from reciprocal_eval q hq i]
    rfl

/-- Distinct powers of an extension-field base guarantee regularity of every translated determinant coefficient. -/
theorem lambertPoleDeterminant_coeff_regular (q : K)
    (hq : Function.Injective (fun n : ℕ => q^n)) (h k d s i : ℕ) :
    (lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h+d) s).coeff i ∈
      ratFuncRegularAt₂ (Rat.castHom K) q :=
  lambertPoleDeterminant_coeff_mem_subring (S q) (qmem q) (rmem q hq)
    (dmem q hq) h k d s i

private theorem determinant_eval (q : K) (hq : Function.Injective (fun n : ℕ => q^n)) (h k d s : ℕ) :
    ∃ D : P q, D.val = lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s ∧
      ψ q D = lambertPoleDeterminant q h k (h + d) s := by
  let : Infinite K := Infinite.of_injective (fun n : ℕ => q^n) hq
  have hD : lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s ∈ P q := by
    apply (Polynomial.lifts_iff_coeff_lifts _).mpr
    intro a
    have hc := lambertPoleDeterminant_coeff_regular q hq h k d s a
    exact ⟨⟨(lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s).coeff a, hc⟩, rfl⟩
  let D : P q := ⟨_, hD⟩
  let A : Matrix (Fin (h + d)) (Fin (h + d)) (P q) := fun i j =>
    Fin.addCases (fun r => entry q hq (r.val + s) (k+j.val))
      (fun r => ⟨C (((Q q) ^ ((k+j.val) * r.val)).val),
        Polynomial.C_mem_lifts (S q).subtype ((Q q) ^ ((k+j.val) * r.val))⟩) i
  let V : S q := (vandermonde (fun j : Fin (h + d) => (Q q) ^ (k+j.val))).det
  let c : S q := (lambertAugmentedSign h d : ℤ) * V
  have hV : V.val = (vandermonde (fun j : Fin (h + d) => (RatFunc.X : RatFunc ℚ) ^ (k+j.val))).det := by
    exact (S q).subtype.map_det _
  have hA : A.det.val = (lambertAugmentedMatrix (RatFunc.X : RatFunc ℚ) h k d s).det := by
    rw [show A.det.val = ((P q).subtype.mapMatrix A).det from (P q).subtype.map_det A]
    congr 1
    apply Matrix.ext
    intro i j
    change (A i j).val = _
    refine Fin.addCases ?_ ?_ i
    · intro r
      simp [A, lambertAugmentedMatrix, entry]
    · intro r
      simp [A, lambertAugmentedMatrix, Q]
  have hid : A.det = (⟨C c.val, Polynomial.C_mem_lifts (S q).subtype c⟩ : P q) * D := by
    apply Subtype.ext
    change A.det.val = C c.val * D.val
    rw [hA]
    simpa only [c, Subring.coe_mul, Subring.coe_intCast, hV] using
      lambertAugmentedMatrix_det_formal h k d s
  have hm := congrArg (ψ q) hid
  rw [map_mul, polynomialSubringMap_C] at hm
  have ha : ψ q A.det = (lambertAugmentedMatrix q h k d s).det := by
    rw [(ψ q).map_det]
    congr 1
    apply Matrix.ext
    intro i j
    change ψ q (A i j) = _
    refine Fin.addCases ?_ ?_ i
    · intro r
      simpa [A, lambertAugmentedMatrix] using entry_eval q hq (r.val + s) (k+j.val)
    · intro r
      simp only [A, Fin.addCases_right]
      rw [polynomialSubringMap_C, map_pow, Q_eval]
      simp only [lambertAugmentedMatrix, Fin.addCases_right]
  have hv : φ q V = (vandermonde (fun j : Fin (h + d) => q ^ (k+j.val))).det := by
    rw [show φ q V = ((φ q).mapMatrix (vandermonde (fun j : Fin (h + d) => (Q q) ^ (k+j.val)))).det from
      (φ q).map_det _]
    congr 1
    apply Matrix.ext
    intro i j
    change φ q (((Q q) ^ (k+i.val)) ^ j.val) = (q ^ (k+i.val)) ^ j.val
    rw [map_pow, map_pow, Q_eval]
  have hc : φ q c = (lambertAugmentedSign h d : K) *
      (vandermonde (fun j : Fin (h + d) => q ^ (k+j.val))).det := by
    dsimp only [c]
    rw [map_mul, map_intCast, hv]
  rw [ha, hc] at hm
  have hn : (lambertAugmentedSign h d : K) *
      (vandermonde (fun j : Fin (h + d) => q ^ (k+j.val))).det ≠ 0 := by
    apply mul_ne_zero
    · have he : (lambertAugmentedSign h d : K) ^ 2 = 1 := by exact_mod_cast lambertAugmentedSign_sq h d
      intro hz
      simp [hz] at he
    · apply det_vandermonde_ne_zero_iff.mpr
      intro i j he
      exact Fin.ext (Nat.add_left_cancel (hq he))
  refine ⟨D, rfl, ?_⟩
  apply mul_left_cancel₀ (show (C ((lambertAugmentedSign h d : K) *
      (vandermonde (fun j : Fin (h + d) => q ^ (k+j.val))).det) : K[X]) ≠ 0 from
      fun hz => hn (Polynomial.C_injective (by simpa using hz)))
  rw [← hm]
  exact lambertAugmentedMatrix_det q h k d s
    (fun i j he => Fin.ext (Nat.add_left_cancel (hq he)))

/-- Specialization in a characteristic-zero field preserves every translated determinant coefficient when the base powers are distinct. -/
theorem lambertPoleDeterminant_coeff_specialize_of_pow_injective (q : K) (hq : Function.Injective (fun n : ℕ => q^n)) (h k d s a : ℕ) :
    RatFunc.eval (Rat.castHom K) q
      ((lambertPoleDeterminant (RatFunc.X : RatFunc ℚ) h k (h + d) s).coeff a) =
      (lambertPoleDeterminant q h k (h + d) s).coeff a := by
  obtain ⟨D, hD, he⟩ := determinant_eval q hq h k d s
  have hc := polynomialSubringMap_coeff (S q) (φ q) D a
  rw [he] at hc
  change (lambertPoleDeterminant q h k (h + d) s).coeff a = RatFunc.eval (Rat.castHom K) q (D.val.coeff a) at hc
  rw [hD] at hc
  exact hc.symm

end
end Lambert
