import Lambert.Arithmetic.NumberFieldHeightBounds
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-! # Height extension from norms of denominator ideals -/
namespace Lambert
noncomputable section
open NumberField Finset

/-- For a quotient of algebraic integers, its finite denominator product times the norm of their common ideal equals the absolute norm of the denominator. -/
theorem finitePlaceDenominator_mul_idealNorm {K : Type*} [Field K] [NumberField K]
    (a b : 𝓞 K) (hb : b≠0) :
    finitePlaceDenominator ((a : K)/(b : K)) * (Ideal.span ({a,b} : Set (𝓞 K))).absNorm =
      |(Algebra.norm ℚ (b : K) : ℝ)| := by
  classical
  have hbK : (b : K)≠0 := by exact_mod_cast hb
  have hv (v : FinitePlace K) : v (b : K)*max (v ((a : K)/(b : K))) 1 =
      max (v (a : K)) (v (b : K)) := by
    rw [map_div₀, mul_max_of_nonneg _ _ (apply_nonneg _ _), mul_div_cancel₀ _ ((map_ne_zero _).mpr hbK), mul_one]
  have hi := NumberField.absNorm_mul_finprod_finitePlace_eq_one
    (x := ![a,b]) (by
      intro hz
      have he := congrFun hz 1
      exact hb (by simpa using he) : (![a,b] : Fin 2 → 𝓞 K)≠0)
  have hI : Set.range (![a,b] : Fin 2 → 𝓞 K)={a,b} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩; fin_cases i <;> simp
    · rintro (rfl|rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  have hmax (v : FinitePlace K) : (⨆ i : Fin 2, v ((![a,b] i : 𝓞 K) : K))=
      max (v (a : K)) (v (b : K)) := by
    have he (i : Fin 2) : v ((![a,b] i : 𝓞 K) : K) = ![v (a : K),v (b : K)] i := by
      fin_cases i <;> rfl
    simp only [he]
    exact eq_of_forall_ge_iff (by simp [ciSup_le_iff, Fin.forall_fin_two])
  rw [hI] at hi
  simp only [hmax] at hi
  have hprod : (∏ᶠ v : FinitePlace K, v (b : K))*finitePlaceDenominator ((a : K)/(b : K)) =
      ∏ᶠ v : FinitePlace K, max (v (a : K)) (v (b : K)) := by
    rw [finitePlaceDenominator, ← finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hbK)
      (finitePlace_max_hasFiniteMulSupport _)]
    exact finprod_congr hv
  rw [← hprod, FinitePlace.prod_eq_inv_abs_norm hbK, Rat.cast_inv, Rat.cast_abs] at hi
  have hn : |(Algebra.norm ℚ (b : K) : ℝ)|≠0 := abs_ne_zero.mpr (by
    exact_mod_cast ((Algebra.norm_ne_zero_iff (R := ℚ)).mpr hbK))
  field_simp at hi
  nlinarith [hi]

/-- The finite denominator product is raised to the relative degree under a number-field extension. -/
theorem finitePlaceDenominator_extension {K L : Type} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] (x : K) :
    finitePlaceDenominator (algebraMap K L x) =
      finitePlaceDenominator x ^ Module.finrank K L := by
  classical
  let : FiniteDimensional K L := FiniteDimensional.right ℚ K L
  obtain ⟨n,hn,a,ha,_⟩ := NumberField.exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow x
  have hb : (n : 𝓞 K)≠0 := by exact_mod_cast hn
  have hbL : (n : 𝓞 L)≠0 := by exact_mod_cast hn
  have hx : x=(a : K)/n := (eq_div_iff (by exact_mod_cast hn)).mpr (by simpa [mul_comm] using ha)
  let A : 𝓞 L := algebraMap (𝓞 K) (𝓞 L) a
  have hI : (Ideal.span ({A,(n : 𝓞 L)} : Set (𝓞 L))).absNorm =
      (Ideal.span ({a,(n : 𝓞 K)} : Set (𝓞 K))).absNorm ^ Module.finrank K L := by
    have he := Ideal.absNorm_algebraMap (𝓞 K) (S := 𝓞 L) (Ideal.span ({a,(n : 𝓞 K)} : Set (𝓞 K)))
    rw [← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L] at he
    simpa only [Ideal.map_span, Set.image_pair, map_natCast] using he
  have hk := finitePlaceDenominator_mul_idealNorm a (n : 𝓞 K) hb
  have hl := finitePlaceDenominator_mul_idealNorm A (n : 𝓞 L) hbL
  simp only [RingOfIntegers.coe_eq_algebraMap, map_natCast] at hk hl
  have hnorm : |(Algebra.norm ℚ (n : L) : ℝ)| =
      |(Algebra.norm ℚ (n : K) : ℝ)| ^ Module.finrank K L := by
    rw [← map_natCast (algebraMap K L), ← Algebra.norm_norm (S := K), Algebra.norm_algebraMap, map_pow,
      Rat.cast_pow, abs_pow]
  rw [hI, Nat.cast_pow, hnorm, ← hk, mul_pow] at hl
  have hI0 : (Ideal.span ({a,(n : 𝓞 K)} : Set (𝓞 K))).absNorm≠0 := by
    intro hz
    have he := Ideal.absNorm_eq_zero_iff.mp hz
    have hm : (n : 𝓞 K)∈Ideal.span ({a,(n : 𝓞 K)} : Set (𝓞 K)) := Ideal.subset_span (by simp)
    rw [he] at hm
    exact hb hm
  have he := mul_right_cancel₀ (pow_ne_zero (Module.finrank K L) (by exact_mod_cast hI0 :
    ((Ideal.span ({a,(n : 𝓞 K)} : Set (𝓞 K))).absNorm : ℝ)≠0)) hl
  dsimp [A] at he
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
    IsScalarTower.algebraMap_apply (𝓞 K) K L] at he
  rw [hx]
  simpa only [map_div₀, map_natCast, RingOfIntegers.coe_eq_algebraMap] using he

/-- The unnormalized logarithmic height multiplies by the relative degree under every number-field extension. -/
theorem numberField_logHeight_extension {K L : Type} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] (x : K) :
    Height.logHeight₁ (algebraMap K L x) =
      (Module.finrank K L : ℝ)*Height.logHeight₁ x := by
  rw [numberField_logHeight_eq_embeddings, numberField_logHeight_eq_embeddings,
    finitePlaceDenominator_extension, Real.log_pow, numberField_sum_embeddings_extension x (fun z => Real.log (max ‖z‖ 1))]
  ring

end
end Lambert
