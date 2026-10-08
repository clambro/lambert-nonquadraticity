import Lambert.Arithmetic.RatFuncSpecializationExtension

/-!
# Specialization on rational functions regular at a point

Evaluation is a ring homomorphism on the subring of functions with no pole at
the chosen point. Polynomial coefficient maps retain this domain restriction.
-/
namespace Lambert
noncomputable section
open Polynomial
open scoped Classical
variable {K : Type*} [Field K]

/-- Mapping coefficients into a subring and forgetting that restriction gives
an equivalence onto the polynomials whose coefficients lie in that subring. -/
def polynomialSubringEquiv {R : Type*} [CommRing R] (S : Subring R) :
    S[X] ≃+* Polynomial.liftsRing S.subtype :=
  RingEquiv.ofBijective (Polynomial.mapRingHom S.subtype).rangeRestrict
    ⟨fun _ _ he => (Polynomial.map_injective S.subtype Subtype.val_injective)
      (congrArg Subtype.val he), RingHom.rangeRestrict_surjective _⟩

/-- A homomorphism on a coefficient subring acts on all polynomials whose
coefficients belong to that subring. -/
def polynomialSubringMap {R L : Type*} [CommRing R] [CommRing L]
    (S : Subring R) (φ : S →+* L) : Polynomial.liftsRing S.subtype →+* L[X] :=
  (Polynomial.mapRingHom φ).comp (polynomialSubringEquiv S).symm.toRingHom

/-- Coefficientwise subring transport agrees with the original polynomial after
forgetting the coefficient restriction. -/
theorem polynomialSubringEquiv_symm_map {R : Type*} [CommRing R] (S : Subring R)
    (p : Polynomial.liftsRing S.subtype) :
    ((polynomialSubringEquiv S).symm p).map S.subtype = p.val :=
  congrArg Subtype.val ((polynomialSubringEquiv S).apply_symm_apply p)

/-- A transported coefficient is the homomorphic image of the same original coefficient. -/
theorem polynomialSubringMap_coeff {R L : Type*} [CommRing R] [CommRing L]
    (S : Subring R) (φ : S →+* L) (p : Polynomial.liftsRing S.subtype) (k : ℕ) :
    (polynomialSubringMap S φ p).coeff k =
      φ ⟨p.val.coeff k, by
        obtain ⟨P, hP⟩ := (Polynomial.mem_lifts (f := S.subtype) _).mp p.property
        rw [← hP, coeff_map]
        exact (P.coeff k).property⟩ := by
  change (((polynomialSubringEquiv S).symm p).map φ).coeff k = _
  rw [coeff_map]
  congr 1
  apply Subtype.ext
  have he := congrArg (fun P : R[X] => P.coeff k) (polynomialSubringEquiv_symm_map S p)
  simpa only [coeff_map, Subring.coe_subtype] using he

/-- Subring coefficient transport maps a constant polynomial to the transported constant. -/
theorem polynomialSubringMap_C {R L : Type*} [CommRing R] [CommRing L]
    (S : Subring R) (φ : S →+* L) (f : S) :
    polynomialSubringMap S φ ⟨C f.val, Polynomial.C_mem_lifts S.subtype f⟩ = C (φ f) := by
  have he : (⟨C f.val, Polynomial.C_mem_lifts S.subtype f⟩ : Polynomial.liftsRing S.subtype) =
      polynomialSubringEquiv S (C f) := by
    apply Subtype.ext
    change C f.val = (C f).map S.subtype
    rw [Polynomial.map_C]
    rfl
  rw [he]
  change (((polynomialSubringEquiv S).symm (polynomialSubringEquiv S (C f))).map φ) = _
  rw [RingEquiv.symm_apply_apply, Polynomial.map_C]

/-- Subring coefficient transport fixes the polynomial variable. -/
theorem polynomialSubringMap_X {R L : Type*} [CommRing R] [CommRing L]
    (S : Subring R) (φ : S →+* L) :
    polynomialSubringMap S φ ⟨X, Polynomial.X_mem_lifts S.subtype⟩ = X := by
  have he : (⟨X, Polynomial.X_mem_lifts S.subtype⟩ : Polynomial.liftsRing S.subtype) =
      polynomialSubringEquiv S X := by
    apply Subtype.ext
    change (X : R[X]) = (X : S[X]).map S.subtype
    rw [Polynomial.map_X]
  rw [he]
  change (((polynomialSubringEquiv S).symm (polynomialSubringEquiv S X)).map φ) = _
  rw [RingEquiv.symm_apply_apply, Polynomial.map_X]

end
end Lambert
