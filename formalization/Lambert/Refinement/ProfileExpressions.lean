import Lambert.Refinement.ProfileCertificate
import Lambert.Refinement.Baseline

/-! # Exact arithmetic expressions for the six Lambert presentations -/
namespace Lambert
noncomputable section
open Finset
open scoped Classical
open LambertProfileExpression

/-- The cyclotomic exponent expression retains both the filtration and the corrected residue bound. -/
def lambertRefinementExponentExpression (h A b d s : ℕ) : LambertProfileExpression :=
  .sub (.add (.add (.linear (h,0)) (.deficit (h+d) 1)) (.deficit A 1))
    (.max (.deficit (h+d+A) 2)
      (.max
        (.sub (.sub (.linear (h,0))
          (.sub (.residue (s+h+A) d) (.residue s d)))
          (.max (.sub (.linear (b+h+d,0)) (.max (.linear (b,0)) (.linear (0,1))))
            (.linear (0,0))))
        (.linear (0,0))))

/-- The transpose multiplier's expression is the signed difference of its four collision sums. -/
def lambertRefinementTransportExpression (h A d : ℕ) : LambertProfileExpression :=
  .sub (.sub (.add (.deficit (h+A) 1) (.deficit d 1)) (.deficit (h+d) 1))
    (.deficit A 1)

/-- The transport expression evaluates to the exact signed multiplier order. -/
theorem lambertRefinementTransportExpression_eval (h A d N n : ℕ) :
    (lambertRefinementTransportExpression h A d).eval N n =
      (lambertRefinementTransportOrder (h*N) (A*N) (d*N) n : ℝ) := by
  simp only [lambertRefinementTransportExpression, LambertProfileExpression.eval,
    lambertRefinementTransportOrder, Int.cast_add, Int.cast_sub, Int.cast_natCast,
    ← Nat.add_mul, one_mul]

/-- The profile expression evaluates to the exact signed coefficient exponent at every scale. -/
theorem lambertRefinementExponentExpression_eval (h A b d s N n : ℕ) :
    (lambertRefinementExponentExpression h A b d s).eval N n =
      (lambertRefinementCyclotomicExponent (h*N) (A*N) (b*N) (d*N) (s*N) n : ℝ) := by
  have hR := lambertRectangularResidualCount_prefix ((h+A)*N) (d*N) (s*N) n
  have hRR : (lambertRectangularResidualCount ((h+A)*N) (d*N) (s*N) n : ℝ) =
      (lambertResidualPrefix ((s+h+A)*N) (d*N) n : ℝ)-lambertResidualPrefix (s*N) (d*N) n := by
    rw [← Nat.add_mul, ← Nat.add_assoc] at hR
    exact_mod_cast (show (lambertRectangularResidualCount ((h+A)*N) (d*N) (s*N) n : ℤ) =
      lambertResidualPrefix ((s+h+A)*N) (d*N) n-lambertResidualPrefix (s*N) (d*N) n by omega)
  simp only [lambertRefinementCyclotomicExponent, Int.cast_add, Int.cast_sub, Int.cast_natCast]
  simp only [lambertRefinementLocalOrder, Nat.cast_max, Nat.sub_sub, natCast_sub_eq_max,
    Nat.cast_add, Nat.cast_mul]
  simp only [lambertRefinementExponentExpression, LambertProfileExpression.eval,
    RationalAffine.eval, Rat.cast_natCast, Rat.cast_zero, Rat.cast_one,
    zero_mul, one_mul, add_zero, zero_add]
  simp only [← Nat.add_mul, Nat.mul_comm (2*n), hRR]
  push_cast
  congr 2
  ring_nf

/-- The six finite expressions encode the six exact transported presentations. -/
def lambertRefinementOrbitExpression (j : Fin 6) : LambertProfileExpression :=
  let t := lambertRefinementTransportExpression 500 0 16
  let u := lambertRefinementTransportExpression 500 27 43
  let v := lambertRefinementTransportExpression 500 41 25
  ![lambertRefinementExponentExpression 500 0 27 16 41,
    .sub (lambertRefinementExponentExpression 500 16 41 0 27) t,
    .sub (lambertRefinementExponentExpression 500 41 43 25 0) u,
    .sub (.sub (lambertRefinementExponentExpression 500 0 25 16 43) v) u,
    .sub (.sub (.sub (lambertRefinementExponentExpression 500 16 43 0 25) u) v) t,
    .sub (.sub (lambertRefinementExponentExpression 500 25 27 41 16) v) t] j

/-- Evaluating an orbit expression recovers the corresponding signed coefficient bound. -/
theorem lambertRefinementOrbitExpression_eval (j : Fin 6) (N n : ℕ) :
    (lambertRefinementOrbitExpression j).eval N n=(lambertRefinementOrbitExponent N n j : ℝ) := by
  fin_cases j <;>
    simp [lambertRefinementOrbitExpression, lambertRefinementOrbitExponent,
      LambertProfileExpression.eval, lambertRefinementExponentExpression_eval,
      lambertRefinementTransportExpression_eval]

end
end Lambert
