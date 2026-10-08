import Lambert.Arithmetic.LaurentSeriesLocalOrder
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Instances.Matrix

/-!
# Laurent limits with explicit order control

Increasing lower orders imply convergence in the Laurent valuation topology.
A fixed lower-order bound is closed under such limits.
-/

namespace Lambert
noncomputable section
open Filter
open scoped Topology WithZero
variable {K : Type*} [Field K]

/-- A sequence whose lower Laurent orders eventually exceed every natural
number tends to zero. -/
theorem laurent_tendsto_zero_of_orders (f : ℕ → LaurentSeries K)
    (hf : ∀ d : ℕ, ∀ᶠ N in atTop, Valued.v (f N) ≤ WithZero.exp (-(d : ℤ))) :
    Tendsto f atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero (LaurentSeries K) _).tendsto_right_iff]
  intro y _
  let e := MonoidWithZeroHom.ValueGroup₀.embedding (f := (.ofClass (Valued.v (R := LaurentSeries K))))
  have hy : e y.val ≠ 0 := by exact (map_ne_zero e).mpr (Units.ne_zero y)
  obtain ⟨d, hd⟩ := WithZero.exists_exp_neg_natCast_lt hy
  filter_upwards [hf d] with N hN
  change Valued.v.restrict (f N) < y.val
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact hN.trans_lt hd

/-- A fixed Laurent valuation bound passes to the limit of a sequence. -/
theorem laurent_valuation_le_of_tendsto (f : ℕ → LaurentSeries K) (a : LaurentSeries K)
    (D : ℤ) (hf : Tendsto f atTop (𝓝 a))
    (hb : ∀ᶠ N in atTop, Valued.v (f N) ≤ WithZero.exp (-D)) :
    Valued.v a ≤ WithZero.exp (-D) := by
  obtain ⟨c, hc⟩ := LaurentSeries.valuation_surjective K (WithZero.exp (-D))
  have hs : IsClosed {x : LaurentSeries K | Valued.v x ≤ WithZero.exp (-D)} := by
    rw [← hc]
    simpa only [Valuation.restrict_le_iff] using
      Valued.isClosed_closedBall (LaurentSeries K) (Valued.v.restrict c)
  exact hs.mem_of_tendsto hf hb

end
end Lambert
