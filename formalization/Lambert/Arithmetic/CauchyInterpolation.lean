import Mathlib.LinearAlgebra.Lagrange

/-! # Interpolation of Cauchy residues -/

namespace Lambert


open Finset Polynomial

noncomputable section

variable {K ι κ : Type*} [Field K] [DecidableEq ι]

/-- The barycentric coefficient attached to an interpolation polynomial at one node. -/
def cauchyResidueCoefficient (nodes : Finset ι) (v : ι → K)
    (P : K[X]) (i : ι) : K :=
  Lagrange.nodalWeight nodes v i * P.eval (v i)

/-- The degree-bounded parameter polynomial corresponding to arbitrary Cauchy residue coefficients. -/
def cauchyResidueParameter (nodes : Finset ι) (v c : ι → K) : K[X] :=
  Lagrange.interpolate nodes v (fun i => c i / Lagrange.nodalWeight nodes v i)

/-- The parameter polynomial has degree below the number of distinct denominator nodes. -/
theorem cauchyResidueParameter_degree_lt (nodes : Finset ι) (v c : ι → K)
    (hv : Set.InjOn v nodes) :
    (cauchyResidueParameter nodes v c).degree < nodes.card :=
  Lagrange.degree_interpolate_lt _ hv

/-- The parameter polynomial recovers each prescribed Cauchy residue exactly. -/
theorem cauchyResidueParameter_coefficient (nodes : Finset ι) (v c : ι → K)
    (hv : Set.InjOn v nodes) (i : ι) (hi : i ∈ nodes) :
    cauchyResidueCoefficient nodes v (cauchyResidueParameter nodes v c) i = c i := by
  rw [cauchyResidueCoefficient, cauchyResidueParameter,
    Lagrange.eval_interpolate_at_node _ hv hi]
  field_simp [Lagrange.nodalWeight_ne_zero hv hi]


/-- The Cauchy convolution determined by a polynomial and a finite set of nodes. -/
def cauchyResidueConvolution (nodes : Finset ι) (v : ι → K)
    (P : K[X]) (x : K) : K :=
  ∑ i ∈ nodes, cauchyResidueCoefficient nodes v P i / (x - v i)

/-- Away from the interpolation nodes, the rectangular Padé convolution is the exact
ratio of the interpolating polynomial to the nodal polynomial. -/
theorem cauchyResidueConvolution_eq_div (nodes : Finset ι) (v : ι → K)
    (P : K[X]) (hv : Set.InjOn v nodes) (hP : P.degree < nodes.card)
    (x : K) (hx : ∀ i ∈ nodes, x ≠ v i) :
    cauchyResidueConvolution nodes v P x =
      P.eval x / (Lagrange.nodal nodes v).eval x := by
  have hinterp := congrArg (fun Q : K[X] ↦ Q.eval x)
    (Lagrange.eq_interpolate hv hP :
      P = Lagrange.interpolate nodes v (fun i ↦ P.eval (v i)))
  rw [Lagrange.eval_interpolate_not_at_node _ hx] at hinterp
  have hnodal : (Lagrange.nodal nodes v).eval x ≠ 0 :=
    Lagrange.eval_nodal_not_at_node hx
  apply (mul_left_cancel₀ hnodal)
  rw [hinterp]
  field_simp [hnodal]
  simp only [cauchyResidueConvolution, cauchyResidueCoefficient, div_eq_mul_inv]

/-- A nodal polynomial divides a polynomial exactly when that polynomial vanishes at
every indexed node.  Injectivity rules out repeated linear factors. -/
theorem nodal_dvd_iff_eval_eq_zero (targets : Finset κ) (w : κ → K)
    (hw : Set.InjOn w targets) (P : K[X]) :
    Lagrange.nodal targets w ∣ P ↔ ∀ j ∈ targets, P.eval (w j) = 0 := by
  constructor
  · intro hdvd j hj
    exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd
      (Lagrange.eval_nodal_at_node hj)
  · intro hzero
    rw [Lagrange.nodal_eq]
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      have hwij : w i ≠ w j := fun heq ↦ hij (hw hi hj heq)
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero_of_ne hwij).isUnit
    · intro j hj
      exact Polynomial.dvd_iff_isRoot.mpr (hzero j hj)









end


end Lambert
