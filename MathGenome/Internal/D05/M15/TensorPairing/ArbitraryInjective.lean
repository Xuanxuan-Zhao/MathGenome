import MathGenome.Internal.Specs.D05.M15.TensorPairing.ArbitraryInjective
import MathGenome.Internal.D05.M02.BasisExtension.Choice
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The canonical algebraic dual tensor pairing is injective in arbitrary dimension.
We expand the second dual factor in a (possibly infinite) basis. For each fixed
vector in the first space, the zero pairing is a zero functional on the second
space. Its basis coordinates are precisely the values of the finitely supported
first-factor coefficients. Thus every coefficient is the zero functional.
-/

namespace D05.M15.TensorPairing.ArbitraryInjective

open scoped TensorProduct

variable {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Extracting a second-factor basis coordinate commutes with first-slot evaluation. -/
lemma coefficient_evaluation [DecidableEq I] (b : Module.Basis I K (Module.Dual K W))
    (z : Module.Dual K V ⊗[K] Module.Dual K W) (v : V) (i : I) :
    (TensorProduct.equivFinsuppOfBasisRight b z i) v =
      b.repr (TensorProduct.lcurry (.id K) V W K (TensorProduct.dualDistrib K V W z) v) i := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul φ ψ =>
    have h : TensorProduct.lcurry (.id K) V W K (TensorProduct.dualDistrib K V W (φ ⊗ₜ[K] ψ)) v =
        φ v • ψ := by
      apply LinearMap.ext
      intro w
      exact TensorProduct.dualDistrib_apply φ ψ v w
    rw [h, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    simp [mul_comm]
  | add x y hx hy =>
    simp_all

theorem elementary_evaluation :
    Specs.D05.M15.TensorPairing.ArbitraryInjective.elementary_evaluation := by
  intro K V W _ _ _ _ _ φ ψ v w
  exact TensorProduct.dualDistrib_apply φ ψ v w

theorem eq_zero_of_evaluations_zero :
    Specs.D05.M15.TensorPairing.ArbitraryInjective.eq_zero_of_evaluations_zero := by
  intro K V W _ _ _ _ _ z hz
  classical
  -- Invoke the accepted unrestricted extension theorem on the empty subset.
  obtain ⟨T, _, b, _⟩ := D05.M02.BasisExtension.Choice.basis_extension
    (K := K) (V := Module.Dual K W) ∅ (by
      exact linearIndependent_empty_type)
  apply (TensorProduct.equivFinsuppOfBasisRight (M := Module.Dual K V) b).injective
  rw [map_zero]
  apply Finsupp.ext
  intro i
  apply LinearMap.ext
  intro v
  change (TensorProduct.equivFinsuppOfBasisRight b z i) v = 0
  have hv : TensorProduct.lcurry (.id K) V W K (TensorProduct.dualDistrib K V W z) v = 0 := by
    apply LinearMap.ext
    intro w
    exact hz v w
  have hc := coefficient_evaluation b z v i
  rw [hv, map_zero, Finsupp.zero_apply] at hc
  exact hc

theorem canonical_map_injective :
    Specs.D05.M15.TensorPairing.ArbitraryInjective.canonical_map_injective := by
  intro K V W _ _ _ _ _ x y hxy
  apply sub_eq_zero.mp
  apply eq_zero_of_evaluations_zero
  intro v w
  rw [map_sub, hxy, sub_self]
  rfl

end D05.M15.TensorPairing.ArbitraryInjective
