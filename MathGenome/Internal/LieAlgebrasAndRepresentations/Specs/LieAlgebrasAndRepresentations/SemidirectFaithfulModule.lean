import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.NilpotentFaithfulTruncation
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ReductiveDecomposition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! LA-I10, source lines 4473–4506. We prove the stronger characteristic-zero
field version; in particular this includes the stated complex case. Reductive
means radical equals center. No restriction on the derivation action is imposed.
The product uses the source order K × N and the existing semidirect bracket.
All zero-dimensional cases are included. -/
namespace Specs.LieAlgebrasAndRepresentations.SemidirectFaithfulModule
universe u v w t
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The compatible actions give exactly (a,x) ↦ D(θ a) + ρ(x). -/
def semidirectActionExpected : Prop :=
  ∀ (k : Type u) [Field k] (K : Type v) [LieRing K] [LieAlgebra k K]
    (N : Type w) [LieRing N] [LieAlgebra k N]
    (V : Type t) [AddCommGroup V] [Module k V]
    (θ : K →ₗ⁅k⁆ LieDerivation k N N)
    (ρ : N →ₗ⁅k⁆ Module.End k V)
    (D : LieDerivation k N N →ₗ⁅k⁆ Module.End k V),
    (∀ δ x, ⁅D δ, ρ x⁆ = ρ (δ x)) →
    letI := ActionsDerivationsSemidirect.semidirect_lie_ring_value θ
    letI := ActionsDerivationsSemidirect.semidirect_lie_algebra_value θ
    ∃ σ : (K × N) →ₗ⁅k⁆ Module.End k V,
      ∀ a x, σ (a, x) = D (θ a) + ρ x

/-- A faithful finite-dimensional module of the reductive factor. -/
def reductiveFaithfulExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (K : Type v) [LieRing K] [LieAlgebra k K] [FiniteDimensional k K],
    ReductiveDecomposition.IsReductive_value k K →
    ∃ (W : Type (max u v)) (_ : AddCommGroup W) (_ : Module k W),
      FiniteDimensional k W ∧
      ∃ τ : K →ₗ⁅k⁆ Module.End k W, Function.Injective τ

/-- Full faithful-module conclusion with arbitrary derivation action. -/
def faithfulExpected : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (K : Type v) [LieRing K] [LieAlgebra k K] [FiniteDimensional k K]
    (N : Type w) [LieRing N] [LieAlgebra k N] [FiniteDimensional k N]
    [LieRing.IsNilpotent N],
    ReductiveDecomposition.IsReductive_value k K →
    ∀ θ : K →ₗ⁅k⁆ LieDerivation k N N,
    letI := ActionsDerivationsSemidirect.semidirect_lie_ring_value θ
    letI := ActionsDerivationsSemidirect.semidirect_lie_algebra_value θ
    ∃ (V : Type (max u v w)) (_ : AddCommGroup V) (_ : Module k V),
      FiniteDimensional k V ∧
      ∃ σ : (K × N) →ₗ⁅k⁆ Module.End k V, Function.Injective σ

end Specs.LieAlgebrasAndRepresentations.SemidirectFaithfulModule
