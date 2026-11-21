import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Algebra.Lie.TransferInstance

/-!
LA-A03, source notes/005/lie-algebras-and-representations.tex, lines 259–301.
The field is arbitrary (section convention, lines 168–171). No dimension or
characteristic restriction is imposed. The product below has the source's
order G × N, transported from Mathlib's N ⋊ G along a linear equivalence.
The abelian bracket is defined for every linear action, before imposing the
representation identity; thus the converse Jacobi assertion is nonvacuous.
-/

universe u v w

namespace Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k]
variable {G : Type v} [LieRing G] [LieAlgebra k G]
variable {N : Type w} [LieRing N] [LieAlgebra k N]
variable {M : Type w} [AddCommGroup M] [Module k M]

/-- The representation identity, with composition as multiplication in End. -/
def IsRepresentation (ρ : G →ₗ[k] Module.End k M) : Prop :=
  ∀ x y, ρ ⁅x, y⁆ = ρ x * ρ y - ρ y * ρ x

/-- The bracket of formula (1.1) when the second summand is abelian. -/
def abelianBracket (ρ : G →ₗ[k] Module.End k M) (p q : G × M) : G × M :=
  (⁅p.1, q.1⁆, ρ p.1 q.2 - ρ q.1 p.2)

/-- Coordinates in the order used in the source, preserving the given module. -/
def semidirectCoordinates (θ : G →ₗ⁅k⁆ LieDerivation k N N) :
    (G × N) ≃ₗ[k] (N ⋊⁅θ⁆ G) :=
  (LinearEquiv.prodComm k G N).trans (LieAlgebra.SemiDirectSum.toProdl θ).symm

def semidirect_lie_ring_value (θ : G →ₗ⁅k⁆ LieDerivation k N N) : LieRing (G × N) :=
  (semidirectCoordinates θ).toAddEquiv.lieRing

def semidirect_lie_algebra_value (θ : G →ₗ⁅k⁆ LieDerivation k N N) :
    letI := semidirect_lie_ring_value θ
    LieAlgebra k (G × N) :=
  (semidirectCoordinates θ).lieAlgebra

def representation_iff_type :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {M : Type w} [AddCommGroup M] [Module k M] (ρ : G →ₗ[k] Module.End k M),
  (∃ f : G →ₗ⁅k⁆ Module.End k M, f.toLinearMap = ρ) ↔ IsRepresentation ρ

def representation_action_type :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {M : Type w} [AddCommGroup M] [Module k M]
    (ρ : G →ₗ⁅k⁆ Module.End k M) (x y : G) (a : M),
  ρ ⁅x, y⁆ a = ρ x (ρ y a) - ρ y (ρ x a)

def derivations_subalgebra_type :=
  ∀ (k : Type u) [Field k] (N : Type w) [LieRing N] [LieAlgebra k N],
    LieSubalgebra k (Module.End k N)

def derivations_subalgebra_value (k : Type u) [Field k]
    (N : Type w) [LieRing N] [LieAlgebra k N] : LieSubalgebra k (Module.End k N) :=
  (LieDerivation.toLinearMapLieHom k N).range

def derivation_membership_type :=
  ∀ {k : Type u} [Field k] {N : Type w} [LieRing N] [LieAlgebra k N]
    (d : Module.End k N),
  d ∈ derivations_subalgebra_value k N ↔
    ∀ a b, d ⁅a, b⁆ = ⁅d a, b⁆ + ⁅a, d b⁆

def derivation_commutator_type :=
  ∀ {k : Type u} [Field k] {N : Type w} [LieRing N] [LieAlgebra k N]
    (d e : LieDerivation k N N) (a : N),
  ⁅d, e⁆ a = d (e a) - e (d a)

def adjoint_type :=
  ∀ (k : Type u) [Field k] (G : Type v) [LieRing G] [LieAlgebra k G],
    G →ₗ⁅k⁆ LieDerivation k G G

def adjoint_value (k : Type u) [Field k]
    (G : Type v) [LieRing G] [LieAlgebra k G] : G →ₗ⁅k⁆ LieDerivation k G G :=
  LieDerivation.ad k G

def adjoint_apply_type :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G] (x y : G),
  adjoint_value k G x y = ⁅x, y⁆

def adjoint_kernel_type :=
  ∀ (k : Type u) [Field k] (G : Type v) [LieRing G] [LieAlgebra k G],
  (adjoint_value k G).ker = LieAlgebra.center k G

/-- The same kernel assertion for the representation with values in gl(G). -/
def adjoint_endomorphism_kernel_type :=
  ∀ (k : Type u) [Field k] (G : Type v) [LieRing G] [LieAlgebra k G],
  ((LieDerivation.toLinearMapLieHom k G).comp (adjoint_value k G)).ker =
    LieAlgebra.center k G

def adjoint_representation_type :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G],
  IsRepresentation ((LieDerivation.toLinearMapLieHom k G).comp
    (adjoint_value k G)).toLinearMap

def semidirect_lie_ring_type :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {N : Type w} [LieRing N] [LieAlgebra k N]
    (θ : G →ₗ⁅k⁆ LieDerivation k N N), LieRing (G × N)

def semidirect_lie_algebra_type :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {N : Type w} [LieRing N] [LieAlgebra k N]
    (θ : G →ₗ⁅k⁆ LieDerivation k N N),
  letI := semidirect_lie_ring_value θ
  LieAlgebra k (G × N)

def semidirect_bracket_type :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {N : Type w} [LieRing N] [LieAlgebra k N]
    (θ : G →ₗ⁅k⁆ LieDerivation k N N) (x y : G) (a b : N),
  letI := semidirect_lie_ring_value θ
  ⁅(x, a), (y, b)⁆ = (⁅x, y⁆, θ x b - θ y a + ⁅a, b⁆)

def abelian_jacobi_iff_representation_type :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {M : Type w} [AddCommGroup M] [Module k M] (ρ : G →ₗ[k] Module.End k M),
  (∀ p q r : G × M,
    abelianBracket ρ p (abelianBracket ρ q r) +
      abelianBracket ρ q (abelianBracket ρ r p) +
      abelianBracket ρ r (abelianBracket ρ p q) = 0) ↔ IsRepresentation ρ

end Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
