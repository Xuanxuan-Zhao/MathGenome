import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.PositiveFunctionals
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The cyclic part of `fa2:p2:gns` (paper.tex 12321–12354).
States are the shared algebraic positive functionals, without an assumed continuity
hypothesis. A cyclic orbit is already a linear subspace, so dense range of the
orbit is equivalent to the usual dense linear span condition. The quotient is
the actual shared A/N. Its embedding supplies its positive definite form and
norm and identifies H as its Hilbert completion. Unitaries are complex-linear
isometric equivalences; arbitrary Hilbert-space universes are allowed in uniqueness.
The all-states faithful sum is a separately allocated obligation. -/
noncomputable section
namespace ExpandedFA.CStar.CyclicGNS.Spec
universe u v w
open scoped InnerProductSpace

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A cyclic realization of the original state. -/
structure Realization (φ : Conventions.Spec.StateValue A) where
  π : A →⋆ₐ[ℂ] (H →L[ℂ] H)
  ξ : H
  unit_vector : ‖ξ‖ = 1
  cyclic : DenseRange (fun a => π a ξ)
  coefficient : ∀ a, φ.val a = ⟪ξ, π a ξ⟫_ℂ

/-- The canonical quotient-to-completion bridge and the left multiplication action. -/
structure Construction (φ : Conventions.Spec.StateValue A) extends Realization (H := H) φ where
  j : PositiveFunctionals.Spec.NullQuotient φ.val →ₗ[ℂ] H
  injective : Function.Injective j
  dense : DenseRange j
  inner_classes : ∀ a b, ⟪j (Submodule.Quotient.mk a), j (Submodule.Quotient.mk b)⟫_ℂ =
    φ.val (star a * b)
  vector_class : ξ = j (Submodule.Quotient.mk 1)
  left_action : ∀ c a, π c (j (Submodule.Quotient.mk a)) =
    j (Submodule.Quotient.mk (c * a))
  norm_bound : ∀ a, ‖π a‖ ≤ ‖a‖

def Existence : Prop := ∀ (A : Type u) [CStarAlgebra A]
  (φ : Conventions.Spec.StateValue A),
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H), Nonempty (Construction (H := H) φ)

/-- Exactly one surjective unitary intertwines any two cyclic realizations and
carries their distinguished vectors to each other. No quotient presentation or
extra norm bound is assumed for these arbitrary realizations. -/
def Uniqueness : Prop := ∀ (A : Type u) [CStarAlgebra A]
  (φ : Conventions.Spec.StateValue A)
  (H : Type v) (K : Type w)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (r : Realization (H := H) φ) (s : Realization (H := K) φ),
  ∃! U : H ≃ₗᵢ[ℂ] K,
    U r.ξ = s.ξ ∧ ∀ a x, U (r.π a x) = s.π a (U x)

end ExpandedFA.CStar.CyclicGNS.Spec
