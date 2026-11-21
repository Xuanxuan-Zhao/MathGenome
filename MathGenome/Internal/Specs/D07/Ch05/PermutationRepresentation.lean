import MathGenome.Internal.Specs.D07.Ch01.InjectiveKernel
import MathGenome.Internal.Specs.D07.Ch02.PermutationConvention
import MathGenome.Internal.Specs.D07.Ch05.ActionDefinition
import Mathlib.Algebra.Group.Action.End

/-!
Independent specification of `K07.05.permutation_representation`
(paper.tex:822–829). Both carriers are arbitrary, and the action carrier may
be empty. Multiplication of permutations applies the right factor first.
The constructions below are canonical data, not assumed inverse laws.
-/

namespace Specs.D07.Ch05.PermutationRepresentation

universe u v

def RepresentationConstructorType : Type (max (u + 1) (v + 1)) :=
  ∀ (G : Type u) (X : Type v) [Group G], MulAction G X → (G →* Equiv.Perm X)

/-- The permutation attached to `g` acts by the original action map. -/
def representationValue : RepresentationConstructorType.{u, v} :=
  fun G X _ a => @MulAction.toPermHom G X _ a

def ActionConstructorType : Type (max (u + 1) (v + 1)) :=
  ∀ (G : Type u) (X : Type v) [Group G], (G →* Equiv.Perm X) → MulAction G X

/-- Pull back the evaluation action of permutations along the homomorphism. -/
def actionValue : ActionConstructorType.{u, v} :=
  fun _ X _ ρ => MulAction.compHom X ρ

def RepresentationApply : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] (a : MulAction G X) (g : G) (x : X),
    representationValue G X a g x = a.smul g x

def ActionApply : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] (ρ : G →* Equiv.Perm X) (g : G) (x : X),
    (actionValue G X ρ).smul g x = ρ g x

def ActionRoundTrip : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] (a : MulAction G X),
    actionValue G X (representationValue G X a) = a

def RepresentationRoundTrip : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] (ρ : G →* Equiv.Perm X),
    representationValue G X (actionValue G X ρ) = ρ

/-- An equivalence with the two specified constructions as its maps. -/
def ActionsEquivHomomorphisms : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G],
    ∃ e : MulAction G X ≃ (G →* Equiv.Perm X),
      (∀ a : MulAction G X, e a = representationValue G X a) ∧
      (∀ ρ : G →* Equiv.Perm X, e.symm ρ = actionValue G X ρ)

def KernelIffFixes : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [a : MulAction G X] (g : G),
    g ∈ (representationValue G X a).ker ↔ ∀ x : X, g • x = x

def FaithfulIffInjective : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [a : MulAction G X],
    ActionDefinition.faithfulValue G X ↔
      Function.Injective (representationValue G X a)

def EmptyRepresentationTrivial : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [a : MulAction G X],
    IsEmpty X → representationValue G X a = 1

/-- A group is trivial precisely when its carrier is a subsingleton, since
the identity always supplies an element. -/
def EmptyFaithfulIffTrivial : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X],
    IsEmpty X → (ActionDefinition.faithfulValue G X ↔ Subsingleton G)

end Specs.D07.Ch05.PermutationRepresentation
