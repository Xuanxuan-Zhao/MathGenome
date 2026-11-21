import MathGenome.Internal.Specs.D07.Ch01.HomomorphismDefinition
import Mathlib.Algebra.Group.Equiv.Defs

/-!
Independent specification of `K07.01.isomorphism_definition`
(paper.tex:323–334, chapters/M07.01.tex:108–119).

The carriers and their group structures are arbitrary, including trivial groups.
`MulEquiv` records an operation-preserving equivalence, and the bridge below
identifies it with the source's bijective group homomorphism. The inverse is
required to be a homomorphism, with both inverse equations on all elements.
-/

namespace Specs.D07.Ch01.IsomorphismDefinition

universe u v w

def GroupIsoType : Type (max u v + 1) :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H], Type (max u v)

def groupIsoValue : GroupIsoType.{u, v} := fun G H _ _ => G ≃* H

def IsomorphismPredicateType : Type (max u v + 1) :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H], (G →* H) → Prop

/-- The source definition applies to a specified homomorphism. -/
def isomorphismPredicateValue : IsomorphismPredicateType.{u, v} :=
  fun _ _ _ _ f => Function.Bijective f

def IsomorphicPredicateType : Type (max u v + 1) :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H], Prop

/-- The assertion denoted by `G ≅ H`: existence of a group isomorphism. -/
def isomorphicPredicateValue : IsomorphicPredicateType.{u, v} :=
  fun G H _ _ => Nonempty (G ≃* H)

/-- Bundling preserves the specified forward homomorphism, not just its
source and target or their cardinalities. -/
def IsomorphismIffBundled : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    Function.Bijective f ↔ ∃ e : G ≃* H, e.toMonoidHom = f

/-- A given homomorphism is bijective precisely when it has a homomorphic
two-sided inverse. No inverse or bijectivity assumption is built into `f`. -/
def IsomorphismIffHomomorphicInverse : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    Function.Bijective f ↔
      ∃ g : H →* G, (∀ x : G, g (f x) = x) ∧ (∀ y : H, f (g y) = y)

def IsomorphicIffBijectiveHom : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H],
    isomorphicPredicateValue G H ↔ ∃ f : G →* H, Function.Bijective f

/-- Reflexivity on every group, including the one-element group. -/
def IsomorphicRefl : Prop :=
  ∀ (G : Type u) [Group G], isomorphicPredicateValue G G

def IsomorphicSymm : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H],
    isomorphicPredicateValue G H → isomorphicPredicateValue H G

def IsomorphicTrans : Prop :=
  ∀ (G : Type u) (H : Type v) (K : Type w) [Group G] [Group H] [Group K],
    isomorphicPredicateValue G H → isomorphicPredicateValue H K →
      isomorphicPredicateValue G K

end Specs.D07.Ch01.IsomorphismDefinition
