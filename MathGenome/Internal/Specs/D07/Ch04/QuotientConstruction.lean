import MathGenome.Internal.Specs.D07.Ch04.NormalityEquivalences
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
Independent specification of `K07.04.quotient_construction`, paper.tex:670–680.

The quotient and its operations are the canonical left-coset quotient already
used by the shared normal-quotient interface. Equality is explicitly identified
with equality of the source's set-valued cosets. The multiplication independence
criterion is stated for arbitrary subgroups, without assuming normality in its
forward direction. The extreme cases retain the representative formula for the
isomorphism and assert that every element of the top quotient is its identity.
-/

namespace Specs.D07.Ch04.QuotientConstruction

open Specs.D07.Ch03.CosetsPartition

universe u

def QuotientEqIffCosetEq : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal] (g h : G),
    QuotientGroup.mk' N g = QuotientGroup.mk' N h ↔ leftCoset N g = leftCoset N h

def QuotientGroupLaws : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal],
    Specs.D07.Ch01.GroupDefinition.groupAxiomsValue (G ⧸ N) (· * ·) 1 Inv.inv

def QuotientOperations : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal],
    (∀ g h : G, QuotientGroup.mk' N g * QuotientGroup.mk' N h =
      QuotientGroup.mk' N (g * h)) ∧
    QuotientGroup.mk' N 1 = 1 ∧
    (∀ g : G, (QuotientGroup.mk' N g)⁻¹ = QuotientGroup.mk' N g⁻¹)

/-- The representative `1` denotes precisely the subgroup coset. -/
def IdentityCoset : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G), leftCoset N 1 = (N : Set G)

def ProjectionSurjective : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal],
    Function.Surjective (QuotientGroup.mk' N)

def ProjectionKernel : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal],
    (QuotientGroup.mk' N).ker = N

/-- This is exactly independence of both representatives in the rule
`(gN)(hN) = (gh)N`. No quotient group operations are used in this criterion. -/
def ProductIndependentIffNormal : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G),
    (∀ g g' h h' : G,
      leftCoset N g = leftCoset N g' → leftCoset N h = leftCoset N h' →
        leftCoset N (g * h) = leftCoset N (g' * h')) ↔ N.Normal

def QuotientBottom : Prop :=
  ∀ (G : Type u) [Group G],
    ∃ e : G ⧸ (⊥ : Subgroup G) ≃* G,
      ∀ g : G, e (QuotientGroup.mk' (⊥ : Subgroup G) g) = g

def QuotientTopTrivial : Prop :=
  ∀ (G : Type u) [Group G] (q : G ⧸ (⊤ : Subgroup G)), q = 1

end Specs.D07.Ch04.QuotientConstruction
