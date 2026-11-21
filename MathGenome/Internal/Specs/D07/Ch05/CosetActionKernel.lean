import MathGenome.Internal.Specs.D07.Ch03.CosetsPartition
import MathGenome.Internal.Specs.D07.Ch05.OrbitStabilizerEquivalence
import MathGenome.Internal.Specs.D07.Ch05.PermutationRepresentation
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
Independent specification of `K07.05.coset_action_kernel`, paper.tex:862–877.
The quotient is the set of left cosets for an arbitrary subgroup. No
normality, finiteness, or faithfulness assumption is imposed. Transitivity
has the source's nonemptiness convention. The intersection below spells out
the conjugate sets, including the direction of conjugation.
-/

namespace Specs.D07.Ch05.CosetActionKernel

universe u v

def CosetEquality : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (x y : G),
    (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk y ↔
      Ch03.CosetsPartition.leftCoset H x = Ch03.CosetsPartition.leftCoset H y

def CosetActionApply : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (g x : G),
    g • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk (g * x)

def CosetActionTransitive : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    ActionDefinition.transitiveValue G (G ⧸ H)

def CosetStabilizer : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) = H

def CosetKernel : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    (PermutationRepresentation.representationValue G (G ⧸ H) inferInstance).ker =
      H.normalCore

def CoreIntersection : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    (H.normalCore : Set G) =
      ⋂ x : G, (fun h : G => x * h * x⁻¹) '' (H : Set G)

def CoreLargestNormal : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G),
    H.normalCore.Normal ∧ H.normalCore ≤ H ∧
      ∀ N : Subgroup G, N.Normal → N ≤ H → N ≤ H.normalCore

/-- The representative formula fixes the bijection to be the orbit map;
equivariance is explicitly required on every quotient point. -/
def TransitiveCosetEquivalence : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X],
    ActionDefinition.transitiveValue G X →
      ∃ a : X, ∃ e : (G ⧸ OrbitStabilizerDefinitions.stabilizerValue G X a) ≃ X,
        (∀ g : G, e (QuotientGroup.mk g) = g • a) ∧
        (∀ (g : G) (q : G ⧸ OrbitStabilizerDefinitions.stabilizerValue G X a),
          e (g • q) = g • e q)

end Specs.D07.Ch05.CosetActionKernel
