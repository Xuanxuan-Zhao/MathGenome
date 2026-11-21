import MathGenome.Internal.Specs.D07.Ch01.KernelImage
import MathGenome.Internal.Specs.D07.Ch03.CosetsPartition
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
Independent specification of `support.group_normal_quotient`,
paper.tex:390–399 (Lemma `normal-quotient-preliminary`).

The canonical quotient `G ⧸ N` uses the left-coset relation. Its fibers
and equality criterion below identify it with the source's set-valued
left cosets, using the existing shared definition. Group operations are
specified on the same quotient, with all five source group axioms.
The projection is the bundled homomorphism `QuotientGroup.mk' N`.
Descent includes both directions and uniqueness among homomorphisms.
No finiteness, commutativity or nontriviality assumptions are imposed.
-/

namespace Specs.D07.Ch01.GroupNormalQuotient

open Specs.D07.Ch03.CosetsPartition

universe u v

def ProjectionFiber : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal] (g : G),
    {x : G | QuotientGroup.mk' N x = QuotientGroup.mk' N g} = leftCoset N g

def QuotientEqIffCosetEq : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal] (g h : G),
    QuotientGroup.mk' N g = QuotientGroup.mk' N h ↔ leftCoset N g = leftCoset N h

def QuotientGroupLaws : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal],
    GroupDefinition.groupAxiomsValue (G ⧸ N) (· * ·) 1 Inv.inv

def QuotientOperations : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal],
    (∀ g h : G, QuotientGroup.mk' N g * QuotientGroup.mk' N h =
      QuotientGroup.mk' N (g * h)) ∧
    QuotientGroup.mk' N 1 = 1 ∧
    (∀ g : G, (QuotientGroup.mk' N g)⁻¹ = QuotientGroup.mk' N g⁻¹)

def ProductIndependent : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal] (g g' h h' : G),
    leftCoset N g = leftCoset N g' → leftCoset N h = leftCoset N h' →
      leftCoset N (g * h) = leftCoset N (g' * h')

def ProjectionSurjective : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal],
    Function.Surjective (QuotientGroup.mk' N)

def ProjectionKernel : Prop :=
  ∀ (G : Type u) [Group G] (N : Subgroup G) [N.Normal],
    (QuotientGroup.mk' N).ker = N

def DescendsUniqueIff : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H]
    (N : Subgroup G) [N.Normal] (f : G →* H),
    (∃! fbar : G ⧸ N →* H, fbar.comp (QuotientGroup.mk' N) = f) ↔ N ≤ f.ker

end Specs.D07.Ch01.GroupNormalQuotient
