import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CoveringClassification
import Mathlib.Topology.Covering.Deck
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Independent statements for `thm:p202-deck-group`, paper.tex 435–468.
The deck group consists of all homeomorphisms over the given projection.
Its multiplication is ordinary function composition. The fundamental group
retains the upstream first-path-first convention. -/
namespace P202Specs.Topology
universe u v
noncomputable section

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

abbrev DeckGroup (p : E → B) := deck p

/-- The restriction of a deck transformation to the whole fiber. -/
def deckFiber (p : E → B) (b : B) (F : DeckGroup p) (e : Fiber p b) : Fiber p b :=
  ⟨F.val e.val, (congrFun F.property e.val).trans e.property⟩

/-- The actual quotient N_G(H)/H, where H is viewed as a subgroup of N_G(H). -/
abbrev NormalizerQuotient {G : Type*} [Group G] (H : Subgroup G) :=
  Subgroup.normalizer H ⧸ H.subgroupOf (Subgroup.normalizer H)

namespace DeckExpected

/-- In particular every deck transformation is determined by its value at the
chosen point. Connectedness suffices for uniqueness of existing lifts. -/
def determined : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace E] (p : C(E, B)), Covering p → ∀ e : E,
      Function.Injective (fun F : DeckGroup p => F.val e)

/-- The action on each fiber is free. -/
def free : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace E] (p : C(E, B)), Covering p →
    ∀ (b : B) (e : Fiber p b) (F : DeckGroup p), deckFiber p b F e = e → F = 1

/-- Deck transformations commute with endpoint transport. -/
def commutes : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)), Covering p → ∀ (b : B) (F : DeckGroup p)
    (e : Fiber p b) (g : Pi1 B b),
      deckFiber p b F (fiberAction p b e g) = fiberAction p b (deckFiber p b F e) g

/-- The isomorphism includes its endpoint formula. Consequently the class of
n*m acts as F_n ∘ F_m, fixing the multiplication convention explicitly. -/
def deckGroup : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace E] [PathConnectedSpace B] [LocallyPathConnectedSpace B],
    SemilocallySimplyConnected B → ∀ (p : C(E, B)), Covering p →
    ∀ (b : B) (e : Fiber p b),
    ∃ Φ : NormalizerQuotient (fiberSubgroup p b e) ≃* DeckGroup p,
      ∀ n : (Subgroup.normalizer (fiberSubgroup p b e)),
        deckFiber p b (Φ (QuotientGroup.mk n)) e = fiberAction p b e n.val

/-- Transitivity means transitivity on the whole fiber, with no finiteness
assumption. This is the source's definition of a regular covering. -/
def regularity : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace E] [PathConnectedSpace B] [LocallyPathConnectedSpace B],
    SemilocallySimplyConnected B → ∀ (p : C(E, B)), Covering p →
    ∀ (b : B) (e : Fiber p b),
      (∀ x y : Fiber p b, ∃ F : DeckGroup p, deckFiber p b F x = y) ↔
        (fiberSubgroup p b e).Normal

end DeckExpected
end
end P202Specs.Topology
