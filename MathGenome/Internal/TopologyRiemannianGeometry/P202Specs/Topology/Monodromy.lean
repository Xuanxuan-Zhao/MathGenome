import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CoveringCriterion
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.SetTheory.Cardinal.Basic

/-! Corollary `cor:p202-cover-action`, paper.tex 342–362.
The entire fiber is used. `Pi1` has the paper's first-path-first product.
Right cosets are `H g`, and cardinal equalities retain infinite sheet numbers.
The fallback in `fiberAction` merely makes it a total definition for arbitrary
maps; every statement below assumes the paper's surjective covering condition. -/
namespace P202Specs.Topology
open scoped unitInterval
universe u v
noncomputable section

abbrev Fiber {E : Type u} {B : Type v} (p : E → B) (b : B) := p ⁻¹' {b}

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Endpoint transport on loop classes, in the right-action argument order. -/
def fiberAction (p : E → B) (b : B) (e : Fiber p b) (g : Pi1 B b) : Fiber p b := by
  classical
  exact if hc : IsCoveringMap p then hc.monodromy (pathClass g) e else e

/-- The subgroup at the specified point of the fiber. -/
def fiberSubgroup (p : C(E, B)) (b : B) (e : Fiber p b) : Subgroup (Pi1 B b) :=
  (PointedMap.induced (⟨p, e.property⟩ : PointedMap E B e.val b)).range

abbrev RightCosets {G : Type*} [Group G] (H : Subgroup G) :=
  Quotient (QuotientGroup.rightRel H)

def rightCoset {G : Type*} [Group G] (H : Subgroup G) (g : G) : RightCosets H :=
  Quotient.mk _ g

/-- The usual right action `H a ↦ H (a g)` on right cosets. -/
def cosetAction {G : Type*} [Group G] (H : Subgroup G) (q : RightCosets H) (g : G) :
    RightCosets H :=
  Quotient.map (fun a => a * g) (by
    intro a b hab
    apply QuotientGroup.rightRel_apply.mpr
    have h := QuotientGroup.rightRel_apply.mp hab
    simpa [mul_inv_rev, mul_assoc] using h) q

namespace MonodromyExpected

def actionLaws : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), Covering p → ∀ b,
    (∀ e, fiberAction p b e 1 = e) ∧
    ∀ e g h, fiberAction p b e (g * h) = fiberAction p b (fiberAction p b e g) h

/-- This formula includes independence from both representative and chosen lift. -/
def endpointFormula : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), Covering p → ∀ b (e : Fiber p b) (a : SourcePath b b)
    (L : C(unitInterval, E)), (∀ t, p (L t) = a t) → L 0 = e.val →
    (fiberAction p b e (loopClass a)).val = L 1

def transitive : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace B]
    (p : E → B), Covering p → ∀ b (e f : Fiber p b),
    ∃ g : Pi1 B b, fiberAction p b e g = f

def stabilizer : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)), Covering p → ∀ b (e : Fiber p b) (g : Pi1 B b),
    fiberAction p b e g = e ↔ g ∈ fiberSubgroup p b e

def cosetEquivalence : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace B]
    (p : C(E, B)), Covering p → ∀ b (e : Fiber p b),
    ∃ F : RightCosets (fiberSubgroup p b e) ≃ Fiber p b,
      (∀ g, F (rightCoset (fiberSubgroup p b e) g) = fiberAction p b e g) ∧
      ∀ q g, F (cosetAction (fiberSubgroup p b e) q g) = fiberAction p b (F q) g

/-- No connectedness is needed if a path between the basepoints is supplied. -/
def fiberTransport : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), Covering p → ∀ x y (d : SourcePath x y),
    ∃ T : Fiber p x ≃ Fiber p y,
      (∀ (e : Fiber p x) (L : C(unitInterval, E)),
        (∀ t, p (L t) = d t) → L 0 = e.val → (T e).val = L 1) ∧
      (∀ (e : Fiber p y) (L : C(unitInterval, E)),
        (∀ t, p (L t) = d.symm t) → L 0 = e.val → (T.symm e).val = L 1)

/-- Cardinal index, without replacing infinite cardinalities by zero. -/
def fiberIndex : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace B]
    (p : C(E, B)), Covering p → ∀ b (e : Fiber p b),
    Cardinal.lift.{v} (Cardinal.mk (Fiber p b)) =
      Cardinal.lift.{u} (Cardinal.mk (Pi1 B b ⧸ fiberSubgroup p b e))

/-- Every disjoint sheet decomposition has one sheet per point of the fiber. -/
def sheetCardinality : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (U : Set B) (b : B), b ∈ U →
    ∀ S : Set (CoveringSheet p U),
      S.Pairwise (fun s t => Disjoint s.chart.source t.chart.source) →
      (⋃ s ∈ S, s.chart.source) = p ⁻¹' U →
      Cardinal.mk S = Cardinal.lift.{v} (Cardinal.mk (Fiber p b))

/-- The sheet number at every base neighborhood is the index of the subgroup
at the originally specified fiber point, even for infinite coverings. -/
def sheetIndex : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace B]
    (p : C(E, B)), Covering p → ∀ b (e : Fiber p b)
    (U : Set B) (c : B), c ∈ U → ∀ S : Set (CoveringSheet p U),
      S.Pairwise (fun s t => Disjoint s.chart.source t.chart.source) →
      (⋃ s ∈ S, s.chart.source) = p ⁻¹' U →
      Cardinal.mk S = Cardinal.lift.{u} (Cardinal.mk (Pi1 B b ⧸ fiberSubgroup p b e))

end MonodromyExpected
end
end P202Specs.Topology
