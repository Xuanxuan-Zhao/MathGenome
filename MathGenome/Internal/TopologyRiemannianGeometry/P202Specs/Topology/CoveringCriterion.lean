import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CoveringLifting

/-! Independent statements for paper.tex, Theorem `thm:p202-cover-criterion`
and the closed-loop characterization in its proof (lines 306–340).
The groups and induced maps use the paper's first-path-first product through
the canonical opposite convention in `FundamentalGroupoid`.
Coverings are surjective and all spaces carry their given topologies. -/
namespace P202Specs.Topology.CriterionExpected

open scoped unitInterval
universe u v w

/-- Injectivity requires no connectedness or local connectedness hypothesis. -/
def coveringInducedInjective : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (e : E) (b : B) (p : PointedMap E B e b),
    Covering p.map → Function.Injective p.induced

/-- Every continuous lift starting at e is closed exactly when the based loop
class belongs to the image subgroup. Existence of the lift is supplied by
the upstream path-lifting theorem. No connectedness hypothesis is imposed. -/
def closedLiftCriterion : Prop :=
  ∀ (E : Type u) (B : Type v) [TopologicalSpace E] [TopologicalSpace B]
    (e : E) (b : B) (p : PointedMap E B e b), Covering p.map →
    ∀ (a : SourcePath b b) (L : C(unitInterval, E)),
      (∀ t, p.map (L t) = a t) → L 0 = e →
      (L 1 = e ↔ loopClass a ∈ p.induced.range)

/-- A based lift exists uniquely iff the image subgroup condition holds.
There are no hypotheses on connectedness of E or B. -/
def coveringLiftCriterion : Prop :=
  ∀ (E : Type u) (B : Type v) (Y : Type w)
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Y]
    [PathConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (e : E) (b : B) (y : Y) (p : PointedMap E B e b), Covering p.map →
    ∀ f : PointedMap Y B y b,
      (∃! L : C(Y, E), (∀ z, p.map (L z) = f.map z) ∧ L y = e) ↔
        f.induced.range ≤ p.induced.range

/-- Uniqueness of an existing based lift, independently of the image condition.
Preconnectedness already suffices for this part of the theorem. -/
def coveringLiftUnique : Prop :=
  ∀ (E : Type u) (B : Type v) (Y : Type w)
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Y]
    [PreconnectedSpace Y]
    (e : E) (b : B) (y : Y) (p : PointedMap E B e b), Covering p.map →
    ∀ (f : PointedMap Y B y b) (L M : C(Y, E)),
      ((∀ z, p.map (L z) = f.map z) ∧ L y = e) →
      ((∀ z, p.map (M z) = f.map z) ∧ M y = e) → L = M

/-- The ordinary existence formulation of the image subgroup criterion. -/
def coveringLiftExists : Prop :=
  ∀ (E : Type u) (B : Type v) (Y : Type w)
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Y]
    [PathConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (e : E) (b : B) (y : Y) (p : PointedMap E B e b), Covering p.map →
    ∀ f : PointedMap Y B y b,
      (∃ L : C(Y, E), (∀ z, p.map (L z) = f.map z) ∧ L y = e) ↔
        f.induced.range ≤ p.induced.range

end P202Specs.Topology.CriterionExpected
