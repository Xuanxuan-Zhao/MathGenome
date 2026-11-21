import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.TychonoffCube
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions

/-!
The evaluation-closure construction in paper.tex, d10:11:stone-cech.
The cube, index of all continuous interval-valued maps, and evaluation
are exactly the shared Chapter 10 objects. The definitions make sense
for every space; the embedding assertion requires precisely Tychonoffness.
No theorem about this construction is assumed by these independent Specs.
-/

open Set Topology
universe u v

namespace Specs.D10Topology.Ch11.StoneCechConstruction

/-- The actual closed subset of the evaluation cube used in the source. -/
def betaSet (X : Type u) [TopologicalSpace X] :
    Set (Ch10.TychonoffCube.Cube (Ch10.TychonoffCube.EvaluationIndex X)) :=
  closure (range (Ch10.TychonoffCube.evaluationMap (X := X)))

/-- The subspace topology of the evaluation cube is inherited automatically. -/
abbrev Beta (X : Type u) [TopologicalSpace X] : Type u := betaSet X

/-- Evaluation with its codomain restricted to the closure of its range. -/
def betaUnit {X : Type u} [TopologicalSpace X] : X → Beta X :=
  fun x => ⟨Ch10.TychonoffCube.evaluationMap x, subset_closure (mem_range_self x)⟩

def betaSetType : Type (u + 1) := (X : Type u) → [TopologicalSpace X] →
  Set (Ch10.TychonoffCube.Cube (Ch10.TychonoffCube.EvaluationIndex X))
def betaSetValue : betaSetType := betaSet

def betaType : Type (u + 1) := (X : Type u) → [TopologicalSpace X] → Type u
def betaValue : betaType := Beta

def betaUnitType : Type (u + 1) := {X : Type u} → [TopologicalSpace X] → X → Beta X
def betaUnitValue : betaUnitType := @betaUnit

def betaUnit_val : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X),
    (betaUnit x).val = Ch10.TychonoffCube.evaluationMap x

def betaUnit_coordinate : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X)
    (f : Ch10.TychonoffCube.EvaluationIndex X), (betaUnit x).val f = f x

def betaSet_closed : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], IsClosed (betaSet X)

def beta_compact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], CompactSpace (Beta X)

def beta_hausdorff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], T2Space (Beta X)

def betaUnit_continuous : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], Continuous (betaUnit (X := X))

def betaUnit_embedding : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], Ch07.SeparationConventions.tychonoffValue X →
    IsEmbedding (betaUnit (X := X))

def betaUnit_dense : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], DenseRange (betaUnit (X := X))

def beta_hausdorffCompactification : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], Ch07.SeparationConventions.tychonoffValue X →
    LocalCompactConventions.HausdorffCompactification (betaUnit (X := X))

/-- The converse also permits a compactification in a different universe. -/
def tychonoff_of_hausdorffCompactification : Prop :=
  ∀ {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K] (i : X → K),
    LocalCompactConventions.HausdorffCompactification i →
      Ch07.SeparationConventions.tychonoffValue X

/-- A compactification in the universe of X already suffices. -/
def has_hausdorffCompactification_iff_tychonoff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    (∃ (K : Type u) (_ : TopologicalSpace K) (i : X → K),
      LocalCompactConventions.HausdorffCompactification i) ↔
    Ch07.SeparationConventions.tychonoffValue X

def empty_betaSet : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X], betaSet X = ∅

def empty_beta : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X], IsEmpty (Beta X)

end Specs.D10Topology.Ch11.StoneCechConstruction
