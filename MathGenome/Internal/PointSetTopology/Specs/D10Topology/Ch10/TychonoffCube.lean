import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import Mathlib.Topology.ContinuousMap.Basic

/-!
Independent statements for paper.tex `d10:10:tychonoff-cube` and
`d10:11:evaluation-embedding`. Cubes carry the product topology of the
usual closed real unit interval. The index contains all continuous maps,
and evaluation is defined for every X, with no nonemptiness assumption.
The separation predicate is the paper's completely regular plus Hausdorff
predicate, with separating functions equal to 1 at the point and 0 on F.
-/

open Set Topology
universe u v

namespace Specs.D10Topology.Ch10.TychonoffCube

abbrev Cube (ι : Type u) := ι → unitInterval
abbrev EvaluationIndex (X : Type u) [TopologicalSpace X] := ContinuousMap X unitInterval

def evaluationMap {X : Type u} [TopologicalSpace X] : X → Cube (EvaluationIndex X) :=
  fun x f => f x

def cubeType : Type (u + 1) := Type u → Type u
def cubeValue : cubeType := Cube

def evaluationIndexType : Type (u + 1) :=
  (X : Type u) → [TopologicalSpace X] → Type u
def evaluationIndexValue : evaluationIndexType := EvaluationIndex

def evaluationMapType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → X → Cube (EvaluationIndex X)
def evaluationMapValue : evaluationMapType := @evaluationMap

def evaluation_continuous : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], Continuous (evaluationMap (X := X))

def tychonoff_evaluation_embedding : Prop :=
  ∀ {X : Type u} [TopologicalSpace X],
    Ch07.SeparationConventions.tychonoffValue X → IsEmbedding (evaluationMap (X := X))

def cube_tychonoff : Prop :=
  ∀ (ι : Type u), Ch07.SeparationConventions.tychonoffValue (Cube ι)

/-- The converse permits an arbitrary universe for the index type. -/
def tychonoff_of_cube_embedding : Prop :=
  ∀ {X : Type u} {ι : Type v} [TopologicalSpace X] (e : X → Cube ι),
    IsEmbedding e → Ch07.SeparationConventions.tychonoffValue X

/-- An index in the universe of X suffices, since C(X,[0,1]) lies there. -/
def tychonoff_iff_cube_embedding : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    Ch07.SeparationConventions.tychonoffValue X ↔
      ∃ (ι : Type u) (e : X → Cube ι), IsEmbedding e

def empty_evaluation_embedding : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X],
    IsEmbedding (evaluationMap (X := X))

def compact_hausdorff_tychonoff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X],
    Ch05.Compactness.CoverCompact X → Ch07.SeparationConventions.tychonoffValue X

/-- In fact compactness of the evaluation image does not require separation. -/
def compact_evaluation_image : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], Ch05.Compactness.CoverCompact X →
    Ch05.Compactness.SubspaceCompact (range (evaluationMap (X := X)))

/-- The cube is Hausdorff; the compact evaluation image is therefore closed. -/
def compact_hausdorff_evaluation_image : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X],
    Ch05.Compactness.CoverCompact X →
      IsEmbedding (evaluationMap (X := X)) ∧
      Ch05.Compactness.SubspaceCompact (range (evaluationMap (X := X))) ∧
      IsClosed (range (evaluationMap (X := X)))

end Specs.D10Topology.Ch10.TychonoffCube
