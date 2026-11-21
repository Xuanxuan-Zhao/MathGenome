import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.StoneCechConstruction
import Mathlib.Topology.Instances.Real.Lemmas

/-!
The full consequences in paper.tex, d10:11:beta-consequences.
The boundedness hypothesis is an absolute-value bound on all values of f.
Beta and betaUnit are the shared evaluation-closure construction.
The canonical map on continuous maps is coordinate reindexing, restricted
from the cube to the closure; its definition assumes no extension theorem.
-/

open Set Topology
universe u v w

namespace Specs.D10Topology.Ch11.StoneCechConsequences

open StoneCechConstruction

/-- Pull back interval-valued coordinates along f and restrict to the closures. -/
def betaMap {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Beta X → Beta Y := by
  let T : Ch10.TychonoffCube.Cube (Ch10.TychonoffCube.EvaluationIndex X) →
      Ch10.TychonoffCube.Cube (Ch10.TychonoffCube.EvaluationIndex Y) :=
    fun t g => t (g.comp f)
  have hT : Continuous T := continuous_pi (fun g => continuous_apply (g.comp f))
  have hmaps : MapsTo T (range (Ch10.TychonoffCube.evaluationMap (X := X)))
      (range (Ch10.TychonoffCube.evaluationMap (X := Y))) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, rfl⟩
  exact fun b => ⟨T b.val, hmaps.closure hT b.property⟩

def betaMapType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → [TopologicalSpace X] → [TopologicalSpace Y] →
    C(X, Y) → Beta X → Beta Y

def betaMapValue : betaMapType := @betaMap

def bounded_real_extension : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], Ch07.SeparationConventions.tychonoffValue X →
    ∀ (f : X → ℝ), Continuous f → (∃ M : ℝ, ∀ x, |f x| ≤ M) →
      ∃! F : Beta X → ℝ, Continuous F ∧ F ∘ betaUnit = f

def compactification_image : Prop :=
  ∀ {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K],
    Ch07.SeparationConventions.tychonoffValue X → ∀ i : X → K,
    LocalCompactConventions.HausdorffCompactification i →
      ∃ F : Beta X → K, Continuous F ∧ Function.Surjective F ∧ F ∘ betaUnit = i

def betaMap_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)), Continuous (betaMap f)

def betaMap_unit : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)), betaMap f ∘ betaUnit = betaUnit ∘ f

/-- Uniqueness is among all continuous maps, not only coordinate reindexings. -/
def betaMap_unique : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y],
    Ch07.SeparationConventions.tychonoffValue X →
    Ch07.SeparationConventions.tychonoffValue Y → ∀ (f : C(X, Y))
    (F : Beta X → Beta Y), Continuous F → F ∘ betaUnit = betaUnit ∘ f → F = betaMap f

/-- The original unbundled-map existence and uniqueness formulation. -/
def betaMap_extension : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y],
    Ch07.SeparationConventions.tychonoffValue X →
    Ch07.SeparationConventions.tychonoffValue Y → ∀ (f : X → Y), Continuous f →
    ∃! F : Beta X → Beta Y, Continuous F ∧ F ∘ betaUnit = betaUnit ∘ f

def betaMap_id : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], betaMap (ContinuousMap.id X) = id

def betaMap_comp : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)), betaMap (g.comp f) = betaMap g ∘ betaMap f

def compact_betaSet_eq_range : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X],
    betaSet X = range (Ch10.TychonoffCube.evaluationMap (X := X))

def compact_betaUnit_surjective : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X],
    Function.Surjective (betaUnit (X := X))

def empty_beta_space : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X], IsEmpty (Beta X)

end Specs.D10Topology.Ch11.StoneCechConsequences
