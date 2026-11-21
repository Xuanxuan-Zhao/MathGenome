import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ResidualFoundation
import Mathlib.Data.ENat.Lattice

/-! W37, first stage: extended natural residual distances never decrease.
The infimum of an empty family is infinity, so unreachable vertices are included.
Shortest means minimum length among all directed walks. -/
open scoped Classical
universe u v
namespace P205.Networks.DistanceSpec
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

noncomputable def distance (G : Digraph V A) (s x : V) : ℕ∞ :=
  ⨅ p : Walk G s x, (p.length : ℕ∞)

def IsShortest {G : Digraph V A} {s t : V} (p : Walk G s t) : Prop :=
  ∀ q : Walk G s t, p.length ≤ q.length

section Expected
set_option linter.checkUnivs false

def distanceType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  Digraph V A → V → V → ℕ∞
def IsShortestType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  {G : Digraph V A} {s t : V}, Walk G s t → Prop

/-- Full-bottleneck shortest augmentation, at every feasible real flow. -/
def residual_distance_mono : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), N.Feasible f →
    ∀ (p : Walk (BoundedSpec.graph N.graph (fun _ => 0) N.capacity f) N.source N.sink),
      p.IsPath → IsShortest p → ∀ δ : ℝ,
      BoundedSpec.Bottleneck N.graph (fun _ => 0) N.capacity f p δ →
      ∀ x : V,
        distance (BoundedSpec.graph N.graph (fun _ => 0) N.capacity f) N.source x ≤
        distance (BoundedSpec.graph N.graph (fun _ => 0) N.capacity
          (BoundedSpec.augment N.graph (fun _ => 0) N.capacity f p δ)) N.source x
end Expected
end P205.Networks.DistanceSpec
