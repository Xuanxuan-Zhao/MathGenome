import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import Mathlib.Topology.Order.IntermediateValue

/-! Independent propositions for chapters/01.tex, d04:01:connectedness.
`IsPreconnected` expresses the source's separation definition, which permits
empty sets. `OrdConnected` means an arbitrary real interval, with any endpoints.
Euclidean path and polygonal conclusions use the canonical upstream objects. -/
noncomputable section
open Set Topology
universe u v
namespace Specs.D04.C01.Connectedness
open Specs.D04.C01.EuclideanInterfaces.Model

def connected_imageType : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : X → Y), IsPreconnected A → ContinuousOn f A →
    IsPreconnected (f '' A)

def interval_connectedType : Prop :=
  ∀ (I : Set ℝ), OrdConnected I → IsPreconnected I

def path_connected_space_connectedType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X],
    (∀ a b : X, Nonempty (Path a b)) → IsPreconnected (univ : Set X)

def pathConnected_connectedType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)), PathConnected A → Connected A

def convexSet_pathConnectedType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)), ConvexSet A → PathConnected A

def connected_intermediate_valueType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X) (f : X → ℝ),
    IsPreconnected A → ContinuousOn f A →
    ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ uIcc (f a) (f b), ∃ x ∈ A, f x = c

def relative_connected_imageType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m),
    Connected A → RelativeContinuous A f → Connected (range f)

def relative_connected_intermediate_valueType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (f : A → ℝ),
    Connected A → Continuous f →
    ∀ a b : A, ∀ c ∈ uIcc (f a) (f b), ∃ x : A, f x = c

def open_connected_polygonallyConnectedType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)), Open U → Connected U → PolygonallyConnected U

end Specs.D04.C01.Connectedness
