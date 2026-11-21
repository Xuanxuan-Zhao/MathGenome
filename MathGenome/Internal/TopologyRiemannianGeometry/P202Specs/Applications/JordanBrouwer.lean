import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.NeighborhoodCohomology
import Mathlib.Topology.Connected.Clopen

/-!
Independent statements for the separation assertion of paper.tex 2854–2884,
Theorem T34. `Sphere n` is the existing unit sphere in Euclidean (n+1)-space.
Components use the actual complement subspace topology; frontiers are taken
in the ambient sphere. In particular n = 1 has domain the two-point sphere.
-/
noncomputable section
open Set Topology

namespace P202Specs.JordanBrouwer
open P202.Duality.NeighborhoodCohomology

/-- Every sufficiently small patch can be added to the complement without
separating it. This is a proof interface, not an extra hypothesis of separation. -/
def HasNonseparatingPatches {X : Type*} [TopologicalSpace X] (K : Set X) : Prop :=
  ∀ x ∈ K, ∀ O : Set X, IsOpen O → x ∈ O →
    ∃ D : Set X, x ∈ D ∧ D ⊆ K ∩ O ∧ IsPreconnected (Kᶜ ∪ D)

namespace Expected

/-- The complete assigned assertion, with no regularity hypothesis on the embedding. -/
def separation : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (e : Sphere (n - 1) → Sphere n),
    Topology.IsEmbedding e →
      Nonempty (ConnectedComponents ((range e)ᶜ : Set (Sphere n)) ≃ Fin 2) ∧
      ∀ x ∈ (range e)ᶜ,
        frontier (connectedComponentIn (range e)ᶜ x) = range e

/-- The point-set boundary argument used in the original proof. -/
def boundaryFromPatches : Prop :=
  ∀ (X : Type*) [TopologicalSpace X] [LocallyConnectedSpace X]
    (K : Set X), IsClosed K → HasNonseparatingPatches K →
      ∀ x ∈ Kᶜ, frontier (connectedComponentIn Kᶜ x) = K

end Expected
end P202Specs.JordanBrouwer
