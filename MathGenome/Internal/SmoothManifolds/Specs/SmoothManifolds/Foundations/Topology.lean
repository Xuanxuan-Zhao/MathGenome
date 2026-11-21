import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Models
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Separation.Regular

/-! Independent statements of the local topology and component conclusions of
M01.01. Compact exhaustion is the separately allocated downstream obligation.
All statements use the original chart data, including dimension zero and empty bases. -/
namespace Specs.SmoothManifolds.Foundations.Topology
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
universe u

def locallyCompactSpaceType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M],
    TopologicalManifold n kind M → LocallyCompactSpace M

def locallyPathConnectedSpaceType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M],
    TopologicalManifold n kind M → LocallyPathConnectedSpace M

def countable_chart_coverType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (A : TopologicalManifold n kind M),
    ∃ C : Set (ModelChart n kind M), C.Countable ∧ C ⊆ A.atlas ∧
      ∀ p : M, ∃ c ∈ C, p ∈ c.source

def regularSpaceType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M],
    TopologicalManifold n kind M → RegularSpace M

def lindelofSpaceType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M],
    TopologicalManifold n kind M → LindelofSpace M

def paracompactSpaceType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M],
    TopologicalManifold n kind M → ParacompactSpace M

def isOpen_connectedComponentType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M],
    TopologicalManifold n kind M → ∀ p : M, IsOpen (connectedComponent p)

def isPathConnected_connectedComponentType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M],
    TopologicalManifold n kind M → ∀ p : M, IsPathConnected (connectedComponent p)

/-- The range is exactly the set of nonempty connected components. In particular
it is empty when the base is empty, with no chosen point or nonemptiness assumption. -/
def countable_connectedComponentsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M],
    TopologicalManifold n kind M → (Set.range (connectedComponent (α := M))).Countable

end Specs.SmoothManifolds.Foundations.Topology
