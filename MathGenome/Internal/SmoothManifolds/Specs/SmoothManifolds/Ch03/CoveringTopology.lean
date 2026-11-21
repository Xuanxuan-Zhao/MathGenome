import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Models
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Bases

/-! Independent topological prerequisites for M03.07. The topology on the total
space is given, and no separation or countability axiom on it is assumed.
Mathlib's covering predicate permits empty fibers and empty total spaces.
`PreconnectedSpace` also permits the empty case, so the connected conclusions
below include it without an artificial nonemptiness hypothesis. -/
namespace Specs.SmoothManifolds.Ch03.CoveringTopology
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
universe u v

def hausdorffType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} {E : Type v}
    [TopologicalSpace M] [TopologicalSpace E],
    TopologicalManifold n kind M → ∀ (p : E → M), IsCoveringMap p → T2Space E

def secondCountable_of_countable_fibersType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} {E : Type v}
    [TopologicalSpace M] [TopologicalSpace E],
    TopologicalManifold n kind M → ∀ (p : E → M), IsCoveringMap p →
      (∀ y : M, (p ⁻¹' {y}).Countable) → SecondCountableTopology E

def secondCountable_of_preconnectedType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} {E : Type v}
    [TopologicalSpace M] [TopologicalSpace E] [PreconnectedSpace E],
    TopologicalManifold n kind M → ∀ (p : E → M), IsCoveringMap p →
      SecondCountableTopology E

def countable_fibers_of_preconnectedType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} {E : Type v}
    [TopologicalSpace M] [TopologicalSpace E] [PreconnectedSpace E],
    TopologicalManifold n kind M → ∀ (p : E → M), IsCoveringMap p →
      ∀ y : M, (p ⁻¹' {y}).Countable

end Specs.SmoothManifolds.Ch03.CoveringTopology
