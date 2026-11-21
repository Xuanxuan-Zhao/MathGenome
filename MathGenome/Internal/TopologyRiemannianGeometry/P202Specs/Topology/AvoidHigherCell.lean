import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellStructures

/-! The open-cell lemma, paper.tex 795–841.  No CW structure is assumed
on the target, and the fixed subset of the disk is an arbitrary preimage. -/

noncomputable section
universe u

namespace P202Specs.Topology.AvoidHigherCell
open P202.Cellular

/-- Every map of a lower dimensional disk can be deformed, relative to the
preimage of the complement of an open Euclidean cell, to miss a cell point. -/
def avoidHigherCell : Prop :=
  ∀ {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    (n k : ℕ), n < k →
    ∀ (U : Set Z), IsOpen U →
    ∀ (_e : EuclideanSpace ℝ (Fin k) ≃ₜ U) (f : C(Disk n, Z)),
    ∃ (g : C(Disk n, Z)) (H : C(Disk n × Interval, Z)) (p : U),
      (∀ x, H (x, 0) = f x) ∧
      (∀ x, H (x, 1) = g x) ∧
      (∀ x t, f x ∉ U → H (x, t) = f x) ∧
      ∀ x, g x ≠ (p : Z)

end P202Specs.Topology.AvoidHigherCell
