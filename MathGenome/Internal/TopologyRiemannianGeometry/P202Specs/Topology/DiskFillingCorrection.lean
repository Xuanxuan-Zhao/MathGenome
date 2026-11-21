import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.HigherHomotopy

/-! The difference correction in paper.tex, lines 949–974.
Only surjectivity in the disk's own dimension is assumed. -/
namespace P202Specs.Topology.ExpectedDiskFillingCorrection
universe u
open scoped _root_.Topology

def fillingCorrection : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (A : Set Y) (n : ℕ),
    (∀ x : A, Function.Surjective
      (higherInduced (n + 1)
        (⟨⟨Subtype.val, continuous_subtype_val⟩, rfl⟩ : PointedMap A Y x x.val))) →
    ∀ (f : RelativeDiskMap (n + 2) A) (g : C(ClosedDisk (n + 2), A)),
      (∀ z ∈ DiskBoundary (n + 2), (g z).val = f.val z) →
      ∃ g' : C(ClosedDisk (n + 2), A),
        Nonempty (f.val.HomotopyRel
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)).comp g')
          (DiskBoundary (n + 2)))

end P202Specs.Topology.ExpectedDiskFillingCorrection
