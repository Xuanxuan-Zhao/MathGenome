import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.HigherHomotopy

/-! The boundary-filling step in paper.tex, lines 943–949.
The homomorphism is induced by the actual inclusion. No separation,
connectedness, or local regularity assumptions are made on either space. -/
namespace P202Specs.Topology.ExpectedDiskBoundaryFilling

universe u

def boundaryFilling : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (A : Set Y) (n : ℕ),
    (∀ x : A, Function.Injective
      (higherInduced n
        (⟨⟨Subtype.val, continuous_subtype_val⟩, rfl⟩ : PointedMap A Y x x.val))) →
    ∀ f : RelativeDiskMap (n + 2) A,
      ∃ g : C(ClosedDisk (n + 2), A),
        ∀ z ∈ DiskBoundary (n + 2), (g z).val = f.val z

end P202Specs.Topology.ExpectedDiskBoundaryFilling
