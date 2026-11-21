import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Models
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Topology
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Normed.Module.Convex
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.StandardParacompactness

namespace SmoothManifolds
open Set Topology
universe u

/-- The model is closed in its finite-dimensional ambient space. -/
theorem isClosed_modelSet (n : ℕ) (kind : ModelKind) : IsClosed (modelSet n kind) := by
  cases kind with
  | euclidean => exact isClosed_univ
  | halfSpace =>
    cases n with
    | zero => exact isClosed_univ
    | succ n => exact isClosed_le continuous_const (continuous_apply (Fin.last n))

/-- Both permitted models are convex in their ambient vector space. -/
theorem convex_modelSet (n : ℕ) (kind : ModelKind) : Convex ℝ (modelSet n kind) := by
  cases kind with
  | euclidean => exact convex_univ
  | halfSpace =>
    cases n with
    | zero => exact convex_univ
    | succ n =>
      exact convex_halfSpace_ge (⟨fun _ _ => rfl, fun _ _ => rfl⟩ :
        IsLinearMap ℝ (fun x : Euclidean (n + 1) => x (Fin.last n))) 0

namespace TopologicalManifold
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]

/-- Transfer only the existing atlas and its chosen charts to Mathlib's chart interface. -/
@[instance_reducible] noncomputable def toChartedSpace (A : TopologicalManifold n kind M) :
    ChartedSpace (ModelSpace n kind) M where
  atlas := A.atlas
  chartAt := A.chartAt
  mem_chart_source := A.mem_chartAt_source
  chart_mem_atlas := A.chartAt_mem

theorem locallyCompactSpace (A : TopologicalManifold n kind M) : LocallyCompactSpace M := by
  let : LocallyCompactSpace (ModelSpace n kind) := (isClosed_modelSet n kind).locallyCompactSpace
  let := A.toChartedSpace
  exact ChartedSpace.locallyCompactSpace (ModelSpace n kind) M

theorem locallyPathConnectedSpace (A : TopologicalManifold n kind M) :
    LocallyPathConnectedSpace M := by
  let : LocallyPathConnectedSpace (ModelSpace n kind) :=
    (convex_modelSet n kind).locallyPathConnectedSpace
  let := A.toChartedSpace
  exact ChartedSpace.locallyPathConnectedSpace (ModelSpace n kind) M

theorem regularSpace (A : TopologicalManifold n kind M) : RegularSpace M := by
  let := A.hausdorff
  let := A.locallyCompactSpace
  infer_instance

theorem lindelofSpace (A : TopologicalManifold n kind M) : LindelofSpace M := by
  let := A.secondCountable
  infer_instance

theorem paracompactSpace (A : TopologicalManifold n kind M) : ParacompactSpace M :=
  D10Topology.Ch15.regular_lindelof_paracompact M A.regularSpace A.lindelofSpace

theorem countable_chart_cover (A : TopologicalManifold n kind M) :
    ∃ C : Set (ModelChart n kind M), C.Countable ∧ C ⊆ A.atlas ∧
      ∀ p : M, ∃ c ∈ C, p ∈ c.source := by
  let := A.lindelofSpace
  obtain ⟨S, hS, hcover⟩ := isLindelof_univ.elim_countable_subcover
    (fun p : M => (A.chartAt p).source) (fun p => (A.chartAt p).open_source)
    (by intro p _; exact mem_iUnion.mpr ⟨p, A.mem_chartAt_source p⟩)
  refine ⟨A.chartAt '' S, hS.image _, ?_, ?_⟩
  · rintro c ⟨p, _, rfl⟩
    exact A.chartAt_mem p
  · intro p
    obtain ⟨q, hq, hp⟩ := mem_iUnion₂.mp (hcover (mem_univ p))
    exact ⟨A.chartAt q, mem_image_of_mem _ hq, hp⟩

theorem isOpen_connectedComponent (A : TopologicalManifold n kind M) (p : M) :
    IsOpen (connectedComponent p) := by
  let := A.locallyPathConnectedSpace
  exact _root_.isOpen_connectedComponent

theorem isPathConnected_connectedComponent (A : TopologicalManifold n kind M) (p : M) :
    IsPathConnected (connectedComponent p) := by
  let := A.locallyPathConnectedSpace
  rw [← pathComponent_eq_connectedComponent]
  exact isPathConnected_pathComponent

theorem countable_connectedComponents (A : TopologicalManifold n kind M) :
    (Set.range (connectedComponent (α := M))).Countable := by
  let := A.secondCountable
  have hd : (Set.range (connectedComponent (α := M))).PairwiseDisjoint id := by
    rintro s ⟨p, rfl⟩ t ⟨q, rfl⟩ hne
    exact connectedComponent_disjoint hne
  apply hd.countable_of_isOpen
  · rintro s ⟨p, rfl⟩
    exact A.isOpen_connectedComponent p
  · rintro s ⟨p, rfl⟩
    exact ⟨p, mem_connectedComponent⟩

end TopologicalManifold
end SmoothManifolds
