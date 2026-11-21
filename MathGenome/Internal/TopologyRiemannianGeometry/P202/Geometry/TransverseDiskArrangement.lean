import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.TransverseDiskArrangement
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.RegularLevels
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.BoundaryRegularLevels
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.Sard
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.TransversePreimage
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.EmbeddedComparison
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith

/-! The transverse chart-disk arrangement of paper.tex 5032–5052.
The proof constructs the supplied-chart cover and actual smooth circles,
selects successive radii using smooth restricted squared-radius maps and Sard,
and proves transverse finite intersections with no triple points. Differential
independence and the inverse theorem give arbitrarily small exact local normal
forms preserving disk signs and two-sided smooth regular endpoint germs. -/
set_option autoImplicit false
noncomputable section
open Set Topology
open scoped ContDiff
open P202Specs.PlanarRegionTopology (Plane)
open P202Specs.SurfaceRegionConstruction
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
universe u v

namespace P202.SurfaceRegionConstruction
variable {X : Type u} [TopologicalSpace X]

/-- A connected set missing an open set's frontier cannot switch membership.
This is the disk-membership step in the source's chart-containment argument. -/
theorem subset_of_avoids_frontier {U C : Set X} (hU : IsOpen U)
    (hC : IsPreconnected C) (hmiss : Disjoint C (frontier U))
    (hmeet : (C ∩ U).Nonempty) : C ⊆ U := by
  apply hC.subset_of_closure_inter_subset hU hmeet
  rintro x ⟨hxcl, hxC⟩
  by_contra hxU
  exact Set.disjoint_left.mp hmiss hxC
    ⟨hxcl, by simpa only [hU.interior_eq] using hxU⟩

/-- The closure of a connected complementary component remains inside one
closed chart disk, as soon as the disks cover it and their frontiers are
contained in the graph. Finiteness and transversality are not assumed here. -/
theorem closure_subset_one_cover {ι : Type*} (U K : ι → Set X) (G C : Set X)
    (hU : ∀ i, IsOpen (U i)) (hUK : ∀ i, U i ⊆ K i)
    (hK : ∀ i, IsClosed (K i)) (hfrontier : ∀ i, frontier (U i) ⊆ G)
    (hcover : C ⊆ ⋃ i, U i) (hC : IsConnected C) (hCG : Disjoint C G) :
    ∃ i, closure C ⊆ K i := by
  obtain ⟨p, hp⟩ := hC.nonempty
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp (hcover hp)
  have hsub : C ⊆ U i := subset_of_avoids_frontier (hU i) hC.isPreconnected
    (hCG.mono_right (hfrontier i)) ⟨p, hp, hpi⟩
  exact ⟨i, closure_minimal (hsub.trans (hUK i)) (hK i)⟩

namespace ChartDisk
open P202Specs.SurfaceRegionConstruction.ChartDisk
variable {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A)

theorem isOpen_inner : IsOpen d.inner :=
  d.chart.isOpen_inter_preimage Metric.isOpen_ball

theorem outer_subset_source : d.outer ⊆ d.chart.source := by
  rintro x ⟨y, hy, rfl⟩
  exact d.chart.map_target (d.closedBall_subset hy)

theorem inner_subset_outer : d.inner ⊆ d.outer := by
  rintro x ⟨hxs, hxb⟩
  refine ⟨d.chart x, Metric.closedBall_subset_closedBall d.inner_lt_outer.le
    (Metric.ball_subset_closedBall hxb), ?_⟩
  exact d.chart.left_inv hxs

theorem isCompact_outer : IsCompact d.outer :=
  (isCompact_closedBall d.center d.outerRadius).image_of_continuousOn
    (d.chart.symm.continuousOn.mono d.closedBall_subset)

theorem closure_inner_subset_outer [T2Space X] : closure d.inner ⊆ d.outer :=
  closure_minimal (inner_subset_outer d) (isCompact_outer d).isClosed

theorem closedBall_subset_target {r : ℝ} (hr : r ≤ d.outerRadius) :
    Metric.closedBall d.center r ⊆ d.chart.target :=
  (Metric.closedBall_subset_closedBall hr).trans d.closedBall_subset

theorem isOpen_openAtRadius (r : ℝ) : IsOpen (openAtRadius d r) :=
  d.chart.isOpen_inter_preimage Metric.isOpen_ball

theorem isCompact_closedAtRadius {r : ℝ} (hr : r ≤ d.outerRadius) :
    IsCompact (closedAtRadius d r) :=
  (isCompact_closedBall d.center r).image_of_continuousOn
    (d.chart.symm.continuousOn.mono (closedBall_subset_target d hr))

theorem closedAtRadius_subset_source {r : ℝ} (hr : r ≤ d.outerRadius) :
    closedAtRadius d r ⊆ d.chart.source := by
  rintro x ⟨z, hz, rfl⟩
  exact d.chart.map_target (closedBall_subset_target d hr hz)

theorem openAtRadius_subset_closedAtRadius (r : ℝ) :
    openAtRadius d r ⊆ closedAtRadius d r := by
  rintro x ⟨hxs, hxb⟩
  exact ⟨d.chart x, Metric.ball_subset_closedBall hxb, d.chart.left_inv hxs⟩

/-- The final disks still cover the inner disks at every permitted radius. -/
theorem inner_subset_openAtRadius {r : ℝ} (hr : d.innerRadius ≤ r) :
    d.inner ⊆ openAtRadius d r :=
  inter_subset_inter_right _ (preimage_mono (Metric.ball_subset_ball hr))

/-- The image/closure equality is ambient, including at the disk boundary;
the compact outer disk prevents loss of points through the chart boundary. -/
theorem closure_openAtRadius [T2Space X] {r : ℝ} (hpos : 0 < r)
    (hr : r ≤ d.outerRadius) :
    closure (openAtRadius d r) = closedAtRadius d r := by
  have hcl : closure (openAtRadius d r) ⊆ d.chart.source :=
    (closure_minimal (openAtRadius_subset_closedAtRadius d r)
      (isCompact_closedAtRadius d hr).isClosed).trans (closedAtRadius_subset_source d hr)
  have hi : d.chart.IsImage (openAtRadius d r) (Metric.ball d.center r) := by
    intro x hx
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  have heq := hi.closure.symm_image_eq
  rw [closure_ball d.center hpos.ne', inter_eq_right.mpr (closedBall_subset_target d hr),
    inter_eq_right.mpr hcl] at heq
  exact heq.symm

/-- The disk frontier is exactly the actual coordinate circle selected by
Sard, with no other boundary pieces introduced by the partial chart. -/
theorem frontier_openAtRadius [T2Space X] {r : ℝ} (hpos : 0 < r)
    (hr : r ≤ d.outerRadius) :
    frontier (openAtRadius d r) = circleAtRadius d r := by
  have hfront : frontier (openAtRadius d r) ⊆ d.chart.source := by
    rw [frontier, closure_openAtRadius d hpos hr]
    exact sdiff_subset.trans (closedAtRadius_subset_source d hr)
  have hsph : Metric.sphere d.center r ⊆ d.chart.target :=
    Metric.sphere_subset_closedBall.trans (closedBall_subset_target d hr)
  have hi : d.chart.IsImage (openAtRadius d r) (Metric.ball d.center r) := by
    intro x hx
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  have heq := hi.frontier.symm_image_eq
  rw [frontier_ball d.center hpos.ne', inter_eq_right.mpr hsph,
    inter_eq_right.mpr hfront] at heq
  exact heq.symm

theorem closure_openAtRadius_subset_outer [T2Space X] {r : ℝ} (hpos : 0 < r)
    (hr : r ≤ d.outerRadius) : closure (openAtRadius d r) ⊆ d.outer := by
  rw [closure_openAtRadius d hpos hr]
  exact image_mono (Metric.closedBall_subset_closedBall hr)

end ChartDisk

/-- The source's entire chart-containment argument for the selected final
circles. Both the final closed disk and the original atlas chart are retained
in the conclusion. No regularity of the crossings is used at this stage. -/
theorem closure_in_selected_chart [T2Space X] {ι : Type*}
    {A : Set (OpenPartialHomeomorph X Plane)} (d : ι → ChartDisk X A) (r : ι → ℝ)
    (hlower : ∀ i, (d i).innerRadius ≤ r i) (hupper : ∀ i, r i ≤ (d i).outerRadius)
    (G C : Set X) (hcircle : ∀ i, ChartDisk.circleAtRadius (d i) (r i) ⊆ G)
    (hcover : C ⊆ ⋃ i, (d i).inner) (hC : IsConnected C) (hCG : Disjoint C G) :
    ∃ i, closure C ⊆ ChartDisk.closedAtRadius (d i) (r i) ∧
      closure C ⊆ (d i).chart.source := by
  have hpos : ∀ i, 0 < r i := fun i => (d i).inner_pos.trans_le (hlower i)
  have hcover' : C ⊆ ⋃ i, ChartDisk.openAtRadius (d i) (r i) :=
    hcover.trans (iUnion_mono (fun i => P202.SurfaceRegionConstruction.ChartDisk.inner_subset_openAtRadius (d i) (hlower i)))
  obtain ⟨i, hi⟩ := closure_subset_one_cover
    (fun i => ChartDisk.openAtRadius (d i) (r i))
    (fun i => ChartDisk.closedAtRadius (d i) (r i)) G C
    (fun i => P202.SurfaceRegionConstruction.ChartDisk.isOpen_openAtRadius (d i) (r i))
    (fun i => P202.SurfaceRegionConstruction.ChartDisk.openAtRadius_subset_closedAtRadius (d i) (r i))
    (fun i => (P202.SurfaceRegionConstruction.ChartDisk.isCompact_closedAtRadius (d i) (hupper i)).isClosed)
    (fun i => by rw [P202.SurfaceRegionConstruction.ChartDisk.frontier_openAtRadius (d i) (hpos i) (hupper i)]; exact hcircle i)
    hcover' hC hCG
  exact ⟨i, hi, hi.trans (P202.SurfaceRegionConstruction.ChartDisk.closedAtRadius_subset_source (d i) (hupper i))⟩

/-- A single supplied chart suffices; no global cover hypothesis is needed. -/
theorem exists_chartDisk_in_chart (A : Set (OpenPartialHomeomorph X Plane))
    (e : OpenPartialHomeomorph X Plane) (he : e ∈ A) (p : X) (hp : p ∈ e.source) :
    ∃ d : ChartDisk X A, d.chart = e ∧ p ∈ d.inner := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e p) (e.map_source hp)
  let d : ChartDisk X A := {
    chart := e
    chart_mem := he
    center := e p
    innerRadius := r / 4
    outerRadius := r / 2
    inner_pos := by linarith
    inner_lt_outer := by linarith
    closedBall_subset := (Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hball }
  exact ⟨d, rfl, hp, by change dist (e p) (e p) < r / 4; simpa using hr⟩

/-- Only K needs to be covered by the supplied family. The ambient surface
may be noncompact, and the family may leave its other points uncovered. -/
theorem finite_chartDisk_cover_on (A : Set (OpenPartialHomeomorph X Plane))
    (K : Set X) (hK : IsCompact K)
    (hA : ∀ p ∈ K, ∃ e ∈ A, p ∈ e.source) :
    ∃ (n : ℕ) (d : Fin n → ChartDisk X A), K ⊆ ⋃ i, (d i).inner := by
  classical
  have hat : ∀ p : K, ∃ d : ChartDisk X A, p.val ∈ d.inner := by
    intro p
    obtain ⟨e, he, hp⟩ := hA p.val p.property
    obtain ⟨d, _, hd⟩ := exists_chartDisk_in_chart A e he p.val hp
    exact ⟨d, hd⟩
  choose d hd using hat
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun p : K => (d p).inner)
    (fun p => P202.SurfaceRegionConstruction.ChartDisk.isOpen_inner (d p))
    (fun p hp => Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hd ⟨p, hp⟩⟩)
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => d (e.symm i).val, ?_⟩
  intro x hx
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact Set.mem_iUnion.mpr ⟨e ⟨p, hp⟩, by simpa using hxp⟩

/-- The compact-subset cover uses the prescribed smooth chart family and
retains its original chart-membership witnesses. -/
theorem finite_supplied_smooth_chartDisk_cover
    (K : Set X) (hK : IsCompact K) (A : Set (ModelChart 2 .euclidean X))
    (hA : ∀ p ∈ K, ∃ e ∈ A, p ∈ e.source) :
    ∃ (n : ℕ) (d : Fin n → ChartDisk X (planeChartFamily A)),
      K ⊆ ⋃ i, (d i).inner := by
  apply finite_chartDisk_cover_on _ K hK
  intro p hp
  obtain ⟨e, he, hpe⟩ := hA p hp
  exact ⟨euclideanChartToPlane e, ⟨e, he, rfl⟩, hpe⟩

/-- A chart around any point contains concentric closed disks with room to
increase the inner radius. This makes no compactness assumption on the surface. -/
theorem exists_chartDisk_at (A : Set (OpenPartialHomeomorph X Plane))
    (hA : ∀ p : X, ∃ e ∈ A, p ∈ e.source) (p : X) :
    ∃ d : ChartDisk X A, p ∈ d.inner := by
  obtain ⟨e, he, hp⟩ := hA p
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e p) (e.map_source hp)
  let d : ChartDisk X A := {
    chart := e
    chart_mem := he
    center := e p
    innerRadius := r / 4
    outerRadius := r / 2
    inner_pos := by linarith
    inner_lt_outer := by linarith
    closedBall_subset := (Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hball }
  exact ⟨d, hp, by change dist (e p) (e p) < r / 4; simpa using hr⟩

/-- Compactness produces a finite chart-disk cover, with perturbation room in
all the charts. It also works for the empty compact subset. -/
theorem finite_chartDisk_cover (A : Set (OpenPartialHomeomorph X Plane))
    (hA : ∀ p : X, ∃ e ∈ A, p ∈ e.source) (K : Set X) (hK : IsCompact K) :
    ∃ (n : ℕ) (d : Fin n → ChartDisk X A), K ⊆ ⋃ i, (d i).inner := by
  classical
  choose d hd using exists_chartDisk_at A hA
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun p => (d p).inner)
    (fun p => P202.SurfaceRegionConstruction.ChartDisk.isOpen_inner (d p)) (fun p _ => Set.mem_iUnion.mpr ⟨p, hd p⟩)
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => d (e.symm i).val, ?_⟩
  intro x hx
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact Set.mem_iUnion.mpr ⟨e ⟨p, hp⟩, by simpa using hxp⟩


/-- This cover consists of actual charts of the original smooth atlas, after
only the fixed change of coordinate norm. -/
theorem finite_smooth_chartDisk_cover (S : SmoothManifold 2 .euclidean X)
    (K : Set X) (hK : IsCompact K) :
    ∃ (n : ℕ) (d : Fin n → ChartDisk X (planeAtlas S)), K ⊆ ⋃ i, (d i).inner := by
  apply finite_chartDisk_cover _ _ _ hK
  intro p
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  exact ⟨euclideanChartToPlane e, ⟨e, he, rfl⟩, hpe⟩

namespace RadiusSelection
open SmoothManifolds.SardData SmoothManifolds.MapData SmoothManifolds.MapClassData
open MeasureTheory

/-- The ambient dimension must be positive to discard a finite set of values.
In dimension zero a point has positive counting measure. -/
theorem finite_isNull {n : ℕ} {kind : ModelKind} {Y : Type*} [TopologicalSpace Y]
    (T : SmoothManifold n kind Y) (hn : 0 < n) {F : Set Y} (hF : F.Finite) :
    IsNull T F := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  intro e _
  exact ((hF.inter_of_left e.source).image (fun y => (e y).val)).measure_zero volume

/-- Nullity is tested on actual coordinate images, so the union does not
require measurable critical-value sets. -/
theorem isNull_iUnion {n : ℕ} {kind : ModelKind} {Y : Type*} [TopologicalSpace Y]
    (T : SmoothManifold n kind Y) {ι : Type*} [Countable ι]
    (A : ι → Set Y) (hA : ∀ i, IsNull T (A i)) : IsNull T (⋃ i, A i) := by
  intro e he
  simp only [iUnion_inter, image_iUnion]
  exact measure_iUnion_null (fun i => hA i e he)

/-- Simultaneously regular values for finitely many actual smooth maps,
also avoiding finitely many previously formed crossings. The maps may have
different domains; their smooth manifold structures are explicit. This is
the Sard selection step once the curve portions and radius maps are built. -/
theorem exists_common_regular_value {ι : Type*} [Finite ι]
    {n : ℕ} {kind : ModelKind} {Y : Type*} [TopologicalSpace Y]
    (T : SmoothManifold n kind Y) (hn : 0 < n)
    (m : ι → ℕ) (a : ι → ModelKind) (M : ι → Type u)
    [∀ i, TopologicalSpace (M i)] (S : ∀ i, SmoothManifold (m i) (a i) (M i))
    (f : ∀ i, M i → Y) (hf : ∀ i, IsSmoothMap (S i) T (f i))
    {F : Set Y} (hF : F.Finite) {O : Set Y} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ y ∈ O, y ∉ F ∧ ∀ i, IsRegularValue (S i) T (f i) y := by
  have hc : IsNull T (⋃ i, criticalValues (S i) T (f i)) :=
    isNull_iUnion T _ (fun i => SmoothManifolds.Sard.sard (S i) T (f i) (hf i))
  have hnull : IsNull T (F ∪ ⋃ i, criticalValues (S i) T (f i)) := by
    intro e he
    simp only [union_inter_distrib_right, image_union]
    exact measure_union_null (finite_isNull T hn hF e he) (hc e he)
  obtain ⟨y, hyO, hy⟩ := dense_iff_inter_open.mp
    (SmoothManifolds.Sard.null_complement_dense T _ hnull) O hO hne
  refine ⟨y, hyO, fun hyF => hy (Or.inl hyF), ?_⟩
  intro i p hpy
  by_contra hp
  exact hy (Or.inr (mem_iUnion.mpr ⟨i, ⟨p, hp, hpy⟩⟩))

/-- Squared planar radius in an original chart is an actual P104 smooth
map, using the standard real-line target chart and the L² coordinate norm. -/
theorem squaredRadius_smooth {n : ℕ} {a b : ModelKind}
    {C : Type u} {M : Type v} [TopologicalSpace C] [TopologicalSpace M]
    (S : SmoothManifold n a C) (T : SmoothManifold 2 b M)
    (R : SmoothManifold 1 .euclidean (Euclidean 1))
    (hR : SmoothManifolds.euclideanChart 1 ∈ R.smoothStructure.val)
    (j : C → M) (hj : IsSmoothMap S T j)
    (e : ModelChart 2 b M) (he : e ∈ T.smoothStructure.val)
    (himage : ∀ p, j p ∈ e.source) (c : Plane) :
    IsSmoothMap S R (fun p (_ : Fin 1) => ‖coordinates e (j p) - c‖ ^ 2) := by
  intro p
  obtain ⟨d, hd, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpd, F, hF, hEq⟩ := (hj p).2 d hd e he hp (himage p)
  apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    S.smoothStructure.property.1 R.smoothStructure.property.1 _ p).mpr
  have hcont : ContinuousAt (fun p => coordinates e (j p)) p := by
    exact toPlane.continuous.continuousAt.comp
      (continuous_subtype_val.continuousAt.comp ((e.continuousAt (himage p)).comp (hj p).1))
  refine ⟨continuousAt_pi.mpr (fun _ => (hcont.sub continuousAt_const).norm.pow 2),
    d, hd, SmoothManifolds.euclideanChart 1, hR, hp, mem_univ _,
    U, hU, hpd, fun z (_ : Fin 1) => ‖toPlane (F z) - c‖ ^ 2, ?_, ?_⟩
  · apply contDiffOn_pi.mpr
    intro i
    exact ((contDiff_norm_sq ℝ).contDiffOn.comp
      ((toPlane.contDiff.comp_contDiffOn hF).sub contDiffOn_const) (fun _ _ => mem_univ _))
  · exact hEq.mono (fun q h => funext (fun _ => by simpa only [coordinates, SmoothManifolds.euclideanChart_val] using congrArg (fun v => ‖toPlane v - c‖ ^ 2) h))

/-- The curve portion in the new chart is an actual open submanifold of the
curve, and its coordinate squared-radius function is an actual smooth map. -/
theorem exists_restricted_squaredRadius {n : ℕ} {a b : ModelKind}
    {C : Type u} {M : Type v} [TopologicalSpace C] [TopologicalSpace M]
    (S : SmoothManifold n a C) (T : SmoothManifold 2 b M)
    (R : SmoothManifold 1 .euclidean (Euclidean 1))
    (hR : SmoothManifolds.euclideanChart 1 ∈ R.smoothStructure.val)
    (j : C → M) (hj : IsSmoothMap S T j)
    (e : ModelChart 2 b M) (he : e ∈ T.smoothStructure.val) (c : Plane) :
    ∃ Q : SmoothManifold n a (j ⁻¹' e.source),
      IsSmoothEmbedding Q S Subtype.val ∧
      IsSmoothMap Q R
        (fun p (_ : Fin 1) => ‖coordinates e (j p.val) - c‖ ^ 2) := by
  have hjc : Continuous j := continuous_iff_continuousAt.mpr (fun p => (hj p).1)
  obtain ⟨Q, _, hQA, hQ⟩ := SmoothManifolds.exists_openSubset_smoothManifold S
    (j ⁻¹' e.source) (e.open_source.preimage hjc)
  have hQE := (SmoothManifolds.TransversePreimage.open_subset_embedded_of_atlas_eq S
    (j ⁻¹' e.source) (e.open_source.preimage hjc) Q hQA).1
  refine ⟨Q, hQE, ?_⟩
  have hcomp : IsSmoothMap Q T (fun p : j ⁻¹' e.source => j p.val) :=
    SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
      S.smoothStructure.property.1.1 Subtype.val j hQ hj
  exact squaredRadius_smooth Q T R hR (fun p => j p.val) hcomp e he
    (fun p => p.property) c

/-- The finite Sard selection actually selects a positive radius inside the
original two bounds, in the squared-radius convention used by the source. -/
theorem exists_common_regular_radius_avoiding_squares {ι : Type*} [Finite ι]
    (R : SmoothManifold 1 .euclidean (Euclidean 1))
    (m : ι → ℕ) (a : ι → ModelKind) (C : ι → Type u)
    [∀ i, TopologicalSpace (C i)]
    (S : ∀ i, SmoothManifold (m i) (a i) (C i))
    (f : ∀ i, C i → Euclidean 1) (hf : ∀ i, IsSmoothMap (S i) R (f i))
    {F : Set ℝ} (hF : F.Finite) {l u : ℝ} (hl : 0 < l) (hlu : l < u) :
    ∃ r ∈ Ioo l u, r ^ 2 ∉ F ∧
      ∀ i, SmoothManifolds.MapClassData.IsRegularValue (S i) R (f i)
        (fun _ : Fin 1 => r ^ 2) := by
  let O : Set (Euclidean 1) := {y | l ^ 2 < y 0 ∧ y 0 < u ^ 2}
  have hO : IsOpen O := isOpen_Ioo.preimage (continuous_apply (0 : Fin 1))
  have hne : O.Nonempty := by
    refine ⟨fun _ => (l ^ 2 + u ^ 2) / 2, ?_⟩
    change l ^ 2 < (l ^ 2 + u ^ 2) / 2 ∧ (l ^ 2 + u ^ 2) / 2 < u ^ 2
    constructor <;> nlinarith
  obtain ⟨y, hy, hyF, hyreg⟩ :=
    P202.SurfaceRegionConstruction.RadiusSelection.exists_common_regular_value
      R (by norm_num) m a C S f hf
      (hF.image (fun s (_ : Fin 1) => s)) hO hne
  have hypos : 0 < y 0 := lt_trans (sq_pos_of_pos hl) hy.1
  let r := Real.sqrt (y 0)
  have hrsq : r ^ 2 = y 0 := Real.sq_sqrt hypos.le
  have hrnonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hry : (fun _ : Fin 1 => r ^ 2) = y := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using hrsq
  refine ⟨r, ⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [hy.1]
  · nlinarith [hy.2]
  · intro hrF
    exact hyF ⟨r ^ 2, hrF, hry⟩
  · simpa only [hry] using hyreg

/-- Compact regular fibers of maps between boundaryless curves are finite.
This uses the actual fiber topology supplied by P104 regular-level charts. -/
theorem finite_regular_fiber {a b : ModelKind}
    {C : Type u} {Y : Type v} [TopologicalSpace C] [TopologicalSpace Y]
    (S : SmoothManifold 1 a C) (T : SmoothManifold 1 b Y)
    (hS : SmoothManifolds.BoundaryData.intrinsicBoundary S = ∅)
    (hT : SmoothManifolds.BoundaryData.intrinsicBoundary T = ∅)
    (f : C → Y) (hf : IsSmoothMap S T f)
    (y : Y) (hy : SmoothManifolds.MapClassData.IsRegularValue S T f y)
    (hcompact : IsCompact (f ⁻¹' {y})) : (f ⁻¹' {y}).Finite := by
  obtain ⟨Q, _, _, _, _⟩ :=
    SmoothManifolds.RegularLevels.regular_fiber_structure S T f hS hT hf y hy
  have hdiscrete : DiscreteTopology (f ⁻¹' {y}) :=
    discreteTopology_iff_isOpen_singleton.mpr
      (SmoothManifolds.RegularLevels.zero_manifold_singleton_open Q)
  exact hcompact.finite (isDiscrete_iff_discreteTopology.mpr hdiscrete)

/-- The fiber image under the actual subtype inclusion is the complete curve
preimage of the selected chart circle. -/
theorem restricted_squaredRadius_fiber_image
    {C : Type u} {M : Type v} [TopologicalSpace C] [TopologicalSpace M]
    {A : Set (OpenPartialHomeomorph M Plane)} (d : ChartDisk M A)
    (j : C → M) {r : ℝ} (hr : 0 ≤ r) (houter : r ≤ d.outerRadius) :
    Subtype.val ''
      ((fun p : j ⁻¹' d.chart.source =>
        (fun _ : Fin 1 => ‖d.chart (j p.val) - d.center‖ ^ 2)) ⁻¹'
        {fun _ : Fin 1 => r ^ 2}) =
      j ⁻¹' P202Specs.SurfaceRegionConstruction.ChartDisk.circleAtRadius d r := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change j q.val ∈ d.chart.symm '' Metric.sphere d.center r
    refine ⟨d.chart (j q.val), ?_, d.chart.left_inv q.property⟩
    have hh : ‖d.chart (j q.val) - d.center‖ ^ 2 = r ^ 2 := congrFun hq 0
    exact Metric.mem_sphere.mpr (by
      rw [dist_eq_norm]
      exact (sq_eq_sq₀ (norm_nonneg _) hr).mp hh)
  · rintro ⟨z, hz, hjz⟩
    have hzt : z ∈ d.chart.target :=
      P202.SurfaceRegionConstruction.ChartDisk.closedBall_subset_target d houter
        (Metric.sphere_subset_closedBall hz)
    have hjs : j p ∈ d.chart.source := by
      rw [← hjz]
      exact d.chart.map_target hzt
    refine ⟨⟨p, hjs⟩, ?_, rfl⟩
    apply funext
    intro i
    change ‖d.chart (j p) - d.center‖ ^ 2 = r ^ 2
    rw [← hjz, d.chart.right_inv hzt]
    exact congrArg (fun s : ℝ => s ^ 2) (by
      simpa only [dist_eq_norm] using Metric.mem_sphere.mp hz)

/-- The actual squared-radius fiber in the open chart portion is compact,
because the selected circle stays inside the original chart target. -/
theorem isCompact_restricted_squaredRadius_fiber
    {C : Type u} {M : Type v} [TopologicalSpace C] [TopologicalSpace M]
    [CompactSpace C] [T2Space M]
    {A : Set (OpenPartialHomeomorph M Plane)} (d : ChartDisk M A)
    (j : C → M) (hj : Continuous j) {r : ℝ} (hr : 0 ≤ r)
    (houter : r ≤ d.outerRadius) :
    IsCompact
      ((fun p : j ⁻¹' d.chart.source =>
        (fun _ : Fin 1 => ‖d.chart (j p.val) - d.center‖ ^ 2)) ⁻¹'
        {fun _ : Fin 1 => r ^ 2}) := by
  have hc : IsCompact (ChartDisk.circleAtRadius d r) :=
    (isCompact_sphere d.center r).image_of_continuousOn
      (d.chart.symm.continuousOn.mono
        (Metric.sphere_subset_closedBall.trans
          (P202.SurfaceRegionConstruction.ChartDisk.closedBall_subset_target d houter)))
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  rw [restricted_squaredRadius_fiber_image d j hr houter]
  exact (hc.isClosed.preimage hj).isCompact

/-- Regularity of the actual smooth squared-radius map on the actual curve
portion gives finite circle preimage and finite geometric intersection. -/
theorem finite_chartCircle_preimage_of_regular
    {C : Type u} {M : Type v} [TopologicalSpace C] [TopologicalSpace M]
    [CompactSpace C] [T2Space M]
    {A : Set (OpenPartialHomeomorph M Plane)} (d : ChartDisk M A)
    (j : C → M) (hj : Continuous j)
    (Q : SmoothManifold 1 .euclidean (j ⁻¹' d.chart.source))
    (R : SmoothManifold 1 .euclidean (Euclidean 1))
    (hf : IsSmoothMap Q R
      (fun p (_ : Fin 1) => ‖d.chart (j p.val) - d.center‖ ^ 2))
    {r : ℝ} (hr : 0 ≤ r) (houter : r ≤ d.outerRadius)
    (hregular : SmoothManifolds.MapClassData.IsRegularValue Q R
      (fun p (_ : Fin 1) => ‖d.chart (j p.val) - d.center‖ ^ 2)
      (fun _ : Fin 1 => r ^ 2)) :
    (j ⁻¹' P202Specs.SurfaceRegionConstruction.ChartDisk.circleAtRadius d r).Finite ∧
      (range j ∩ P202Specs.SurfaceRegionConstruction.ChartDisk.circleAtRadius d r).Finite := by
  have hfinite := finite_regular_fiber Q R
    (SmoothManifolds.intrinsicBoundary_euclidean Q)
    (SmoothManifolds.intrinsicBoundary_euclidean R)
    (fun p (_ : Fin 1) => ‖d.chart (j p.val) - d.center‖ ^ 2) hf
    (fun _ : Fin 1 => r ^ 2) hregular
    (isCompact_restricted_squaredRadius_fiber d j hj hr houter)
  have hpre := hfinite.image (Subtype.val : (j ⁻¹' d.chart.source) → C)
  rw [restricted_squaredRadius_fiber_image d j hr houter] at hpre
  refine ⟨hpre, ?_⟩
  simpa only [image_preimage_eq_inter_range, inter_comm] using hpre.image j

/-- The complete regular-value selection on the actual chart portions of
finitely many smooth curves. Both the restricted source manifolds and the
standard real-line target manifold are constructed here. The finite forbidden
set consists of squared radii of earlier crossings. Turning regular values
into transverse geometric intersections is a separate differential step. -/
theorem exists_regular_radius_on_curve_portions {ι : Type*} [Finite ι]
    {kind : ModelKind} (T : SmoothManifold 2 kind X)
    (a : ι → ModelKind) (C : ι → Type v) [∀ i, TopologicalSpace (C i)]
    (S : ∀ i, SmoothManifold 1 (a i) (C i))
    (j : ∀ i, C i → X) (hj : ∀ i, IsSmoothMap (S i) T (j i))
    (e : ModelChart 2 kind X) (he : e ∈ T.smoothStructure.val) (c : Plane)
    {F : Set ℝ} (hF : F.Finite) {l r : ℝ} (hl : 0 < l) (hlr : l < r) :
    ∃ (R : SmoothManifold 1 .euclidean (Euclidean 1))
      (Q : ∀ i, SmoothManifold 1 (a i) ((j i) ⁻¹' e.source)) (ρ : ℝ),
      SmoothManifolds.euclideanChart 1 ∈ R.smoothStructure.val ∧
      ρ ∈ Ioo l r ∧ ρ ^ 2 ∉ F ∧
      (∀ i, IsSmoothEmbedding (Q i) (S i) Subtype.val) ∧
      (∀ i, IsSmoothMap (Q i) R
        (fun p (_ : Fin 1) => ‖coordinates e (j i p.val) - c‖ ^ 2)) ∧
      (∀ i, IsRegularValue (Q i) R
        (fun p (_ : Fin 1) => ‖coordinates e (j i p.val) - c‖ ^ 2)
        (fun _ : Fin 1 => ρ ^ 2)) := by
  obtain ⟨R, hR⟩ := SmoothManifolds.standardEuclidean_exists 1
  choose Q hQ hsquared using
    fun i => exists_restricted_squaredRadius (S i) T R hR (j i) (hj i) e he c
  obtain ⟨ρ, hρ, havoid, hregular⟩ := exists_common_regular_radius_avoiding_squares
    R (fun _ => 1) a (fun i => (j i) ⁻¹' e.source) Q
    (fun i p (_ : Fin 1) => ‖coordinates e (j i p.val) - c‖ ^ 2)
    hsquared hF hl hlr
  exact ⟨R, Q, ρ, hR, hρ, havoid, hQ, hsquared, hregular⟩

/-- A single recursive radius-selection step for actual compact boundaryless
curves. The forbidden set is a finite set of ambient crossing points. Smooth
restrictions and regular values are constructed, and the chosen geometric
circle both avoids those points and meets each supplied compact curve finitely.
Geometric transversality is still a separate differential bridge. -/
theorem exists_radius_avoiding_points_with_finite_intersections {ι : Type*} [Finite ι]
    (T : SmoothManifold 2 .euclidean X)
    (A : Set (OpenPartialHomeomorph X Plane)) (d : ChartDisk X A)
    (e : ModelChart 2 .euclidean X) (he : e ∈ T.smoothStructure.val)
    (hde : d.chart = euclideanChartToPlane e)
    (C : ι → Type v) [∀ i, TopologicalSpace (C i)] [∀ i, CompactSpace (C i)]
    (S : ∀ i, SmoothManifold 1 .euclidean (C i))
    (j : ∀ i, C i → X) (hj : ∀ i, IsSmoothMap (S i) T (j i))
    (P : Set X) (hP : P.Finite) :
    ∃ ρ ∈ Ioo d.innerRadius d.outerRadius,
      Disjoint (d.circleAtRadius ρ) P ∧
      (∀ i, ((range (j i)) ∩ d.circleAtRadius ρ).Finite) ∧
      ∃ (R : SmoothManifold 1 .euclidean (Euclidean 1))
        (Q : ∀ i, SmoothManifold 1 .euclidean ((j i) ⁻¹' d.chart.source)),
        SmoothManifolds.euclideanChart 1 ∈ R.smoothStructure.val ∧
        (∀ i, IsSmoothEmbedding (Q i) (S i) Subtype.val) ∧
        (∀ i, IsSmoothMap (Q i) R
          (fun p (_ : Fin 1) => ‖d.chart (j i p.val) - d.center‖ ^ 2)) ∧
        (∀ i, IsRegularValue (Q i) R
          (fun p (_ : Fin 1) => ‖d.chart (j i p.val) - d.center‖ ^ 2)
          (fun _ : Fin 1 => ρ ^ 2)) := by
  let : T2Space X := T.topologicalManifold.hausdorff
  let F : Set ℝ := (fun p => ‖d.chart p - d.center‖ ^ 2) '' P
  have hF : F.Finite := hP.image _
  obtain ⟨R, Q, ρ, hR, hρ, havoid, hQ, hsmooth, hregular⟩ :=
    exists_regular_radius_on_curve_portions T (fun _ => .euclidean) C S j hj
      e he d.center hF d.inner_pos d.inner_lt_outer
  have hsource : d.chart.source = e.source := by rw [hde]; rfl
  have hvalue : ∀ p, d.chart p = coordinates e p := by intro p; rw [hde]; rfl
  have hdata : ∀ i, ∃ Qd : SmoothManifold 1 .euclidean ((j i) ⁻¹' d.chart.source),
      IsSmoothEmbedding Qd (S i) Subtype.val ∧
      IsSmoothMap Qd R (fun p (_ : Fin 1) => ‖d.chart (j i p.val) - d.center‖ ^ 2) ∧
      IsRegularValue Qd R
        (fun p (_ : Fin 1) => ‖d.chart (j i p.val) - d.center‖ ^ 2)
        (fun _ : Fin 1 => ρ ^ 2) := by
    intro i
    rw [hsource]
    simp_rw [hvalue]
    exact ⟨Q i, hQ i, hsmooth i, hregular i⟩
  choose Qd hincld hsmoothd hregulard using hdata
  have hpos : 0 < ρ := d.inner_pos.trans hρ.1
  refine ⟨ρ, hρ, ?_, ?_, R, Qd, hR, hincld, hsmoothd, hregulard⟩
  · apply Set.disjoint_left.mpr
    intro x hx hxP
    obtain ⟨z, hz, hzx⟩ := hx
    have hzt : z ∈ d.chart.target :=
      P202.SurfaceRegionConstruction.ChartDisk.closedBall_subset_target d hρ.2.le
        (Metric.sphere_subset_closedBall hz)
    apply havoid
    refine ⟨x, hxP, ?_⟩
    change ‖d.chart x - d.center‖ ^ 2 = ρ ^ 2
    rw [← hzx, d.chart.right_inv hzt]
    exact congrArg (fun t : ℝ => t ^ 2) (by
      simpa only [dist_eq_norm] using Metric.mem_sphere.mp hz)
  · intro i
    exact (finite_chartCircle_preimage_of_regular d (j i)
      (continuous_iff_continuousAt.mpr (fun p => (hj i p).1))
      (Qd i) R (hsmoothd i) hpos.le hρ.2.le (hregulard i)).2

/-- Surjectivity of the derivative restricted to the first tangent forces
that tangent and the level-set tangent to span the ambient tangent. -/
theorem range_sup_ker_eq_top_of_surjective_comp {V W Z : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Z] [Module ℝ Z]
    (L : V →ₗ[ℝ] W) (G : W →ₗ[ℝ] Z)
    (h : Function.Surjective (G.comp L)) : LinearMap.range L ⊔ LinearMap.ker G = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨v, hv⟩ := h (G w)
  apply Submodule.mem_sup.mpr
  refine ⟨L v, ⟨v, rfl⟩, w - L v, ?_, add_sub_cancel _ _⟩
  change G (w - L v) = 0
  change G (L v) = G w at hv
  rw [map_sub, hv, sub_self]

/-- The regular-value-to-geometric-transversality bridge for an actual regular
fiber with its embedded subspace smooth structure. Both the source curve and
the level-set inclusion use their genuine intrinsic differentials. -/
theorem transverse_regular_fiber_of_regular_composite
    {m n k : ℕ} {a b c : ModelKind}
    {M N Y : Type u} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Y]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (E : SmoothManifold k c Y) (f : N → Y)
    (hT : SmoothManifolds.BoundaryData.intrinsicBoundary T = ∅)
    (hE : SmoothManifolds.BoundaryData.intrinsicBoundary E = ∅)
    (hf : IsSmoothMap T E f) (y : Y) (hy : IsRegularValue T E f y)
    (R : SmoothManifold (n - k) .euclidean (f ⁻¹' {y}))
    (hR : IsSmoothEmbedding R T Subtype.val)
    (j : M → N) (hj : IsSmoothMap S T j)
    (hregular : IsRegularValue S E (f ∘ j) y) :
    SmoothManifolds.TransversePreimageData.IsTransverse S T R j := by
  intro p hp L I hL hI
  obtain ⟨G, hG, _⟩ := SmoothManifolds.differential_exists T E f hf (j p)
  have hcomp : IsSmoothMap S E (f ∘ j) :=
    SmoothManifolds.manifoldContDiff_comp ⊤ _ _ _
      T.smoothStructure.property.1.1 j f hj hf
  have hGL := SmoothManifolds.differential_comp S T E j f hj hf p L G hL hG
  have hsurj : Function.Surjective (G.comp L) :=
    (SmoothManifolds.MapClasses.smooth_tangent_invariants S E (f ∘ j)
      hcomp p (G.comp L) hGL).2.2.mp (hregular p hp)
  have hker := (SmoothManifolds.RegularLevels.regular_fiber_tangent T E f
    hT hE hf y hy R hR ⟨j p, hp⟩ G I hG hI).2
  rw [hker]
  apply top_unique
  intro w _
  obtain ⟨v, hv⟩ := hsurj (G w)
  apply Submodule.mem_sup.mpr
  refine ⟨L v, ⟨v, rfl⟩, w + (-1 : ℝ) • L v, ?_, ?_⟩
  · change G (w + (-1 : ℝ) • L v) = 0
    change G (L v) = G w at hv
    rw [map_add, map_smul, hv]
    ext q
    change (G w).val q + (-1 : ℝ) * (G w).val q = 0
    ring
  · ext q
    change (L v).val q + (w.val q + (-1 : ℝ) * (L v).val q) = w.val q
    ring

end RadiusSelection


/-- The ordinary affine identification of a positive-radius circle with S¹. -/
def unitSphereAffineHomeomorph (c : Plane) (r : ℝ) (hr : 0 < r) :
    Metric.sphere (0 : Plane) 1 ≃ₜ Metric.sphere c r := by
  let h : Plane ≃ₜ Plane :=
    (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addRight c)
  apply h.subtype
  intro x
  change dist x 0 = 1 ↔ dist (r • x + c) c = r
  rw [dist_eq_norm, sub_zero, dist_eq_norm, add_sub_cancel_right,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  constructor
  · intro hx
    rw [hx, mul_one]
  · intro hx
    nlinarith

namespace ChartDisk
open P202Specs.SurfaceRegionConstruction.ChartDisk
variable {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A)

/-- Every permitted chart circle is the actual ordinary circle subspace. -/
def circleHomeomorph {r : ℝ} (hr : 0 < r) (houter : r ≤ d.outerRadius) :
    (d.circleAtRadius r) ≃ₜ Metric.sphere (0 : Plane) 1 :=
  (d.chart.symm.toPartialHomeomorph.homeomorphOfImageSubsetSource
    (Metric.sphere_subset_closedBall.trans (closedBall_subset_target d houter)) rfl).symm.trans
      (unitSphereAffineHomeomorph d.center r hr).symm

/-- Compactness concerns the ambient circle image, not an auxiliary topology. -/
theorem isCompact_circleAtRadius {r : ℝ} (houter : r ≤ d.outerRadius) :
    IsCompact (d.circleAtRadius r) :=
  (isCompact_sphere d.center r).image_of_continuousOn
    (d.chart.symm.continuousOn.mono
      (Metric.sphere_subset_closedBall.trans (closedBall_subset_target d houter)))

end ChartDisk

/-- The optional absent seam is represented by the actual empty subspace,
with a genuine boundaryless one-manifold structure and a smooth embedding. -/
def emptySmoothSeam (S : SmoothManifold 2 .euclidean X) : CompactSmoothSeam S := by
  letI : T2Space X := S.topologicalManifold.hausdorff
  letI : SecondCountableTopology X := S.topologicalManifold.secondCountable
  let E := (∅ : Set X)
  have hE : IsEmpty E := inferInstance
  have hatlas : IsContDiffAtlas ⊤ (∅ : Set (ModelChart 1 .euclidean E)) := by
    exact ⟨fun p => isEmptyElim p, fun _ h => False.elim h⟩
  have hmax : IsMaximalContDiffAtlas ⊤ (∅ : Set (ModelChart 1 .euclidean E)) := by
    refine ⟨hatlas, fun B _ _ => ?_⟩
    apply eq_empty_iff_forall_notMem.mpr
    intro e _
    exact isEmptyElim (e.symm ⟨0, mem_univ _⟩)
  let Q : SmoothManifold 1 .euclidean E := {
    topologicalManifold := ⟨inferInstance, inferInstance, ∅, hatlas.1⟩
    smoothStructure := ⟨∅, hmax⟩ }
  refine ⟨E, isCompact_empty, Q, ?_⟩
  refine ⟨fun p => isEmptyElim p, Subtype.val_injective, fun p => isEmptyElim p,
    Topology.IsEmbedding.subtypeVal.toHomeomorph, fun _ => rfl⟩

namespace TangentTransport
open SmoothManifolds.MapData SmoothManifolds.MapClassData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  SmoothManifolds.TransversePreimageData SmoothManifolds.TransversePreimage

/-- Push transverse tangent spaces through an equal-dimensional ambient
immersion. The submanifold map must identify its full tangent space as well. -/
theorem transverse_push_of_immersions {m n k : ℕ} {a b b' c c' : ModelKind}
    {M N Y : Type u} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Y]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (A : SmoothManifold n b' Y) {s : Set N} (R : SmoothManifold k c s)
    {t : Set Y} (C : SmoothManifold k c' t)
    (h : Y → N) (hmem : ∀ q : t, h q.val ∈ s) (f : M → Y)
    (hh : IsSmoothMap A T h) (hhi : IsImmersion A T h)
    (hj : IsSmoothMap C R (fun q => ⟨h q.val, hmem q⟩))
    (hji : IsImmersion C R (fun q => ⟨h q.val, hmem q⟩))
    (he : IsSmoothMap R T Subtype.val) (hc : IsSmoothMap C A Subtype.val)
    (hf : IsSmoothMap S A f)
    (hpre : ∀ p, h (f p) ∈ s → f p ∈ t)
    (ht : IsTransverse S A C f) : IsTransverse S T R (h ∘ f) := by
  intro p hp L G hL hG
  have hpt := hpre p hp
  let q : t := ⟨f p, hpt⟩
  let j : t → s := fun q => ⟨h q.val, hmem q⟩
  obtain ⟨F, hF, _⟩ := SmoothManifolds.differential_exists S A f hf p
  obtain ⟨H, hH, _⟩ := SmoothManifolds.differential_exists A T h hh (f p)
  obtain ⟨I, hI, _⟩ := SmoothManifolds.differential_exists C A Subtype.val hc q
  obtain ⟨J, hJ, _⟩ := SmoothManifolds.differential_exists C R j hj q
  have hHs := (same_dimension_immersion_differential_bijective A T h hh
    (f p) (hhi _) H hH).2
  have hJs := (same_dimension_immersion_differential_bijective C R j hj
    q (hji _) J hJ).2
  have hfs : IsSmoothMap S T (h ∘ f) := SmoothManifolds.manifoldContDiff_comp ⊤
    _ _ _ A.smoothStructure.property.1.1 f h hf hh
  obtain ⟨_, _, huniq⟩ := SmoothManifolds.differential_exists S T (h ∘ f) hfs p
  have hLF : L = H.comp F := (huniq _ hL).trans
    (huniq _ (SmoothManifolds.differential_comp S A T f h hf hh p F H hF hH)).symm
  have hcs : IsSmoothMap C T (h ∘ Subtype.val) :=
    SmoothManifolds.manifoldContDiff_comp ⊤ _ _ _
      A.smoothStructure.property.1.1 Subtype.val h hc hh
  obtain ⟨_, _, hu⟩ := SmoothManifolds.differential_exists C T (h ∘ Subtype.val) hcs q
  have hHI : H.comp I = G.comp J :=
    (hu _ (SmoothManifolds.differential_comp C A T Subtype.val h hc hh q I H hI hH)).trans
      (hu _ (SmoothManifolds.differential_comp C R T j Subtype.val hj he q J G hJ hG)).symm
  have hspan := congrArg (Submodule.map H) (ht p hpt F I hF hI)
  rw [Submodule.map_sup, ← LinearMap.range_comp, ← LinearMap.range_comp,
    hHI, LinearMap.range_comp J G, LinearMap.range_eq_top.mpr hJs,
    Submodule.map_top, Submodule.map_top, LinearMap.range_eq_top.mpr hHs] at hspan
  simpa only [hLF] using hspan

/-- Transversality on a same-dimensional open source restriction gives
transversality on the original source when all relevant points lie there. -/
theorem transverse_of_source_restriction {m n k : ℕ} {a a' b c : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    {s : Set N} (R : SmoothManifold k c s) (f : M → N)
    (V : Set M) (D : SmoothManifold m a' V)
    (hD : IsSmoothEmbedding D S Subtype.val) (hf : IsSmoothMap S T f)
    (hpre : f ⁻¹' s ⊆ V)
    (ht : IsTransverse D T R (f ∘ Subtype.val)) : IsTransverse S T R f := by
  intro p hp L I hL hI
  let q : V := ⟨p, hpre hp⟩
  obtain ⟨J, hJ, _⟩ := SmoothManifolds.differential_exists D S Subtype.val hD.1 q
  have hJs := (same_dimension_immersion_differential_bijective D S Subtype.val
    hD.1 q (hD.2.2.1 q) J hJ).2
  have hLJ := SmoothManifolds.differential_comp D S T Subtype.val f hD.1 hf q J L hJ hL
  have hspan := ht q hp (L.comp J) I hLJ hI
  rwa [LinearMap.range_comp, LinearMap.range_eq_top.mpr hJs, Submodule.map_top] at hspan

/-- The transversality predicate is symmetric for actual embedded subsets. -/
theorem transverse_symm {m n k : ℕ} {a b c : ModelKind}
    {N : Type u} [TopologicalSpace N] (T : SmoothManifold n b N)
    {s t : Set N} (S : SmoothManifold m a s) (R : SmoothManifold k c t)
    (ht : IsTransverse S T R Subtype.val) : IsTransverse R T S Subtype.val := by
  intro p hp L I hL hI
  exact (sup_comm _ _).trans (ht ⟨p.val, hp⟩ p.property I L hI hL)

end TangentTransport

namespace SmoothCircles
open SmoothManifolds.MapData SmoothManifolds.MapClassData
open SmoothManifolds.FiniteRegularityData

/-- The actual coordinate squared-radius derivative surjects onto the real
line at every positive radius. The codomain is P104's one-coordinate line. -/
theorem squaredRadius_derivative_surjective (c : Plane) (z : Euclidean 2)
    (h : toPlane z - c ≠ 0) :
    Function.Surjective
      (fderiv ℝ (fun v (_ : Fin 1) => ‖toPlane v - c‖ ^ 2) z) := by
  let w := toPlane z - c
  let L : Euclidean 2 →L[ℝ] Euclidean 1 := ContinuousLinearMap.pi
    (fun _ : Fin 1 => (2 • innerSL ℝ w).comp toPlane.toContinuousLinearMap)
  have hD : HasFDerivAt (fun v (_ : Fin 1) => ‖toPlane v - c‖ ^ 2) L z := by
    apply hasFDerivAt_pi.mpr
    intro i
    exact (toPlane.hasFDerivAt.sub_const c).norm_sq
  rw [hD.fderiv]
  intro y
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr h
  refine ⟨(y 0 / (2 * ‖w‖ ^ 2)) • toPlane.symm w, ?_⟩
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simp only [L, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearEquiv.coe_coe, toPlane.map_smul, ContinuousLinearEquiv.apply_symm_apply,
    innerSL_apply_apply, real_inner_smul_right, real_inner_self_eq_norm_sq, hi]
  field_simp [hn]
  ring

/-- The radius map on the actual open chart submanifold is regular at every
positive squared radius. No regularity certificate is added to the chart data. -/
theorem squaredRadius_regular_in_chart
    (S : SmoothManifold 2 .euclidean X)
    (e : ModelChart 2 .euclidean X) (he : e ∈ S.smoothStructure.val)
    (Q : SmoothManifold 2 .euclidean e.source)
    (hQ : Q.smoothStructure.val = SmoothManifolds.AtlasData.maximalExtension ⊤
      (SmoothManifolds.MapData.openSubsetAtlas S.smoothStructure.val e.source e.open_source))
    (R : SmoothManifold 1 .euclidean (Euclidean 1))
    (hR : SmoothManifolds.euclideanChart 1 ∈ R.smoothStructure.val)
    (c : Plane) {r : ℝ} (hr : 0 < r)
    (hf : IsSmoothMap Q R (fun p (_ : Fin 1) => ‖coordinates e p.val - c‖ ^ 2)) :
    IsRegularValue Q R (fun p (_ : Fin 1) => ‖coordinates e p.val - c‖ ^ 2)
      (fun _ : Fin 1 => r ^ 2) := by
  intro p hp
  let d := e.subtypeRestr (s := ⟨e.source, e.open_source⟩) ⟨p⟩
  have hd : d ∈ Q.smoothStructure.val := by
    rw [hQ]
    exact SmoothManifolds.subset_maximalExtension
      (SmoothManifolds.openSubsetAtlas_isContDiffAtlas ⊤ _
        S.smoothStructure.property.1 e.source e.open_source) ⟨⟨p⟩, e, he, rfl⟩
  have hpd : p ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using p.property
  let F : Euclidean 2 → Euclidean 1 := fun v (_ : Fin 1) => ‖toPlane v - c‖ ^ 2
  have hFd : DifferentiableAt ℝ F (d p).val := by
    apply differentiableAt_pi.mpr
    intro i
    exact (toPlane.differentiableAt.sub_const c).norm_sq (𝕜 := ℝ)
  have hJ : chartDerivative d (SmoothManifolds.euclideanChart 1)
      (fun p (_ : Fin 1) => ‖coordinates e p.val - c‖ ^ 2) p =
        fderiv ℝ F (d p).val := by
    apply SmoothManifolds.FiniteRegularity.coordinateDerivative_eq d _ p hpd
    exact ⟨F, hFd.hasFDerivAt, Filter.Eventually.of_forall (fun _ => rfl)⟩
  have hw : toPlane (d p).val - c ≠ 0 := by
    intro hw
    have hs := congrFun hp 0
    change ‖toPlane (d p).val - c‖ ^ 2 = r ^ 2 at hs
    rw [hw, norm_zero, zero_pow (by decide)] at hs
    nlinarith
  have hs := squaredRadius_derivative_surjective c (d p).val hw
  have hf1 := SmoothManifolds.manifoldContDiff_of_le ⊤ 1 _ _ _ (by simp) hf
  have hss := (congrArg (fun L : Euclidean 2 →L[ℝ] Euclidean 1 =>
    Function.Surjective L) hJ).mpr hs
  exact (SmoothManifolds.MapClasses.chart_invariants Q R _ hf1 p d
    (SmoothManifolds.euclideanChart 1) hd hR hpd (mem_univ _)).2.2.mpr hss

/-- Construct the actual smooth regular chart circle and its inclusion,
using a regular level set on the actual open chart submanifold. -/
theorem exists_smoothChartCircle
    (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A)
    (e : ModelChart 2 .euclidean X) (he : e ∈ S.smoothStructure.val)
    (hde : d.chart = euclideanChartToPlane e) {r : ℝ}
    (hr : 0 < r) (houter : r ≤ d.outerRadius) :
    Nonempty (SmoothChartCircle S d r) := by
  obtain ⟨Q, _, hQ, hj⟩ := SmoothManifolds.exists_openSubset_smoothManifold S
    e.source e.open_source
  have hQembed := (SmoothManifolds.TransversePreimage.open_subset_embedded_of_atlas_eq S
    e.source e.open_source Q hQ).1
  obtain ⟨R, hR⟩ := SmoothManifolds.standardEuclidean_exists 1
  let f : e.source → Euclidean 1 :=
    fun p (_ : Fin 1) => ‖coordinates e p.val - d.center‖ ^ 2
  have hf : IsSmoothMap Q R f := RadiusSelection.squaredRadius_smooth Q S R hR
    Subtype.val hj e he (fun p => p.property) d.center
  have hregular := squaredRadius_regular_in_chart S e he Q hQ R hR d.center hr hf
  obtain ⟨C, hC, _, _, _⟩ := SmoothManifolds.RegularLevels.regular_fiber_structure Q R f
    (SmoothManifolds.intrinsicBoundary_euclidean Q)
    (SmoothManifolds.intrinsicBoundary_euclidean R) hf (fun _ => r ^ 2) hregular
  have hsource : d.chart.source = e.source := by rw [hde]; rfl
  have hvalue : ∀ p, d.chart p = coordinates e p := by intro p; rw [hde]; rfl
  have hiff : ∀ p : e.source, f p = (fun _ => r ^ 2) ↔ p.val ∈ d.circleAtRadius r := by
    intro p
    constructor
    · intro hp
      refine ⟨d.chart p.val, ?_, d.chart.left_inv (hsource.symm ▸ p.property)⟩
      apply Metric.mem_sphere.mpr
      rw [dist_eq_norm, hvalue]
      exact (sq_eq_sq₀ (norm_nonneg _) hr.le).mp (congrFun hp 0)
    · rintro ⟨z, hz, hzp⟩
      have hzt := ChartDisk.closedBall_subset_target d houter (Metric.sphere_subset_closedBall hz)
      funext i
      change ‖coordinates e p.val - d.center‖ ^ 2 = r ^ 2
      rw [← hvalue, ← hzp, d.chart.right_inv hzt]
      exact congrArg (fun t : ℝ => t ^ 2) (by
        simpa only [dist_eq_norm] using Metric.mem_sphere.mp hz)
  have hcircle_source : d.circleAtRadius r ⊆ e.source := by
    rintro x ⟨z, hz, rfl⟩
    rw [← hsource]
    exact d.chart.map_target (ChartDisk.closedBall_subset_target d houter
      (Metric.sphere_subset_closedBall hz))
  let H : (f ⁻¹' {fun _ => r ^ 2}) ≃ₜ d.circleAtRadius r := {
    toFun := fun p => ⟨p.val.val, (hiff p.val).mp p.property⟩
    invFun := fun p => ⟨⟨p.val, hcircle_source p.property⟩,
      (hiff ⟨p.val, hcircle_source p.property⟩).mpr p.property⟩
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hcomp := SmoothManifolds.TransversePreimage.smoothEmbedding_comp C Q S
    Subtype.val Subtype.val hC hQembed
  obtain ⟨B, hB, _⟩ := SmoothManifolds.TransversePreimage.transport_embedded C S
    (fun p => p.val.val) hcomp H
  exact ⟨⟨B, hB, ChartDisk.circleHomeomorph d hr houter⟩⟩

/-- A regular value of the squared radius on a curve's actual open chart
portion makes that curve transverse to any smooth embedded structure on the
actual new chart circle. Transport uses the full inclusion differentials. -/
theorem transverse_chartCircle_of_regular
    (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A)
    (e : ModelChart 2 .euclidean X) (he : e ∈ S.smoothStructure.val)
    (hde : d.chart = euclideanChartToPlane e)
    {C : Type u} [TopologicalSpace C] (T : SmoothManifold 1 .euclidean C)
    (j : C → X) (hj : IsSmoothMap T S j)
    (Q : SmoothManifold 1 .euclidean (j ⁻¹' d.chart.source))
    (hQ : IsSmoothEmbedding Q T Subtype.val)
    (R : SmoothManifold 1 .euclidean (Euclidean 1))
    (hR : SmoothManifolds.euclideanChart 1 ∈ R.smoothStructure.val)
    (hf : IsSmoothMap Q R
      (fun p (_ : Fin 1) => ‖d.chart (j p.val) - d.center‖ ^ 2))
    {r : ℝ} (hr : 0 < r) (houter : r ≤ d.outerRadius)
    (hregular : IsRegularValue Q R
      (fun p (_ : Fin 1) => ‖d.chart (j p.val) - d.center‖ ^ 2)
      (fun _ : Fin 1 => r ^ 2))
    (B : SmoothChartCircle S d r) :
    SmoothManifolds.TransversePreimageData.IsTransverse T S B.manifold j := by
  have hsource : d.chart.source = e.source := by rw [hde]; rfl
  have hvalue : ∀ p, d.chart p = coordinates e p := by intro p; rw [hde]; rfl
  let f : d.chart.source → Euclidean 1 :=
    fun p (_ : Fin 1) => ‖d.chart p.val - d.center‖ ^ 2
  let y : Euclidean 1 := fun _ => r ^ 2
  have hdata : ∃ U : SmoothManifold 2 .euclidean d.chart.source,
      IsSmoothEmbedding U S Subtype.val ∧ IsSmoothMap U R f ∧
      IsRegularValue U R f y := by
    dsimp only [f, y]
    rw [hsource]
    simp_rw [hvalue]
    obtain ⟨U, _, hU, hi⟩ := SmoothManifolds.exists_openSubset_smoothManifold S
      e.source e.open_source
    have hUE := (SmoothManifolds.TransversePreimage.open_subset_embedded_of_atlas_eq
      S e.source e.open_source U hU).1
    have hfs := RadiusSelection.squaredRadius_smooth U S R hR Subtype.val hi
      e he (fun p => p.property) d.center
    exact ⟨U, hUE, hfs, squaredRadius_regular_in_chart S e he U hU R hR d.center hr hfs⟩
  obtain ⟨U, hU, hfu, hregularU⟩ := hdata
  have hiff : ∀ p : d.chart.source, f p = y ↔ p.val ∈ d.circleAtRadius r := by
    intro p
    constructor
    · intro hp
      refine ⟨d.chart p.val, ?_, d.chart.left_inv p.property⟩
      apply Metric.mem_sphere.mpr
      rw [dist_eq_norm]
      exact (sq_eq_sq₀ (norm_nonneg _) hr.le).mp (congrFun hp 0)
    · rintro ⟨z, hz, hzp⟩
      funext i
      change ‖d.chart p.val - d.center‖ ^ 2 = r ^ 2
      rw [← hzp, d.chart.right_inv (ChartDisk.closedBall_subset_target d houter
        (Metric.sphere_subset_closedBall hz))]
      exact congrArg (fun t : ℝ => t ^ 2) (by
        simpa only [dist_eq_norm] using Metric.mem_sphere.mp hz)
  have hcircle_source : d.circleAtRadius r ⊆ d.chart.source := by
    rintro x ⟨z, hz, rfl⟩
    exact d.chart.map_target (ChartDisk.closedBall_subset_target d houter
      (Metric.sphere_subset_closedBall hz))
  obtain ⟨E, η, _⟩ := SmoothManifolds.TransversePreimage.exists_manifold_diffeomorph R
    (Homeomorph.ulift : ULift.{u} (Euclidean 1) ≃ₜ Euclidean 1).symm
  let g : d.chart.source → ULift.{u} (Euclidean 1) := η.toEquiv ∘ f
  let z : ULift.{u} (Euclidean 1) := η.toEquiv y
  have hg : IsSmoothMap U E g := SmoothManifolds.manifoldContDiff_comp ⊤ _ _ _
    R.smoothStructure.property.1.1 f η.toEquiv hfu η.contDiff_toFun
  have hregularG : IsRegularValue U E g z :=
    SmoothManifolds.TransversePreimage.regularValue_postcomp_diffeomorph
      U R E η f hfu y hregularU
  have hgiff : ∀ p : d.chart.source, g p = z ↔ p.val ∈ d.circleAtRadius r :=
    fun p => η.toEquiv.injective.eq_iff.trans (hiff p)
  obtain ⟨D, hD, _, _, _⟩ := SmoothManifolds.RegularLevels.regular_fiber_structure U E g
    (SmoothManifolds.intrinsicBoundary_euclidean U)
    (SmoothManifolds.intrinsicBoundary_euclidean E) hg z hregularG
  have hDS := SmoothManifolds.TransversePreimage.smoothEmbedding_comp D U S
    Subtype.val Subtype.val hD hU
  let F : (g ⁻¹' {z}) → d.circleAtRadius r :=
    fun p => ⟨p.val.val, (hgiff p.val).mp p.property⟩
  have hF : IsSmoothEmbedding D B.manifold F :=
    SmoothManifolds.TransversePreimage.embedding_into_subspace D S (d.circleAtRadius r)
      B.manifold B.embedding F (by fun_prop) hDS
  let J : (j ⁻¹' d.chart.source) → d.chart.source := fun p => ⟨j p.val, p.property⟩
  have hJ : IsSmoothMap Q U J :=
    SmoothManifolds.TransversePreimage.smooth_restriction T S j hj
      d.chart.source U hU Q hQ
  have hregularJ : IsRegularValue Q E (g ∘ J) z :=
    SmoothManifolds.TransversePreimage.regularValue_postcomp_diffeomorph Q R E η
      (f ∘ J) hf y hregular
  have htrans := RadiusSelection.transverse_regular_fiber_of_regular_composite Q U E g
    (SmoothManifolds.intrinsicBoundary_euclidean U)
    (SmoothManifolds.intrinsicBoundary_euclidean E) hg z hregularG D hD J hJ hregularJ
  have hpush := TangentTransport.transverse_push_of_immersions Q S U B.manifold D
    Subtype.val (fun p => (hgiff p.val).mp p.property) J hU.1 hU.2.2.1
    hF.1 hF.2.2.1 B.embedding.1 hD.1 hJ
    (fun p hp => (hgiff (J p)).mpr hp) htrans
  exact TangentTransport.transverse_of_source_restriction T S B.manifold j
    (j ⁻¹' d.chart.source) Q hQ hj (fun _ hp => hcircle_source hp) hpush


/-- Choose one new smooth embedded chart circle, transverse to every supplied
compact smooth curve and avoiding every prescribed finite crossing point. -/
theorem exists_transverse_chartCircle {ι : Type*} [Finite ι]
    (T : SmoothManifold 2 .euclidean X)
    (A : Set (OpenPartialHomeomorph X Plane)) (d : ChartDisk X A)
    (e : ModelChart 2 .euclidean X) (he : e ∈ T.smoothStructure.val)
    (hde : d.chart = euclideanChartToPlane e)
    (C : ι → Type u) [∀ i, TopologicalSpace (C i)] [∀ i, CompactSpace (C i)]
    (S : ∀ i, SmoothManifold 1 .euclidean (C i))
    (j : ∀ i, C i → X) (hj : ∀ i, IsSmoothMap (S i) T (j i))
    (P : Set X) (hP : P.Finite) :
    ∃ ρ ∈ Ioo d.innerRadius d.outerRadius,
      ∃ B : SmoothChartCircle T d ρ,
        Disjoint (d.circleAtRadius ρ) P ∧
        (∀ i, (range (j i) ∩ d.circleAtRadius ρ).Finite) ∧
        (∀ i, SmoothManifolds.TransversePreimageData.IsTransverse
          (S i) T B.manifold (j i)) := by
  obtain ⟨ρ, hρ, havoid, hfinite, R, Q, hR, hQ, hf, hregular⟩ :=
    RadiusSelection.exists_radius_avoiding_points_with_finite_intersections T A d e he hde
      C S j hj P hP
  have hpos : 0 < ρ := d.inner_pos.trans hρ.1
  obtain ⟨B⟩ := exists_smoothChartCircle T d e he hde hpos hρ.2.le
  refine ⟨ρ, hρ, B, havoid, hfinite, fun i => ?_⟩
  exact transverse_chartCircle_of_regular T d e he hde (S i) (j i) (hj i)
    (Q i) (hQ i) R hR (hf i) hpos hρ.2.le (hregular i) B

end SmoothCircles

open SmoothManifolds.MapData SmoothManifolds.SliceData

/-- Same-model compatibility with a maximal smooth atlas is actual membership. -/
theorem compatibleChart_mem {n : ℕ} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n .euclidean X) (c : ModelChart n .euclidean X)
    (hc : CompatibleChart S c) : c ∈ S.smoothStructure.val := by
  have hmax : maximalExtension (⊤ : ℕ∞) S.smoothStructure.val =
      S.smoothStructure.val :=
    S.smoothStructure.property.2 _
      (SmoothManifolds.maximalExtension_isContDiffAtlas S.smoothStructure.property.1)
      (SmoothManifolds.subset_maximalExtension S.smoothStructure.property.1)
  rw [← hmax]
  intro d hd
  apply SmoothManifolds.contDiffCompatible_of_germs
  · intro x hx hxd
    exact (hc d hd x hx hxd).1
  · intro x hx hxc
    exact (hc d hd x hxc hx).2

/-- Compose an actual smooth chart with a Euclidean local diffeomorphism;
the result belongs to the original maximal smooth atlas. -/
theorem euclidean_changeChart_mem {n : ℕ} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n .euclidean X)
    (e : ModelChart n .euclidean X) (he : e ∈ S.smoothStructure.val)
    (j : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hj : ContDiffOn ℝ (⊤ : ℕ∞) j j.source)
    (hji : ContDiffOn ℝ (⊤ : ℕ∞) j.symm j.target) :
    ∃ c : ModelChart n .euclidean X,
      c ∈ S.smoothStructure.val ∧
      c.source = e.source ∩ (fun x => (e x).val) ⁻¹' j.source ∧
      (∀ x, (c x).val = j (e x).val) := by
  let h : ModelSpace n .euclidean ≃ₜ Euclidean n := Homeomorph.Set.univ _
  let c : ModelChart n .euclidean X :=
    ((e.transHomeomorph h).trans j).transHomeomorph h.symm
  have hcs : c.source = e.source ∩ (fun x => (e x).val) ⁻¹' j.source := by
    rfl
  have hcf : ∀ x, (c x).val = j (e x).val := by
    intro x
    rfl
  refine ⟨c, ?_, hcs, hcf⟩
  apply compatibleChart_mem S c
  apply SmoothManifolds.BoundaryRegularLevels.compatibleChart_of_model_change S e he c j hj hji
  · rw [hcs]
    exact inter_subset_left
  · intro x hx
    rw [hcs] at hx
    exact ⟨hx.2, hcf x⟩

/-- Local coordinate realization of a genuine smooth map with invertible
derivative. All coordinate functions, and their signs, remain exactly equal
to the supplied map on the resulting chart source. -/
theorem exists_smooth_coordinateChart {n : ℕ} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n .euclidean X)
    (e : ModelChart n .euclidean X) (he : e ∈ S.smoothStructure.val)
    (p : X) (hp : p ∈ e.source)
    (f : Euclidean n → Euclidean n) (U : Set (Euclidean n)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hpU : (e p).val ∈ U)
    (L : Euclidean n →L[ℝ] Euclidean n)
    (hL : HasFDerivAt f L (e p).val) (hbij : Function.Bijective L) :
    ∃ c : ModelChart n .euclidean X,
      c ∈ S.smoothStructure.val ∧ p ∈ c.source ∧ c.source ⊆ e.source ∧
      (∀ x ∈ c.source, (e x).val ∈ U) ∧
      (∀ x, (c x).val = f (e x).val) := by
  obtain ⟨j₀, hpj₀, hj₀, hji₀⟩ :=
    SmoothManifolds.InteriorInverse.euclidean_inverse (⊤ : ℕ∞) (by simp)
      f U hU hf (e p).val hpU L hL hbij
  let j := j₀.restrOpen U hU
  have hpj : (e p).val ∈ j.source := ⟨hpj₀, hpU⟩
  have hj : ContDiffOn ℝ (⊤ : ℕ∞) j j.source := by
    have hjf : (j : Euclidean n → Euclidean n) = f := hj₀
    rw [hjf]
    exact hf.mono inter_subset_right
  have hji : ContDiffOn ℝ (⊤ : ℕ∞) j.symm j.target :=
    hji₀.mono inter_subset_left
  obtain ⟨c, hc, hcs, hcf⟩ := euclidean_changeChart_mem S e he j hj hji
  refine ⟨c, hc, ?_, ?_, ?_, ?_⟩
  · rw [hcs]
    exact ⟨hp, hpj⟩
  · rw [hcs]
    exact inter_subset_left
  · intro x hx
    rw [hcs] at hx
    exact hx.2.2
  · intro x
    rw [hcf]
    exact congrFun hj₀ _

/-- A centered chart admits a whole coordinate ball inside any prescribed
open neighborhood of its center. The radius uses the canonical L² plane. -/
theorem exists_centeredChart_ball {X : Type u} [TopologicalSpace X]
    (e : ModelChart 2 .euclidean X) (p : X) (hp : p ∈ e.source)
    (hcenter : coordinates e p = 0) (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ z : ModelSpace 2 .euclidean,
        toPlane z.val ∈ Metric.ball (0 : Plane) ρ → z ∈ e.target) ∧
      e.source ∩ coordinates e ⁻¹' Metric.ball (0 : Plane) ρ ⊆ O := by
  let c := euclideanChartToPlane e
  have hpc : p ∈ c.source := hp
  have hczero : c p = 0 := hcenter
  have hOpen : IsOpen (c '' (c.source ∩ O)) := c.isOpen_image_source_inter hO
  have hzero : (0 : Plane) ∈ c '' (c.source ∩ O) := by
    rw [← hczero]
    exact ⟨p, ⟨hpc, hpO⟩, rfl⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hOpen 0 hzero
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, heq⟩ := hball hz
    have he : e x = z := by
      apply Subtype.ext
      apply toPlane.injective
      exact heq
    rw [← he]
    exact e.map_source hx.1
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hball hx.2
    have hxy : y = x := c.injOn hy.1 hx.1 hyx
    exact hxy ▸ hy.2

/-- Complementary kernels of two surjective maps give a surjective paired
map. This is the differential independence step for transverse defining
submersions; it does not rely on a dimension count. -/
theorem prod_surjective_of_ker_sup_eq_top {V W Z : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Z] [Module ℝ Z]
    (f : V →ₗ[ℝ] W) (g : V →ₗ[ℝ] Z)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : LinearMap.ker f ⊔ LinearMap.ker g = ⊤) :
    Function.Surjective (f.prod g) := by
  rintro ⟨w, z⟩
  obtain ⟨x, hx⟩ := hf w
  obtain ⟨y, hy⟩ := hg z
  have hxt : x ∈ LinearMap.ker f ⊔ LinearMap.ker g := hker.symm ▸ Submodule.mem_top
  have hyt : y ∈ LinearMap.ker f ⊔ LinearMap.ker g := hker.symm ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxt
  obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hyt
  change f a = 0 at ha
  change g b = 0 at hb
  change f c = 0 at hc
  change g d = 0 at hd
  refine ⟨b + c, ?_⟩
  apply Prod.ext
  · change f (b + c) = w
    rw [map_add, hc, add_zero, ← hx, ← hab, map_add, ha, zero_add]
  · change g (b + c) = z
    rw [map_add, hb, zero_add, ← hy, ← hcd, map_add, hd, add_zero]

/-- Two smooth defining submersions with transverse kernels are exactly the
two coordinates of an actual original-atlas chart. In particular both zero
sets and both strict sublevel sets are preserved without any sign choices. -/
theorem exists_two_defining_coordinateChart {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold 2 .euclidean X)
    (e : ModelChart 2 .euclidean X) (he : e ∈ S.smoothStructure.val)
    (p : X) (hp : p ∈ e.source)
    (f g : Euclidean 2 → ℝ) (U : Set (Euclidean 2)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hpU : (e p).val ∈ U)
    (L M : Euclidean 2 →L[ℝ] ℝ)
    (hL : HasFDerivAt f L (e p).val) (hM : HasFDerivAt g M (e p).val)
    (hLs : Function.Surjective L) (hMs : Function.Surjective M)
    (hker : LinearMap.ker L.toLinearMap ⊔ LinearMap.ker M.toLinearMap = ⊤) :
    ∃ c : ModelChart 2 .euclidean X,
      c ∈ S.smoothStructure.val ∧ p ∈ c.source ∧ c.source ⊆ e.source ∧
      (∀ x ∈ c.source, (e x).val ∈ U) ∧
      (∀ x, (c x).val 0 = f (e x).val ∧ (c x).val 1 = g (e x).val) := by
  let E := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  let F : Euclidean 2 → Euclidean 2 := fun z => E (f z, g z)
  let D : Euclidean 2 →L[ℝ] Euclidean 2 := E.toContinuousLinearMap.comp (L.prod M)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F U := E.contDiff.comp_contDiffOn (hf.prodMk hg)
  have hD : HasFDerivAt F D (e p).val :=
    E.hasFDerivAt.comp _ (hL.prodMk hM)
  have hDs : Function.Surjective D :=
    E.surjective.comp (prod_surjective_of_ker_sup_eq_top L.toLinearMap M.toLinearMap
      hLs hMs hker)
  have hDb : Function.Bijective D :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hDs, hDs⟩
  obtain ⟨c, hc, hpc, hcsub, hcU, hcf⟩ :=
    exists_smooth_coordinateChart S e he p hp F U hU hF hpU D hD hDb
  refine ⟨c, hc, hpc, hcsub, hcU, ?_⟩
  intro x
  rw [hcf]
  exact ⟨rfl, rfl⟩

/-- A genuine surjective planar functional has a continuous linear
complement. The complement can be one of the original coordinate projections. -/
theorem exists_planar_linear_complement (L : Euclidean 2 →L[ℝ] ℝ)
    (hL : Function.Surjective L) :
    ∃ M : Euclidean 2 →L[ℝ] ℝ, Function.Surjective (L.prod M) := by
  have hv (z : Euclidean 2) : z = z 0 • ![1, 0] + z 1 • ![0, 1] := by
    ext i
    fin_cases i <;> simp
  have hrep (z : Euclidean 2) :
      L z = z 0 * L ![1, 0] + z 1 * L ![0, 1] := by
    calc
      L z = L (z 0 • ![1, 0] + z 1 • ![0, 1]) := congrArg L (hv z)
      _ = _ := by rw [map_add, map_smul, map_smul]; rfl
  by_cases h0 : L ![1, 0] = 0
  · have h1 : L ![0, 1] ≠ 0 := by
      intro h1
      obtain ⟨z, hz⟩ := hL 1
      rw [hrep, h0, h1, mul_zero, mul_zero, zero_add] at hz
      exact zero_ne_one hz
    refine ⟨ContinuousLinearMap.proj (0 : Fin 2), ?_⟩
    rintro ⟨s, t⟩
    refine ⟨![t, s / L ![0, 1]], ?_⟩
    apply Prod.ext
    · change L ![t, s / L ![0, 1]] = s
      rw [hrep]
      simp [h0, h1]
    · rfl
  · refine ⟨ContinuousLinearMap.proj (1 : Fin 2), ?_⟩
    rintro ⟨s, t⟩
    refine ⟨![(s - t * L ![0, 1]) / L ![1, 0], t], ?_⟩
    apply Prod.ext
    · change L ![(s - t * L ![0, 1]) / L ![1, 0], t] = s
      rw [hrep]
      simp [h0]
    · rfl

/-- At a regular zero of a smooth scalar defining function, that function
is exactly the first coordinate of a centered original-atlas chart. -/
theorem exists_one_defining_coordinateChart {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold 2 .euclidean X)
    (e : ModelChart 2 .euclidean X) (he : e ∈ S.smoothStructure.val)
    (p : X) (hp : p ∈ e.source)
    (f : Euclidean 2 → ℝ) (U : Set (Euclidean 2)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hpU : (e p).val ∈ U)
    (hzero : f (e p).val = 0)
    (L : Euclidean 2 →L[ℝ] ℝ)
    (hL : HasFDerivAt f L (e p).val) (hLs : Function.Surjective L) :
    ∃ c : ModelChart 2 .euclidean X,
      c ∈ S.smoothStructure.val ∧ p ∈ c.source ∧ c.source ⊆ e.source ∧
      (c p).val = 0 ∧
      (∀ x ∈ c.source, (e x).val ∈ U) ∧
      (∀ x, (c x).val 0 = f (e x).val) := by
  obtain ⟨M, hM⟩ := exists_planar_linear_complement L hLs
  let E := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  let g : Euclidean 2 → ℝ := fun z => M z - M (e p).val
  let F : Euclidean 2 → Euclidean 2 := fun z => E (f z, g z)
  let D : Euclidean 2 →L[ℝ] Euclidean 2 := E.toContinuousLinearMap.comp (L.prod M)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g U :=
    (M.contDiff.sub contDiff_const).contDiffOn
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F U := E.contDiff.comp_contDiffOn (hf.prodMk hg)
  have hD : HasFDerivAt F D (e p).val :=
    E.hasFDerivAt.comp _ (hL.prodMk (M.hasFDerivAt.sub_const _))
  have hDs : Function.Surjective D := E.surjective.comp hM
  have hDb : Function.Bijective D :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hDs, hDs⟩
  obtain ⟨c, hc, hpc, hcsub, hcU, hcf⟩ :=
    exists_smooth_coordinateChart S e he p hp F U hU hF hpU D hD hDb
  refine ⟨c, hc, hpc, hcsub, ?_, hcU, ?_⟩
  · rw [hcf]
    change E (f (e p).val, M (e p).val - M (e p).val) = 0
    simp [hzero]
  · intro x
    rw [hcf]
    rfl


namespace LocalGeometry
open Filter SmoothManifolds.MapData SmoothManifolds.FiniteRegularityData

/-- A nonzero straight coordinate line has a two-sided regular germ in every
chart of the given smooth atlas. -/
theorem exists_chart_line_germ (S : SmoothManifold 2 .euclidean X)
    (p : X) (c : ModelChart 2 .euclidean X)
    (hc : c ∈ S.smoothStructure.val) (hp : p ∈ c.source)
    (hcenter : coordinates c p = 0) (v : Plane) (hv : v ≠ 0) :
    ∃ (δ : ℝ) (g : ℝ → X), 0 < δ ∧ g 0 = p ∧
      (∀ t ∈ Ioo (-δ) δ, g t ∈ c.source ∧ coordinates c (g t) = t • v) ∧
      (∀ e ∈ S.smoothStructure.val, p ∈ e.source →
        ContDiffAt ℝ ∞ (fun t => coordinates e (g t)) 0 ∧
        deriv (fun t => coordinates e (g t)) 0 ≠ 0) := by
  let w : Euclidean 2 := toPlane.symm v
  let L : ℝ → Euclidean 2 := fun t => t • w
  let q : ℝ → ModelSpace 2 .euclidean := fun t => ⟨L t, mem_univ _⟩
  let g : ℝ → X := fun t => c.symm (q t)
  have hcp : (c p).val = 0 := by
    apply toPlane.injective
    simpa [coordinates] using hcenter
  have hq0 : q 0 = c p := by
    apply Subtype.ext
    simpa [q, L] using hcp.symm
  have hg0 : g 0 = p := by
    change c.symm (q 0) = p
    rw [hq0, c.left_inv hp]
  have hLc : Continuous L := continuous_id.smul continuous_const
  have hLs : ContDiff ℝ (∞) L := contDiff_id.smul contDiff_const
  have hLd : HasDerivAt L w 0 := by
    simpa [L] using (hasDerivAt_id (0 : ℝ)).smul_const w
  have hqc : Continuous q := hLc.subtype_mk _
  have hqt : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ c.target :=
    hqc.continuousAt.eventually (c.open_target.mem_nhds (by rw [hq0]; exact c.map_source hp))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.mp hqt
  have hline : ∀ t ∈ Ioo (-δ) δ, g t ∈ c.source ∧ coordinates c (g t) = t • v := by
    intro t ht
    have htq : q t ∈ c.target := hδsub (by
      rw [Real.dist_eq, sub_zero, abs_lt]
      exact ht)
    refine ⟨c.map_target htq, ?_⟩
    change toPlane (c (c.symm (q t))).val = t • v
    rw [c.right_inv htq]
    change toPlane (t • w) = t • v
    rw [toPlane.map_smul, ContinuousLinearEquiv.apply_symm_apply]
  have hgc : ContinuousAt g 0 :=
    (c.symm.continuousAt (by rw [hq0]; exact c.map_source hp)).comp hqc.continuousAt
  have hgt : Tendsto g (𝓝 0) (𝓝 p) := by simpa only [ContinuousAt, hg0] using hgc
  have hceq : (fun t => (c (g t)).val) =ᶠ[𝓝 0] L := by
    filter_upwards [hqt] with t ht
    change (c (c.symm (q t))).val = L t
    rw [c.right_inv ht]
  refine ⟨δ, g, hδ, hg0, hline, ?_⟩
  intro e he hpe
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 c hc e he) hp hpe
  have hF0 : ContDiffAt ℝ ∞ F 0 := by
    have hz : (0 : Euclidean 2) ∈ U := by simpa [hcp] using hpU
    exact hF.contDiffAt (hU.mem_nhds hz)
  have hFder : HasFDerivAt F (fderiv ℝ F 0) 0 :=
    (hF0.differentiableAt (by simp)).hasFDerivAt
  have hJ : chartDerivative c e id p = fderiv ℝ F 0 := by
    apply SmoothManifolds.FiniteRegularity.coordinateDerivative_eq c _ p hp
    exact ⟨F, by simpa [hcp] using hFder, hrep⟩
  have heeq : (fun t => coordinates e (g t)) =ᶠ[𝓝 0] (fun t => toPlane (F (L t))) := by
    filter_upwards [hrep.comp_tendsto hgt, hceq] with t ht hcgt
    change toPlane (e (g t)).val = toPlane (F (L t))
    change F (c (g t)).val = (e (g t)).val at ht
    rw [← ht, hcgt]
  have hF0L : ContDiffAt ℝ ∞ F (L 0) := by simpa [L] using hF0
  have hFL : ContDiffAt ℝ ∞ (fun t => toPlane (F (L t))) 0 :=
    toPlane.contDiff.contDiffAt.comp 0 (hF0L.comp 0 hLs.contDiffAt)
  have hDer : HasDerivAt (fun t => toPlane (F (L t)))
      (toPlane (fderiv ℝ F 0 w)) 0 := by
    have hFderL : HasFDerivAt F (fderiv ℝ F 0) (L 0) := by simpa [L] using hFder
    have hfL := hFderL.comp_hasDerivAt 0 hLd
    exact toPlane.hasFDerivAt.comp_hasDerivAt 0 hfL
  refine ⟨hFL.congr_of_eventuallyEq heeq, ?_⟩
  rw [(hDer.congr_of_eventuallyEq heeq).deriv]
  intro hzero
  have hz : fderiv ℝ F 0 w = 0 := by
    apply toPlane.injective
    simpa using hzero
  have hinj : Function.Injective (chartDerivative c e id p) :=
    (SmoothManifolds.FiniteRegularity.transitionLinearEquiv (⊤ : ℕ∞) (by simp)
      S.smoothStructure.val S.smoothStructure.property.1 p c e hc he hp hpe).injective
  have hw : w = 0 := hinj (by simpa [hJ] using hz)
  apply hv
  simpa [w] using congrArg toPlane hw


theorem axisTangent_apply (a b : Fin 2) :
    axisTangent a b = if b = a then 0 else 1 := rfl

theorem axisTangent_ne_zero (a : Fin 2) : axisTangent a ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_ne a
  intro hz
  have h := congrArg (fun v : Plane => v b) hz
  simp [axisTangent_apply, hb] at h

/-- Exact straight-axis equations imply full smooth regular endpoint germs.
The parameter interval can be shrunk inside any retained coordinate ball. -/
theorem endpoint_germ_of_axis (S : SmoothManifold 2 .euclidean X)
    (p : X) (c : ModelChart 2 .euclidean X)
    (hc : c ∈ S.smoothStructure.val) (hp : p ∈ c.source)
    (hcenter : coordinates c p = 0) (ρ : ℝ) (hρ : 0 < ρ)
    (C : Set X) (a : Fin 2)
    (hC : ∀ x, x ∈ c.source → coordinates c x ∈ Metric.ball 0 ρ →
      (x ∈ C ↔ coordinates c x a = 0)) :
    ∃ (δ : ℝ) (g : ℝ → X), 0 < δ ∧ g 0 = p ∧
      (∀ t ∈ Ioo (-δ) δ, g t ∈ c.source ∧ g t ∈ C ∧
        coordinates c (g t) = t • axisTangent a) ∧
      (∀ e ∈ S.smoothStructure.val, p ∈ e.source →
        ContDiffAt ℝ ∞ (fun t => coordinates e (g t)) 0 ∧
        deriv (fun t => coordinates e (g t)) 0 ≠ 0) := by
  obtain ⟨δ₀, g, hδ₀, hg, hline, hregular⟩ :=
    exists_chart_line_germ S p c hc hp hcenter (axisTangent a) (axisTangent_ne_zero a)
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), t • axisTangent a ∈ Metric.ball (0 : Plane) ρ :=
    (continuous_id.smul continuous_const).continuousAt.eventually
      (Metric.isOpen_ball.mem_nhds (by simpa using hρ))
  obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff.mp hsmall
  refine ⟨min δ₀ ε, g, lt_min hδ₀ hε, hg, ?_, hregular⟩
  intro t ht
  have ht₀ : t ∈ Ioo (-δ₀) δ₀ :=
    ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  obtain ⟨hts, htc⟩ := hline t ht₀
  have htε : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) ht.1,
      lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  refine ⟨hts, (hC _ hts (by rw [htc]; exact hεsub htε)).mpr ?_, htc⟩
  rw [htc]
  simp [axisTangent_apply]


/-- Membership in an open disk is locally constant away from its frontier. -/
theorem eventually_mem_iff_of_not_mem_frontier {U : Set X} (hU : IsOpen U)
    {p : X} (hp : p ∉ frontier U) :
    ∀ᶠ x in 𝓝 p, (x ∈ U ↔ p ∈ U) := by
  by_cases hpU : p ∈ U
  · filter_upwards [hU.mem_nhds hpU] with x hx
    exact iff_of_true hx hpU
  · have hpcl : p ∉ closure U := by
      intro h
      exact hp ⟨h, by simpa only [hU.interior_eq] using hpU⟩
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hpcl] with x hx
    exact iff_of_false (fun h => hx (subset_closure h)) hpU

/-- Before changing coordinates, one can remove every nonincident curve and
freeze every nonincident disk membership in an arbitrarily small neighborhood. -/
theorem exists_arrangement_neighborhood
    (S : SmoothManifold 2 .euclidean X) {n : ℕ}
    {A : Set (OpenPartialHomeomorph X Plane)}
    (B : CompactSmoothSeam S) (d : Fin n → ChartDisk X A) (r : Fin n → ℝ)
    (hpos : ∀ i, 0 < r i) (houter : ∀ i, r i ≤ (d i).outerRadius)
    (p : X) (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ N : Set X, IsOpen N ∧ p ∈ N ∧ N ⊆ O ∧
      (∀ i : Option (Fin n), p ∉ arrangementCurve B.carrier d r i →
        Disjoint N (arrangementCurve B.carrier d r i)) ∧
      (∀ i : Fin n, p ∉ (d i).circleAtRadius (r i) →
        ∀ x ∈ N, (x ∈ (d i).openAtRadius (r i) ↔ p ∈ (d i).openAtRadius (r i))) := by
  let : T2Space X := S.topologicalManifold.hausdorff
  have hclosed : ∀ i : Option (Fin n), IsClosed (arrangementCurve B.carrier d r i) := by
    intro i
    cases i with
    | none => exact B.compact.isClosed
    | some i => exact (ChartDisk.isCompact_circleAtRadius (d i) (houter i)).isClosed
  have hcurve : ∀ i : Option (Fin n),
      ∀ᶠ x in 𝓝 p, (p ∉ arrangementCurve B.carrier d r i →
        x ∉ arrangementCurve B.carrier d r i) := by
    intro i
    by_cases hp : p ∈ arrangementCurve B.carrier d r i
    · exact Eventually.of_forall (fun _ h => False.elim (h hp))
    · filter_upwards [(hclosed i).isOpen_compl.mem_nhds hp] with x hx
      exact fun _ => hx
  have hdisk : ∀ i : Fin n, ∀ᶠ x in 𝓝 p,
      p ∉ (d i).circleAtRadius (r i) →
        (x ∈ (d i).openAtRadius (r i) ↔ p ∈ (d i).openAtRadius (r i)) := by
    intro i
    by_cases hp : p ∈ (d i).circleAtRadius (r i)
    · exact Eventually.of_forall (fun _ h => False.elim (h hp))
    · have hpf : p ∉ frontier ((d i).openAtRadius (r i)) := by
        rwa [ChartDisk.frontier_openAtRadius (d i) (hpos i) (houter i)]
      filter_upwards [eventually_mem_iff_of_not_mem_frontier
        (ChartDisk.isOpen_openAtRadius (d i) (r i)) hpf] with x hx
      exact fun _ => hx
  have hboth : ∀ᶠ x in 𝓝 p,
      x ∈ O ∧
      (∀ i : Option (Fin n), p ∉ arrangementCurve B.carrier d r i →
        x ∉ arrangementCurve B.carrier d r i) ∧
      (∀ i : Fin n, p ∉ (d i).circleAtRadius (r i) →
        (x ∈ (d i).openAtRadius (r i) ↔ p ∈ (d i).openAtRadius (r i))) := by
    have hOm : ∀ᶠ x in 𝓝 p, x ∈ O := hO.mem_nhds hpO
    exact hOm.and ((eventually_all.mpr hcurve).and (eventually_all.mpr hdisk))
  obtain ⟨N, hNsub, hN, hpN⟩ := mem_nhds_iff.mp hboth
  refine ⟨N, hN, hpN, fun x hx => (hNsub hx).1, ?_, ?_⟩
  · intro i hp
    exact disjoint_left.mpr (fun x hx hxi => (hNsub hx).2.1 i hp hxi)
  · intro i hp x hx
    exact (hNsub hx).2.2 i hp


/-- Every point has a centered chart in the actual original maximal atlas. -/
theorem exists_centered_chart (S : SmoothManifold 2 .euclidean X) (p : X) :
    ∃ c : ModelChart 2 .euclidean X,
      c ∈ S.smoothStructure.val ∧ p ∈ c.source ∧ coordinates c p = 0 := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨c, hc, hpc, _, _, hcf⟩ := exists_smooth_coordinateChart S e he p hp
    (fun z => z - (e p).val) univ isOpen_univ (contDiff_id.sub contDiff_const).contDiffOn
    (mem_univ _) (ContinuousLinearMap.id ℝ (Euclidean 2))
    ((hasFDerivAt_id _).sub_const (e p).val) ⟨Function.injective_id, Function.surjective_id⟩
  refine ⟨c, hc, hpc, ?_⟩
  change toPlane (c p).val = 0
  rw [hcf, sub_self, map_zero]

/-- Away from the curves, the full arrangement normal form has no active
axis and every disk sign is constant throughout the retained coordinate ball. -/
theorem normalForm_of_no_incident
    (S : SmoothManifold 2 .euclidean X) {n : ℕ}
    {A : Set (OpenPartialHomeomorph X Plane)}
    (B : CompactSmoothSeam S) (d : Fin n → ChartDisk X A) (r : Fin n → ℝ)
    (hpos : ∀ i, 0 < r i) (houter : ∀ i, r i ≤ (d i).outerRadius)
    (p : X) (hno : ∀ i : Option (Fin n), p ∉ arrangementCurve B.carrier d r i)
    (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    Nonempty (ArrangementNormalForm S B.carrier d r p O) := by
  obtain ⟨N, hN, hpN, hNO, hmiss, hsign⟩ :=
    exists_arrangement_neighborhood S B d r hpos houter p O hO hpO
  obtain ⟨c, hc, hpc, hcenter⟩ := exists_centered_chart S p
  obtain ⟨ρ, hρ, hball, hsub⟩ := exists_centeredChart_ball c p hpc hcenter N hN hpN
  refine ⟨{
    chart := c
    chart_mem := hc
    mem_source := hpc
    centered := hcenter
    radius := ρ
    radius_pos := hρ
    ball_in_target := hball
    neighborhood_subset := hsub.trans hNO
    axis := fun _ => none
    axis_injective := ?_
    active_iff := ?_
    curve_eq := ?_
    disk_sign := ?_
    endpoint_germs := ?_ }⟩
  · intro i j a hi
    cases hi
  · intro i
    exact iff_of_false (fun h => h rfl) (hno i)
  · intro i x hx hxc
    have hxN : x ∈ N := hsub ⟨hx, hxc⟩
    have hxC : x ∉ arrangementCurve B.carrier d r i :=
      fun h => Set.disjoint_left.mp (hmiss i (hno i)) hxN h
    constructor
    · intro h
      exact (hxC h).elim
    · rintro ⟨a, ha, _⟩
      cases ha
  · intro i x hx hxc
    exact hsign i (hno (some i)) x (hsub ⟨hx, hxc⟩)
  · intro i a hi
    cases hi


end LocalGeometry

namespace FiniteArrangement
open SmoothManifolds.MapClassData
variable {X : Type u} [TopologicalSpace X]

/-- All ambient pair crossings of a finite curve family. -/
def crossings {ι : Type*} (C : ι → Set X) : Set X :=
  by classical exact ⋃ i, ⋃ j, if i = j then ∅ else C i ∩ C j

omit [TopologicalSpace X] in
lemma finite_crossings {ι : Type*} [Finite ι] (C : ι → Set X)
    (hC : ∀ i j, i ≠ j → (C i ∩ C j).Finite) : (crossings C).Finite := by
  classical
  unfold crossings
  apply Set.finite_iUnion
  intro i
  apply Set.finite_iUnion
  intro j
  split_ifs with hij
  · exact Set.finite_empty
  · exact hC i j hij

omit [TopologicalSpace X] in
lemma mem_crossings {ι : Type*} {C : ι → Set X} {i j : ι} (hij : i ≠ j)
    {x : X} (hi : x ∈ C i) (hj : x ∈ C j) : x ∈ crossings C := by
  classical
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, by simp [hij, hi, hj]⟩⟩

omit [TopologicalSpace X] in
/-- A purely set-theoretic extension step for the no-triple invariant. -/
lemma no_triple_option {ι : Type*} (C : ι → Set X) (N : Set X)
    (hC : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → C i ∩ C j ∩ C k = ∅)
    (hN : Disjoint N (crossings C)) :
    ∀ i j k : Option ι, i ≠ j → i ≠ k → j ≠ k →
      (i.elim N C) ∩ (j.elim N C) ∩ (k.elim N C) = ∅ := by
  intro i j k hij hik hjk
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨⟨hxi, hxj⟩, hxk⟩
  cases i with
  | none =>
    cases j with
    | none => exact hij rfl
    | some j =>
      cases k with
      | none => exact hik rfl
      | some k =>
        exact Set.disjoint_left.mp hN hxi
          (mem_crossings (fun h => hjk (congrArg some h)) hxj hxk)
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact hjk rfl
      | some k =>
        exact Set.disjoint_left.mp hN hxj
          (mem_crossings (fun h => hik (congrArg some h)) hxi hxk)
    | some j =>
      cases k with
      | none =>
        exact Set.disjoint_left.mp hN hxk
          (mem_crossings (fun h => hij (congrArg some h)) hxi hxj)
      | some k =>
        have hx : x ∈ C i ∩ C j ∩ C k := ⟨⟨hxi, hxj⟩, hxk⟩
        rw [hC i j k (fun h => hij (congrArg some h))
          (fun h => hik (congrArg some h)) (fun h => hjk (congrArg some h))] at hx
        exact hx

/-- Insert the new first circle while keeping the seam as `none`. -/
def insertIndex {n : ℕ} : Option (Fin (n+1)) → Option (Option (Fin n))
  | none => some none
  | some i => Fin.cases none (fun j => some (some j)) i

lemma insertIndex_injective {n : ℕ} : Function.Injective (@insertIndex n) := by
  intro i j
  cases i with
  | none =>
    cases j with
    | none => intro _; rfl
    | some j =>
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [insertIndex]
  | some i =>
    cases j with
    | none =>
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [insertIndex]
    | some j =>
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j <;> simp [insertIndex]
      · refine Fin.cases ?_ (fun j => ?_) j <;> simp [insertIndex]

structure Data (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (B : CompactSmoothSeam S)
    {n : ℕ} (d : Fin n → ChartDisk X A) where
  radius : Fin n → ℝ
  bounds : ∀ i, radius i ∈ Ioo (d i).innerRadius (d i).outerRadius
  circle : ∀ i, SmoothChartCircle S (d i) (radius i)
  transverse_pairs : ∀ i j, i ≠ j →
    SmoothManifolds.TransversePreimageData.IsTransverse
      (circle i).manifold S (circle j).manifold Subtype.val
  transverse_seam : ∀ i, SmoothManifolds.TransversePreimageData.IsTransverse
    (circle i).manifold S B.manifold Subtype.val
  finite_pairs : ∀ i j, i ≠ j →
    ((d i).circleAtRadius (radius i) ∩ (d j).circleAtRadius (radius j)).Finite
  finite_seam : ∀ i, ((d i).circleAtRadius (radius i) ∩ B.carrier).Finite
  no_triple : ∀ i j k : Option (Fin n), i ≠ j → i ≠ k → j ≠ k →
    arrangementCurve B.carrier d radius i ∩ arrangementCurve B.carrier d radius j ∩
      arrangementCurve B.carrier d radius k = ∅

lemma curve_compact (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (B : CompactSmoothSeam S)
    {n : ℕ} {d : Fin n → ChartDisk X A} (D : Data S B d) (i : Option (Fin n)) :
    IsCompact (arrangementCurve B.carrier d D.radius i) := by
  cases i with
  | none => exact B.compact
  | some i => exact ChartDisk.isCompact_circleAtRadius (d i) (D.bounds i).2.le

lemma curve_finite (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (B : CompactSmoothSeam S)
    {n : ℕ} {d : Fin n → ChartDisk X A} (D : Data S B d)
    (i j : Option (Fin n)) (hij : i ≠ j) :
    (arrangementCurve B.carrier d D.radius i ∩
      arrangementCurve B.carrier d D.radius j).Finite := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j => simpa [arrangementCurve, inter_comm] using D.finite_seam j
  | some i =>
    cases j with
    | none => exact D.finite_seam i
    | some j => exact D.finite_pairs i j (fun h => hij (congrArg some h))


def curveManifold (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (B : CompactSmoothSeam S)
    {n : ℕ} {d : Fin n → ChartDisk X A} (D : Data S B d) :
    ∀ i : Option (Fin n), SmoothManifold 1 .euclidean
      (arrangementCurve B.carrier d D.radius i)
  | none => B.manifold
  | some i => (D.circle i).manifold

lemma curveEmbedding (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (B : CompactSmoothSeam S)
    {n : ℕ} {d : Fin n → ChartDisk X A} (D : Data S B d) :
    ∀ i : Option (Fin n), IsSmoothEmbedding (curveManifold S B D i) S Subtype.val
  | none => B.embedding
  | some i => (D.circle i).embedding

lemma exists_data (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (B : CompactSmoothSeam S)
    (n : ℕ) (d : Fin n → ChartDisk X A)
    (hd : ∀ i, ∃ e ∈ S.smoothStructure.val,
      (d i).chart = euclideanChartToPlane e) : Nonempty (Data S B d) := by
  classical
  induction n with
  | zero =>
    refine ⟨{
      radius := fun i => i.elim0
      bounds := fun i => i.elim0
      circle := fun i => i.elim0
      transverse_pairs := fun i => i.elim0
      transverse_seam := fun i => i.elim0
      finite_pairs := fun i => i.elim0
      finite_seam := fun i => i.elim0
      no_triple := ?_ }⟩
    intro i j k hij hik hjk
    have hi : i = none := by cases i with | none => rfl | some i => exact Fin.elim0 i
    have hj : j = none := by cases j with | none => rfl | some j => exact Fin.elim0 j
    exact (hij (hi.trans hj.symm)).elim
  | succ n ih =>
    let d0 : Fin n → ChartDisk X A := fun i => d i.succ
    obtain ⟨D⟩ := ih d0 (fun i => hd i.succ)
    let C : Option (Fin n) → Set X := arrangementCurve B.carrier d0 D.radius
    let M : ∀ i, SmoothManifold 1 .euclidean (C i) := curveManifold S B D
    let : ∀ i, CompactSpace (C i) := fun i =>
      isCompact_iff_compactSpace.mp (curve_compact S B D i)
    let P : Set X := crossings C
    have hP : P.Finite := finite_crossings C (curve_finite S B D)
    obtain ⟨e, he, hde⟩ := hd 0
    obtain ⟨ρ, hρ, newCircle, havoid, hfinite, htrans⟩ :=
      SmoothCircles.exists_transverse_chartCircle
        S A (d 0) e he hde (fun i => C i) M
        (fun _ => Subtype.val) (fun i => (curveEmbedding S B D i).1) P hP
    let r : Fin (n+1) → ℝ := Fin.cons ρ D.radius
    have hfinite' : ∀ i, (C i ∩ (d 0).circleAtRadius ρ).Finite := by
      intro i
      simpa only [Subtype.range_coe] using hfinite i
    have hcurve : ∀ i : Option (Fin (n+1)),
        arrangementCurve B.carrier d r i =
          (insertIndex i).elim ((d 0).circleAtRadius ρ) C := by
      intro i
      cases i with
      | none => rfl
      | some i =>
        refine Fin.cases ?_ (fun i => ?_) i <;> simp [arrangementCurve, r, insertIndex, C, d0]
    let circle : ∀ i, SmoothChartCircle S (d i) (r i) :=
      Fin.cases newCircle (fun i => D.circle i)
    refine ⟨{
      radius := r
      bounds := ?_
      circle := circle
      transverse_pairs := ?_
      transverse_seam := ?_
      finite_pairs := ?_
      finite_seam := ?_
      no_triple := ?_ }⟩
    · exact Fin.cases hρ (fun i => D.bounds i)
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro h; exact (h rfl).elim
        · intro _
          exact TangentTransport.transverse_symm S (D.circle j).manifold
            newCircle.manifold (htrans (some j))
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _; exact htrans (some i)
        · intro hij
          exact D.transverse_pairs i j (fun h => hij (congrArg Fin.succ h))
    · refine Fin.cases ?_ (fun i => ?_)
      · exact TangentTransport.transverse_symm S B.manifold newCircle.manifold (htrans none)
      · exact D.transverse_seam i
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro h; exact (h rfl).elim
        · intro _; simpa [C, d0, r, arrangementCurve, inter_comm] using hfinite' (some j)
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _; simpa [C, d0, r, arrangementCurve] using hfinite' (some i)
        · intro hij
          exact D.finite_pairs i j (fun h => hij (congrArg Fin.succ h))
    · refine Fin.cases ?_ (fun i => ?_)
      · simpa [C, r, arrangementCurve, inter_comm] using hfinite' none
      · exact D.finite_seam i
    · intro i j k hij hik hjk
      rw [hcurve i, hcurve j, hcurve k]
      exact no_triple_option C ((d 0).circleAtRadius ρ) D.no_triple havoid
        (insertIndex i) (insertIndex j) (insertIndex k)
        (fun h => hij (insertIndex_injective h))
        (fun h => hik (insertIndex_injective h))
        (fun h => hjk (insertIndex_injective h))


/-- Successive radius choices in every supplied disk preserve the original
inner cover and give a transverse finite arrangement with no triple points. -/
theorem exists_finite_data (S : SmoothManifold 2 .euclidean X)
    (K : Set X) (hK : IsCompact K) (A : Set (ModelChart 2 .euclidean X))
    (hAS : A ⊆ S.smoothStructure.val)
    (hcover : ∀ p ∈ K, ∃ e ∈ A, p ∈ e.source) (B : CompactSmoothSeam S) :
    ∃ (n : ℕ) (d : Fin n → ChartDisk X (planeChartFamily A)) (D : Data S B d),
      K ⊆ ⋃ i, (d i).inner ∧
      K ⊆ ⋃ i, (d i).openAtRadius (D.radius i) := by
  obtain ⟨n, d, hdcover⟩ := finite_supplied_smooth_chartDisk_cover K hK A hcover
  have hd : ∀ i, ∃ e ∈ S.smoothStructure.val,
      (d i).chart = euclideanChartToPlane e := by
    intro i
    obtain ⟨e, he, hde⟩ := (d i).chart_mem
    exact ⟨e, hAS he, hde.symm⟩
  obtain ⟨D⟩ := exists_data S B n d hd
  refine ⟨n, d, D, hdcover, ?_⟩
  exact hdcover.trans (Set.iUnion_mono (fun i =>
    ChartDisk.inner_subset_openAtRadius (d i) (D.bounds i).1.le))

/-- Attach local geometric normal forms to the finite arrangement core. -/
def Data.toArrangement (S : SmoothManifold 2 .euclidean X)
    (K : Set X) (A : Set (ModelChart 2 .euclidean X)) (B : CompactSmoothSeam S)
    {n : ℕ} {d : Fin n → ChartDisk X (planeChartFamily A)} (D : Data S B d)
    (hcover : K ⊆ ⋃ i, (d i).inner)
    (hnormal : ∀ p, ∀ O : Set X, IsOpen O → p ∈ O →
      Nonempty (ArrangementNormalForm S B.carrier d D.radius p O)) :
    TransverseDiskArrangement S K A B where
  count := n
  disk := d
  radius := D.radius
  radius_bounds := D.bounds
  inner_cover := hcover
  final_cover := hcover.trans (Set.iUnion_mono (fun i =>
    ChartDisk.inner_subset_openAtRadius (d i) (D.bounds i).1.le))
  circle := D.circle
  transverse_pairs := D.transverse_pairs
  transverse_seam := D.transverse_seam
  finite_pairs := D.finite_pairs
  finite_seam := D.finite_seam
  no_triple := D.no_triple
  normal_forms := hnormal

end FiniteArrangement


/-- The signed squared-radius function is globally smooth in the actual
original Euclidean chart coordinates. -/
theorem contDiff_signed_squaredRadius (c : Plane) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Euclidean 2 => ‖toPlane z - c‖ ^ 2 - r ^ 2) :=
  (ContDiff.norm_sq ℝ (toPlane.contDiff.sub contDiff_const)).sub contDiff_const

/-- The scalar signed squared-radius differential is surjective away from
the disk center. This is deduced from the actual already-proved P104 radius
map, with its one-coordinate Euclidean target. -/
theorem signed_squaredRadius_derivative_surjective (c : Plane) (r : ℝ)
    (z : Euclidean 2) (hz : toPlane z - c ≠ 0) :
    Function.Surjective
      (fderiv ℝ (fun w : Euclidean 2 => ‖toPlane w - c‖ ^ 2 - r ^ 2) z) := by
  let f : Euclidean 2 → ℝ := fun w => ‖toPlane w - c‖ ^ 2
  let L : Euclidean 2 →L[ℝ] ℝ := fderiv ℝ f z
  have hfcont : ContDiff ℝ (⊤ : ℕ∞) f :=
    ContDiff.norm_sq ℝ (toPlane.contDiff.sub contDiff_const)
  have hf : HasFDerivAt f L z :=
    (hfcont.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hF : HasFDerivAt (fun w (_ : Fin 1) => f w)
      (ContinuousLinearMap.pi fun _ : Fin 1 => L) z := hasFDerivAt_pi.mpr (fun _ => hf)
  have hs := SmoothCircles.squaredRadius_derivative_surjective c z hz
  change Function.Surjective (fderiv ℝ (fun w (_ : Fin 1) => f w) z) at hs
  rw [hF.fderiv] at hs
  have hsub := hf.sub_const (r ^ 2)
  rw [hsub.fderiv]
  intro t
  obtain ⟨w, hw⟩ := hs (fun _ => t)
  exact ⟨w, congrFun hw 0⟩

/-- The original chart circle and disk are the exact zero and strict negative
sets of the signed squared radius; the source condition is retained. -/
theorem chartDisk_signed_squaredRadius {X : Type u} [TopologicalSpace X]
    {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A)
    (e : ModelChart 2 .euclidean X) (hde : d.chart = euclideanChartToPlane e)
    {r : ℝ} (hr : 0 < r) (houter : r ≤ d.outerRadius)
    (x : X) (hx : x ∈ e.source) :
    (x ∈ d.circleAtRadius r ↔ ‖toPlane (e x).val - d.center‖ ^ 2 - r ^ 2 = 0) ∧
    (x ∈ d.openAtRadius r ↔ ‖toPlane (e x).val - d.center‖ ^ 2 - r ^ 2 < 0) := by
  have hsource : d.chart.source = e.source := by rw [hde]; rfl
  have hval : d.chart x = toPlane (e x).val := by rw [hde]; rfl
  have hxsource : x ∈ d.chart.source := hsource.symm ▸ hx
  have hcircle : x ∈ d.circleAtRadius r ↔ ‖d.chart x - d.center‖ = r := by
    constructor
    · rintro ⟨z, hz, hzx⟩
      have hzt : z ∈ d.chart.target :=
        ChartDisk.closedBall_subset_target d houter (Metric.sphere_subset_closedBall hz)
      rw [← hzx, d.chart.right_inv hzt]
      simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    · intro hrad
      refine ⟨d.chart x, ?_, d.chart.left_inv hxsource⟩
      simpa only [Metric.mem_sphere, dist_eq_norm] using hrad
  constructor
  · rw [← hval, hcircle, sub_eq_zero]
    exact (sq_eq_sq₀ (norm_nonneg _) hr.le).symm
  · change (x ∈ d.chart.source ∧ d.chart x ∈ Metric.ball d.center r) ↔ _
    rw [and_iff_right hxsource, Metric.mem_ball, dist_eq_norm, hval, sub_lt_zero]
    exact (sq_lt_sq₀ (norm_nonneg _) hr.le).symm

/-- Positive-radius circle points are regular zeros of the genuine smooth
scalar defining function in the supplied original chart. -/
theorem chartDisk_signed_squaredRadius_regular {X : Type u} [TopologicalSpace X]
    {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A)
    (e : ModelChart 2 .euclidean X) (hde : d.chart = euclideanChartToPlane e)
    {r : ℝ} (hr : 0 < r) (houter : r ≤ d.outerRadius)
    (x : X) (hx : x ∈ d.circleAtRadius r) :
    x ∈ e.source ∧
      ‖toPlane (e x).val - d.center‖ ^ 2 - r ^ 2 = 0 ∧
      Function.Surjective
        (fderiv ℝ (fun w : Euclidean 2 => ‖toPlane w - d.center‖ ^ 2 - r ^ 2) (e x).val) := by
  have hsource : d.chart.source = e.source := by rw [hde]; rfl
  have hxs : x ∈ e.source := by
    rw [← hsource]
    obtain ⟨z, hz, rfl⟩ := hx
    exact d.chart.map_target
      (ChartDisk.closedBall_subset_target d houter (Metric.sphere_subset_closedBall hz))
  have hzero := ((chartDisk_signed_squaredRadius d e hde hr houter x hxs).1).mp hx
  refine ⟨hxs, hzero, signed_squaredRadius_derivative_surjective d.center r (e x).val ?_⟩
  intro hcenter
  rw [hcenter, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_sub] at hzero
  have hsq : r ^ 2 = 0 := neg_eq_zero.mp hzero
  exact (ne_of_gt hr) (sq_eq_zero_iff.mp hsq)


open SmoothManifolds.MapClassData SmoothManifolds.TangentData SmoothManifolds.DifferentialData
open SmoothManifolds.FiniteRegularityData SmoothManifolds.TransversePreimageData


/-- Actual transverse inclusion tangents span in every common ambient chart. -/
theorem transverse_chartDerivative_ranges {m n k : ℕ} {a b c : SmoothManifolds.ModelKind}
    {X : Type u} [TopologicalSpace X] (S : SmoothManifold n b X)
    {s t : Set X} (R : SmoothManifold m a s) (T : SmoothManifold k c t)
    (hR : IsSmoothMap R S Subtype.val) (hT : IsSmoothMap T S Subtype.val)
    (ht : IsTransverse R S T Subtype.val)
    (p : s) (hp : p.val ∈ t)
    (e : ModelChart n b X) (he : e ∈ S.smoothStructure.val) (hpe : p.val ∈ e.source)
    (d : ModelChart m a s) (hd : d ∈ R.smoothStructure.val) (hpd : p ∈ d.source)
    (f : ModelChart k c t) (hf : f ∈ T.smoothStructure.val)
    (hpf : (⟨p.val, hp⟩ : t) ∈ f.source) :
    LinearMap.range (chartDerivative d e Subtype.val p).toLinearMap ⊔
      LinearMap.range (chartDerivative f e Subtype.val ⟨p.val, hp⟩).toLinearMap = ⊤ := by
  obtain ⟨L, hL, _⟩ := SmoothManifolds.differential_exists R S Subtype.val hR p
  obtain ⟨I, hI, _⟩ := SmoothManifolds.differential_exists T S Subtype.val hT ⟨p.val, hp⟩
  obtain ⟨E, hE⟩ := SmoothManifolds.FiniteRegularity.exists_smooth_chart_coordinates
    S p.val e he hpe
  obtain ⟨D, hD⟩ := SmoothManifolds.FiniteRegularity.exists_smooth_chart_coordinates
    R p d hd hpd
  obtain ⟨F, hF⟩ := SmoothManifolds.FiniteRegularity.exists_smooth_chart_coordinates
    T ⟨p.val, hp⟩ f hf hpf
  have hLD := SmoothManifolds.FiniteRegularity.smooth_jacobian_coordinateDerivative
    R S Subtype.val hR p L hL d e hd he hpd hpe D E hD hE
  have hIF := SmoothManifolds.FiniteRegularity.smooth_jacobian_coordinateDerivative
    T S Subtype.val hT ⟨p.val, hp⟩ I hI f e hf he hpf hpe F E hF hE
  have hmapL : (LinearMap.range L).map E.toLinearMap =
      LinearMap.range (chartDerivative d e Subtype.val p).toLinearMap := by
    ext y
    constructor
    · rintro ⟨z, ⟨v, rfl⟩, rfl⟩
      exact ⟨D v, (hLD v).symm⟩
    · rintro ⟨v, rfl⟩
      refine ⟨L (D.symm v), ⟨D.symm v, rfl⟩, ?_⟩
      simpa only [LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe, LinearEquiv.apply_symm_apply] using hLD (D.symm v)
  have hmapI : (LinearMap.range I).map E.toLinearMap =
      LinearMap.range (chartDerivative f e Subtype.val ⟨p.val, hp⟩).toLinearMap := by
    ext y
    constructor
    · rintro ⟨z, ⟨v, rfl⟩, rfl⟩
      exact ⟨F v, (hIF v).symm⟩
    · rintro ⟨v, rfl⟩
      refine ⟨I (F.symm v), ⟨F.symm v, rfl⟩, ?_⟩
      simpa only [LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe, LinearEquiv.apply_symm_apply] using hIF (F.symm v)
  have hspan := congrArg (Submodule.map E.toLinearMap) (ht p hp L I hL hI)
  rwa [Submodule.map_sup, hmapL, hmapI, Submodule.map_top,
    LinearMap.range_eq_top.mpr E.surjective] at hspan


/-- A differentiable coordinate function locally constant on a smooth curve
annihilates its actual coordinate tangent image. -/
theorem chartDerivative_range_le_ker_of_locally_zero {m n : ℕ}
    {a : SmoothManifolds.ModelKind} {Y X : Type u}
    [TopologicalSpace Y] [TopologicalSpace X]
    (R : SmoothManifold m a Y) (S : SmoothManifold n .euclidean X)
    (j : Y → X) (hj : IsSmoothMap R S j) (p : Y)
    (d : ModelChart m a Y) (hd : d ∈ R.smoothStructure.val) (hpd : p ∈ d.source)
    (e : ModelChart n .euclidean X) (he : e ∈ S.smoothStructure.val)
    (hpe : j p ∈ e.source)
    (f : SmoothManifolds.Euclidean n → ℝ)
    (L : SmoothManifolds.Euclidean n →L[ℝ] ℝ)
    (hf : HasFDerivAt f L (e (j p)).val)
    (hzero : (fun q => f (e (j q)).val) =ᶠ[nhds p] (fun _ => (0 : ℝ))) :
    LinearMap.range (chartDerivative d e j p).toLinearMap ≤ LinearMap.ker L.toLinearMap := by
  obtain ⟨F, hF, hFeq⟩ := SmoothManifolds.FiniteRegularity.chartDerivative_exists
    (⊤ : ℕ∞) (by simp) d e j p ((hj p).2 d hd e he hpd hpe)
  have hFp : F (d p).val = (e (j p)).val := hFeq.eq_of_nhds
  let K : SmoothManifolds.Euclidean m →L[ℝ] SmoothManifolds.Euclidean 1 :=
    ContinuousLinearMap.pi (fun _ : Fin 1 => L.comp (chartDerivative d e j p))
  have hK : HasFDerivAt (fun z (_ : Fin 1) => f (F z)) K (d p).val := by
    apply hasFDerivAt_pi.mpr
    intro i
    exact (hFp.symm ▸ hf).comp (d p).val hF
  have hcoord : HasCoordinateDerivative d (fun _ : Y => (0 : SmoothManifolds.Euclidean 1)) p K := by
    refine ⟨fun z (_ : Fin 1) => f (F z), hK, ?_⟩
    filter_upwards [hFeq, hzero] with q hq hq0
    funext i
    change f (F (d q).val) = 0
    rw [hq, hq0]
  have hKzero : K = 0 := by
    have h₁ := SmoothManifolds.FiniteRegularity.coordinateDerivative_eq d
      (fun _ : Y => (0 : SmoothManifolds.Euclidean 1)) p hpd K hcoord
    have h₂ := SmoothManifolds.FiniteRegularity.coordinateDerivative_eq d
      (fun _ : Y => (0 : SmoothManifolds.Euclidean 1)) p hpd 0
      ⟨fun _ => 0, hasFDerivAt_const _ _, Filter.Eventually.of_forall (fun _ => rfl)⟩
    exact h₁.symm.trans h₂
  rintro _ ⟨v, rfl⟩
  change L ((chartDerivative d e j p) v) = 0
  have hv := congrArg (fun D : SmoothManifolds.Euclidean m →L[ℝ] SmoothManifolds.Euclidean 1 => D v 0) hKzero
  simpa only [K, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    zero_apply, Pi.zero_apply] using hv


/-- Two differentiable local defining functions of actual transverse embedded
curves have complementary normal kernels in every ambient chart. -/
theorem transverse_defining_kernels {m n k : ℕ} {a c : SmoothManifolds.ModelKind}
    {X : Type u} [TopologicalSpace X] (S : SmoothManifold n .euclidean X)
    {s t : Set X} (R : SmoothManifold m a s) (T : SmoothManifold k c t)
    (hR : IsSmoothMap R S Subtype.val) (hT : IsSmoothMap T S Subtype.val)
    (ht : IsTransverse R S T Subtype.val)
    (p : s) (hp : p.val ∈ t)
    (e : ModelChart n .euclidean X) (he : e ∈ S.smoothStructure.val)
    (hpe : p.val ∈ e.source)
    (f g : SmoothManifolds.Euclidean n → ℝ)
    (L M : SmoothManifolds.Euclidean n →L[ℝ] ℝ)
    (hf : HasFDerivAt f L (e p.val).val) (hg : HasFDerivAt g M (e p.val).val)
    (hfzero : (fun q : s => f (e q.val).val) =ᶠ[nhds p] (fun _ => (0 : ℝ)))
    (hgzero : (fun q : t => g (e q.val).val) =ᶠ[nhds (⟨p.val, hp⟩ : t)]
      (fun _ => (0 : ℝ))) :
    LinearMap.ker L.toLinearMap ⊔ LinearMap.ker M.toLinearMap = ⊤ := by
  obtain ⟨d, hd, hpd⟩ := R.smoothStructure.property.1.1 p
  obtain ⟨c, hc, hpc⟩ := T.smoothStructure.property.1.1 ⟨p.val, hp⟩
  have hspan := transverse_chartDerivative_ranges S R T hR hT ht p hp e he hpe
    d hd hpd c hc hpc
  have hL := chartDerivative_range_le_ker_of_locally_zero R S Subtype.val hR p
    d hd hpd e he hpe f L hf hfzero
  have hM := chartDerivative_range_le_ker_of_locally_zero T S Subtype.val hT ⟨p.val, hp⟩
    c hc hpc e he hpe g M hg hgzero
  apply top_unique
  rw [← hspan]
  exact sup_le_sup hL hM


namespace LocalGeometry
open Filter SmoothManifolds.MapData SmoothManifolds.FiniteRegularityData

/-- A scalar submersion in one smooth chart has an exact smooth representative
with surjective derivative in any other chart at the same point. -/
theorem exists_chart_scalar_representative {n : ℕ} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n .euclidean X)
    (e d : ModelChart n .euclidean X)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : X) (hpe : p ∈ e.source) (hpd : p ∈ d.source)
    (f : Euclidean n → ℝ) (V : Set (Euclidean n)) (hV : IsOpen V)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) (hpV : (d p).val ∈ V)
    (L : Euclidean n →L[ℝ] ℝ) (hL : HasFDerivAt f L (d p).val)
    (hLs : Function.Surjective L) :
    ∃ (U : Set (Euclidean n)) (F : Euclidean n → ℝ) (J : Euclidean n →L[ℝ] ℝ),
      IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
      HasFDerivAt F J (e p).val ∧ Function.Surjective J ∧
      (∀ x ∈ e.source, (e x).val ∈ U → F (e x).val = f (d x).val) ∧
      (∀ x ∈ e.source, (e x).val ∈ U → x ∈ d.source) := by
  obtain ⟨U₀, hU₀, hpU₀, G, hG, hrep⟩ := SmoothManifolds.chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he d hd) hpe hpd
  have hGp : G (e p).val = (d p).val := hrep.eq_of_nhds
  have hGder : HasFDerivAt G (fderiv ℝ G (e p).val) (e p).val :=
    ((hG.contDiffAt (hU₀.mem_nhds hpU₀)).differentiableAt (by simp)).hasFDerivAt
  have hJ : chartDerivative e d id p = fderiv ℝ G (e p).val := by
    apply SmoothManifolds.FiniteRegularity.coordinateDerivative_eq e _ p hpe
    exact ⟨G, hGder, hrep⟩
  have hGsurj : Function.Surjective (fderiv ℝ G (e p).val) := by
    rw [← hJ]
    exact (SmoothManifolds.FiniteRegularity.transitionLinearEquiv (⊤ : ℕ∞) (by simp)
      S.smoothStructure.val S.smoothStructure.property.1 p e d he hd hpe hpd).surjective
  obtain ⟨N, hNsub, hN, hpN⟩ := mem_nhds_iff.mp
    (hrep.and (d.open_source.mem_nhds hpd))
  let a : OpenPartialHomeomorph X (Euclidean n) :=
    e.transHomeomorph (Homeomorph.Set.univ _)
  let W : Set (Euclidean n) := a.target ∩ a.symm ⁻¹' N
  have hW : IsOpen W := a.symm.isOpen_inter_preimage hN
  have hpW : (e p).val ∈ W := by
    refine ⟨a.map_source hpe, ?_⟩
    change a.symm (a p) ∈ N
    rwa [a.left_inv hpe]
  let U : Set (Euclidean n) := (U₀ ∩ G ⁻¹' V) ∩ W
  have hU : IsOpen U := (hG.continuousOn.isOpen_inter_preimage hU₀ hV).inter hW
  have hpU : (e p).val ∈ U := ⟨⟨hpU₀, by change G (e p).val ∈ V; rwa [hGp]⟩, hpW⟩
  let F : Euclidean n → ℝ := f ∘ G
  let J : Euclidean n →L[ℝ] ℝ := L.comp (fderiv ℝ G (e p).val)
  refine ⟨U, F, J, hU, hpU, ?_, ?_, hLs.comp hGsurj, ?_, ?_⟩
  · exact hf.comp (hG.mono (inter_subset_left.trans inter_subset_left))
      (fun z hz => hz.1.2)
  · exact (hGp ▸ hL).comp (e p).val hGder
  · intro x hx hxU
    have hxN : x ∈ N := by
      have hh : a.symm (a x) ∈ N := hxU.2.2
      rwa [a.left_inv hx] at hh
    exact congrArg f (hNsub hxN).1
  · intro x hx hxU
    have hxN : x ∈ N := by
      have hh : a.symm (a x) ∈ N := hxU.2.2
      rwa [a.left_inv hx] at hh
    exact (hNsub hxN).2

end LocalGeometry

namespace LocalGeometry

/-- No triple point leaves exactly zero, one or two incident curve labels. -/
theorem incident_cases {X ι : Type*} (C : ι → Set X) (p : X)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → C i ∩ C j ∩ C k = ∅) :
    (∀ i, p ∉ C i) ∨
    (∃ i, p ∈ C i ∧ ∀ j, p ∈ C j → j = i) ∨
    (∃ i j, i ≠ j ∧ p ∈ C i ∧ p ∈ C j ∧ ∀ k, p ∈ C k → k = i ∨ k = j) := by
  classical
  by_cases hnone : ∀ i, p ∉ C i
  · exact Or.inl hnone
  · push Not at hnone
    obtain ⟨i, hi⟩ := hnone
    by_cases hone : ∀ j, p ∈ C j → j = i
    · exact Or.inr (Or.inl ⟨i, hi, hone⟩)
    · push Not at hone
      obtain ⟨j, hj, hji⟩ := hone
      refine Or.inr (Or.inr ⟨i, j, Ne.symm hji, hi, hj, ?_⟩)
      intro k hk
      by_cases hki : k = i
      · exact Or.inl hki
      · by_cases hkj : k = j
        · exact Or.inr hkj
        · have hmem : p ∈ C i ∩ C j ∩ C k := ⟨⟨hi, hj⟩, hk⟩
          rw [htriple i j k (Ne.symm hji) (Ne.symm hki) (Ne.symm hkj)] at hmem
          exact hmem.elim

end LocalGeometry

namespace FiniteArrangement
/-- Pairwise transversality includes the optional seam as an ordinary label. -/
theorem curve_transverse (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (B : CompactSmoothSeam S)
    {n : ℕ} {d : Fin n → ChartDisk X A} (D : Data S B d)
    (i j : Option (Fin n)) (hij : i ≠ j) :
    SmoothManifolds.TransversePreimageData.IsTransverse
      (curveManifold S B D i) S (curveManifold S B D j) Subtype.val := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
        exact TangentTransport.transverse_symm S (D.circle j).manifold B.manifold
          (D.transverse_seam j)
  | some i =>
    cases j with
    | none => exact D.transverse_seam i
    | some j => exact D.transverse_pairs i j (fun h => hij (congrArg some h))

end FiniteArrangement

namespace LocalGeometry
structure LocalDefiningData (S : SmoothManifold 2 .euclidean X) (C : Set X)
    (e : ModelChart 2 .euclidean X) (p : X) where
  domain : Set (Euclidean 2)
  isOpen_domain : IsOpen domain
  mem_domain : (e p).val ∈ domain
  function : Euclidean 2 → ℝ
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) function domain
  zero : function (e p).val = 0
  regular : Function.Surjective (fderiv ℝ function (e p).val)
  curve_eq : ∀ x ∈ e.source, (e x).val ∈ domain →
    (x ∈ C ↔ function (e x).val = 0)
end LocalGeometry

namespace LocalGeometry
open Filter
variable {X : Type u} [TopologicalSpace X]

theorem LocalDefiningData.hasFDerivAt
    {S : SmoothManifold 2 .euclidean X} {C : Set X}
    {e : ModelChart 2 .euclidean X} {p : X} (F : LocalDefiningData S C e p) :
    HasFDerivAt F.function (fderiv ℝ F.function (e p).val) (e p).val :=
  ((F.smooth.contDiffAt (F.isOpen_domain.mem_nhds F.mem_domain)).differentiableAt
    (by simp)).hasFDerivAt

/-- The exact local zero-set identity is an actual zero germ on the curve's
ambient subspace; it can therefore be differentiated along its tangent. -/
theorem LocalDefiningData.eventually_zero
    {S : SmoothManifold 2 .euclidean X} {C : Set X}
    {e : ModelChart 2 .euclidean X} {p : X} (F : LocalDefiningData S C e p)
    (hpC : p ∈ C) (hpe : p ∈ e.source) :
    (fun q : C => F.function (e q.val).val) =ᶠ[𝓝 (⟨p, hpC⟩ : C)] (fun _ => 0) := by
  have hU : IsOpen (e.source ∩ (fun x => (e x).val) ⁻¹' F.domain) :=
    e.isOpen_inter_preimage (F.isOpen_domain.preimage continuous_subtype_val)
  have hloc : ∀ᶠ q : C in 𝓝 (⟨p, hpC⟩ : C),
      q.val ∈ e.source ∩ (fun x => (e x).val) ⁻¹' F.domain :=
    continuous_subtype_val.continuousAt.eventually (hU.mem_nhds ⟨hpe, F.mem_domain⟩)
  filter_upwards [hloc] with q hq
  exact (F.curve_eq q.val hq.1 hq.2).mp q.property

/-- Local regular defining functions of a transverse pair have precisely the
independence hypothesis used by the two-coordinate inverse theorem. -/
theorem LocalDefiningData.transverse_kernels
    (S : SmoothManifold 2 .euclidean X) {C D : Set X}
    (R : SmoothManifold 1 .euclidean C) (T : SmoothManifold 1 .euclidean D)
    (hR : SmoothManifolds.MapData.IsSmoothMap R S Subtype.val)
    (hT : SmoothManifolds.MapData.IsSmoothMap T S Subtype.val)
    (htrans : SmoothManifolds.TransversePreimageData.IsTransverse R S T Subtype.val)
    (p : X) (hpC : p ∈ C) (hpD : p ∈ D)
    (e : ModelChart 2 .euclidean X) (he : e ∈ S.smoothStructure.val)
    (hpe : p ∈ e.source) (F : LocalDefiningData S C e p) (G : LocalDefiningData S D e p) :
    LinearMap.ker (fderiv ℝ F.function (e p).val).toLinearMap ⊔
      LinearMap.ker (fderiv ℝ G.function (e p).val).toLinearMap = ⊤ := by
  exact transverse_defining_kernels S R T hR hT htrans ⟨p, hpC⟩ hpD e he hpe
    F.function G.function (fderiv ℝ F.function (e p).val) (fderiv ℝ G.function (e p).val)
    F.hasFDerivAt G.hasFDerivAt (F.eventually_zero hpC hpe) (G.eventually_zero hpD hpe)

end LocalGeometry

namespace LocalGeometry
open Filter

/-- The selected circle has an actual smooth regular scalar defining function
in any chosen common ambient chart, preserving the original disk sign. -/
theorem exists_circle_local_defining_functions {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A)
    (a : ModelChart 2 .euclidean X) (ha : a ∈ S.smoothStructure.val)
    (hda : d.chart = euclideanChartToPlane a)
    (e : ModelChart 2 .euclidean X) (he : e ∈ S.smoothStructure.val)
    {r : ℝ} (hr : 0 < r) (houter : r ≤ d.outerRadius)
    (p : X) (hpc : p ∈ d.circleAtRadius r) (hpe : p ∈ e.source) :
    ∃ (U : Set (Euclidean 2)) (F : Euclidean 2 → ℝ) (J : Euclidean 2 →L[ℝ] ℝ),
      IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
      HasFDerivAt F J (e p).val ∧ Function.Surjective J ∧ F (e p).val = 0 ∧
      ∀ x ∈ e.source, (e x).val ∈ U →
        (x ∈ d.circleAtRadius r ↔ F (e x).val = 0) ∧
        (x ∈ d.openAtRadius r ↔ F (e x).val < 0) := by
  let f : Euclidean 2 → ℝ := fun z => ‖toPlane z - d.center‖ ^ 2 - r ^ 2
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_signed_squaredRadius d.center r
  obtain ⟨hpa, hpzero, hpregular⟩ :=
    chartDisk_signed_squaredRadius_regular d a hda hr houter p hpc
  have hfd : HasFDerivAt f (fderiv ℝ f (a p).val) (a p).val :=
    (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
  obtain ⟨U, F, J, hU, hpU, hF, hJ, hJs, hEq, hsource⟩ :=
    exists_chart_scalar_representative S e a he ha p hpe hpa f univ isOpen_univ
      hf.contDiffOn (mem_univ _) (fderiv ℝ f (a p).val) hfd hpregular
  refine ⟨U, F, J, hU, hpU, hF, hJ, hJs, ?_, ?_⟩
  · rw [hEq p hpe hpU]
    exact hpzero
  · intro x hx hxU
    rw [hEq x hx hxU]
    exact chartDisk_signed_squaredRadius d a hda hr houter x (hsource x hx hxU)


/-- Package the circle's exact zero and negative sides in the shared local
submersion interface. -/
theorem exists_circle_localDefiningData {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold 2 .euclidean X)
    {A : Set (OpenPartialHomeomorph X Plane)} (d : ChartDisk X A)
    (a : ModelChart 2 .euclidean X) (ha : a ∈ S.smoothStructure.val)
    (hda : d.chart = euclideanChartToPlane a)
    (e : ModelChart 2 .euclidean X) (he : e ∈ S.smoothStructure.val)
    {r : ℝ} (hr : 0 < r) (houter : r ≤ d.outerRadius)
    (p : X) (hpc : p ∈ d.circleAtRadius r) (hpe : p ∈ e.source) :
    ∃ F : LocalDefiningData S (d.circleAtRadius r) e p,
      ∀ x ∈ e.source, (e x).val ∈ F.domain →
        (x ∈ d.openAtRadius r ↔ F.function (e x).val < 0) := by
  obtain ⟨U, F, J, hU, hpU, hF, hJ, hJs, hzero, hEq⟩ :=
    exists_circle_local_defining_functions S d a ha hda e he hr houter p hpc hpe
  let D : LocalDefiningData S (d.circleAtRadius r) e p := {
    domain := U
    isOpen_domain := hU
    mem_domain := hpU
    function := F
    smooth := hF
    zero := hzero
    regular := by simpa only [hJ.fderiv] using hJs
    curve_eq := fun x hx hxU => (hEq x hx hxU).1 }
  exact ⟨D, fun x hx hxU => (hEq x hx hxU).2⟩

/-- A disk's retained membership label supplies its original smooth chart. -/
theorem exists_supplied_circle_localDefiningData {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold 2 .euclidean X)
    {A : Set (ModelChart 2 .euclidean X)} (hAS : A ⊆ S.smoothStructure.val)
    (d : ChartDisk X (planeChartFamily A))
    (e : ModelChart 2 .euclidean X) (he : e ∈ S.smoothStructure.val)
    {r : ℝ} (hr : 0 < r) (houter : r ≤ d.outerRadius)
    (p : X) (hpc : p ∈ d.circleAtRadius r) (hpe : p ∈ e.source) :
    ∃ F : LocalDefiningData S (d.circleAtRadius r) e p,
      ∀ x ∈ e.source, (e x).val ∈ F.domain →
        (x ∈ d.openAtRadius r ↔ F.function (e x).val < 0) := by
  obtain ⟨a, ha, hda⟩ := d.chart_mem
  exact exists_circle_localDefiningData S d a (hAS ha) hda.symm e he hr houter p hpc hpe

end LocalGeometry

namespace LocalGeometry
open SmoothManifolds.MapClassData SmoothManifolds.SliceData

/-- The actual coordinate line slice in a surface is defined by coordinate 1. -/
theorem coordinateSlice_one_two (z : Euclidean 2) :
    z ∈ coordinateSlice 1 2 .euclidean ↔ z 1 = 0 := by
  constructor
  · rintro ⟨w, _, rfl⟩
    simp [sliceEmbedding]
  · intro hz
    refine ⟨fun _ : Fin 1 => z 0, mem_univ _, ?_⟩
    ext i
    fin_cases i <;> simp [sliceEmbedding, hz]

/-- A genuine embedded boundaryless curve admits a regular scalar defining
function in any prescribed original smooth chart at one of its points. -/
theorem exists_embedded_curve_defining_function
    {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold 2 .euclidean X) {s : Set X}
    (R : SmoothManifold 1 .euclidean s)
    (hR : IsSmoothEmbedding R S Subtype.val)
    (p : s) (e : ModelChart 2 .euclidean X)
    (he : e ∈ S.smoothStructure.val) (hpe : p.val ∈ e.source) :
    ∃ (U : Set (Euclidean 2)) (F : Euclidean 2 → ℝ),
      IsOpen U ∧ (e p.val).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
      F (e p.val).val = 0 ∧
      Function.Surjective (fderiv ℝ F (e p.val).val) ∧
      (∀ x ∈ e.source, (e x).val ∈ U → (x ∈ s ↔ F (e x).val = 0)) := by
  obtain ⟨_, c, hc, hpc, hslice⟩ := SmoothManifolds.RegularLevels.embedded_boundaryless_slice
    S R Subtype.val (SmoothManifolds.intrinsicBoundary_euclidean S)
    (SmoothManifolds.intrinsicBoundary_euclidean R) hR p
  have hcS : c ∈ S.smoothStructure.val := compatibleChart_mem S c hc
  have hcurve (x : X) (hx : x ∈ c.source) : x ∈ s ↔ (c x).val 1 = 0 := by
    have hpoint : x ∈ s ↔ (c x).val ∈ coordinateSlice 1 2 .euclidean := by
      constructor
      · intro hs
        have hcx : c x ∈ c '' (range (Subtype.val : s → X) ∩ c.source) :=
          ⟨x, ⟨⟨⟨x, hs⟩, rfl⟩, hx⟩, rfl⟩
        rw [hslice.2.2] at hcx
        exact hcx.2
      · intro hs
        have hcx : c x ∈ c '' (range (Subtype.val : s → X) ∩ c.source) := by
          rw [hslice.2.2]
          exact ⟨c.map_source hx, hs⟩
        obtain ⟨y, ⟨⟨q, hqy⟩, hy⟩, hyx⟩ := hcx
        have hxy : y = x := c.injOn hy hx hyx
        exact hxy ▸ hqy ▸ q.property
    exact hpoint.trans (coordinateSlice_one_two (c x).val)
  let L : Euclidean 2 →L[ℝ] ℝ := ContinuousLinearMap.proj (1 : Fin 2)
  have hLs : Function.Surjective L := by
    intro t
    exact ⟨fun _ => t, rfl⟩
  obtain ⟨U, F, J, hU, hpU, hF, hJ, hJs, hrepr, hsource⟩ :=
    exists_chart_scalar_representative S e c he hcS p.val hpe hpc
      L univ isOpen_univ L.contDiff.contDiffOn (mem_univ _) L L.hasFDerivAt hLs
  refine ⟨U, F, hU, hpU, hF, ?_, ?_, ?_⟩
  · rw [hrepr p.val hpe hpU]
    exact (hcurve p.val hpc).mp p.property
  · rwa [hJ.fderiv]
  · intro x hx hxU
    rw [hrepr x hx hxU]
    exact hcurve x (hsource x hx hxU)


/-- Local defining data for any actual boundaryless embedded curve. -/
theorem embedded_curve_defining_data
    {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold 2 .euclidean X) {s : Set X}
    (R : SmoothManifold 1 .euclidean s)
    (hR : IsSmoothEmbedding R S Subtype.val)
    (p : X) (hp : p ∈ s) (e : ModelChart 2 .euclidean X)
    (he : e ∈ S.smoothStructure.val) (hpe : p ∈ e.source) :
    Nonempty (LocalDefiningData S s e p) := by
  obtain ⟨U, F, hU, hpU, hF, hz, hreg, heq⟩ :=
    exists_embedded_curve_defining_function S R hR ⟨p, hp⟩ e he hpe
  exact ⟨⟨U, hU, hpU, F, hF, hz, hreg, heq⟩⟩

end LocalGeometry

namespace LocalGeometry
variable {X : Type u} [TopologicalSpace X]

/-- Every incident arrangement curve has regular exact defining data in any
original smooth chart, retaining the negative side of each supplied disk. -/
theorem exists_arrangement_curve_localDefiningData
    (S : SmoothManifold 2 .euclidean X)
    {A : Set (ModelChart 2 .euclidean X)} (hAS : A ⊆ S.smoothStructure.val)
    (B : CompactSmoothSeam S) {n : ℕ}
    (d : Fin n → ChartDisk X (planeChartFamily A)) (r : Fin n → ℝ)
    (hpos : ∀ i, 0 < r i) (houter : ∀ i, r i ≤ (d i).outerRadius)
    (i : Option (Fin n)) (p : X) (hpi : p ∈ arrangementCurve B.carrier d r i)
    (e : ModelChart 2 .euclidean X) (he : e ∈ S.smoothStructure.val) (hpe : p ∈ e.source) :
    ∃ F : LocalDefiningData S (arrangementCurve B.carrier d r i) e p,
      ∀ j, i = some j → ∀ x ∈ e.source, (e x).val ∈ F.domain →
        (x ∈ (d j).openAtRadius (r j) ↔ F.function (e x).val < 0) := by
  cases i with
  | none =>
    obtain ⟨F⟩ := embedded_curve_defining_data S B.manifold B.embedding p hpi e he hpe
    refine ⟨F, ?_⟩
    intro j hj
    cases hj
  | some i =>
    obtain ⟨F, hF⟩ := exists_supplied_circle_localDefiningData S hAS (d i) e he
      (hpos i) (houter i) p hpi hpe
    refine ⟨F, ?_⟩
    intro j hij
    have hij' : i = j := Option.some.inj hij
    subst j
    exact hF

end LocalGeometry

namespace LocalGeometry
variable {X : Type u} [TopologicalSpace X]

/-- Exact coordinate axes and signs in an actual smooth chart give the
complete arbitrary-small normal form, including regular endpoint germs. -/
theorem normalForm_of_chart_axes
    (S : SmoothManifold 2 .euclidean X) {n : ℕ}
    {A : Set (OpenPartialHomeomorph X Plane)}
    (B : CompactSmoothSeam S) (d : Fin n → ChartDisk X A) (r : Fin n → ℝ)
    (hpos : ∀ i, 0 < r i) (houter : ∀ i, r i ≤ (d i).outerRadius)
    (p : X) (c : ModelChart 2 .euclidean X)
    (hc : c ∈ S.smoothStructure.val) (hpc : p ∈ c.source)
    (hcenter : coordinates c p = 0)
    (axis : Option (Fin n) → Option (Fin 2))
    (hinj : ∀ i j a, axis i = some a → axis j = some a → i = j)
    (hactive : ∀ i, axis i ≠ none ↔ p ∈ arrangementCurve B.carrier d r i)
    (hcurve : ∀ i a, axis i = some a → ∀ x ∈ c.source,
      (x ∈ arrangementCurve B.carrier d r i ↔ coordinates c x a = 0))
    (hnegative : ∀ i a, axis (some i) = some a → ∀ x ∈ c.source,
      (x ∈ (d i).openAtRadius (r i) ↔ coordinates c x a < 0))
    (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    Nonempty (ArrangementNormalForm S B.carrier d r p O) := by
  classical
  obtain ⟨N, hN, hpN, hNO, hmiss, hsign⟩ :=
    exists_arrangement_neighborhood S B d r hpos houter p O hO hpO
  obtain ⟨ρ, hρ, hball, hsub⟩ := exists_centeredChart_ball c p hpc hcenter N hN hpN
  refine ⟨{
    chart := c
    chart_mem := hc
    mem_source := hpc
    centered := hcenter
    radius := ρ
    radius_pos := hρ
    ball_in_target := hball
    neighborhood_subset := hsub.trans hNO
    axis := axis
    axis_injective := hinj
    active_iff := hactive
    curve_eq := ?_
    disk_sign := ?_
    endpoint_germs := ?_ }⟩
  · intro i x hx hxc
    cases hai : axis i with
    | none =>
      have hpno : p ∉ arrangementCurve B.carrier d r i := by
        intro hi
        exact ((hactive i).mpr hi) hai
      have hxno : x ∉ arrangementCurve B.carrier d r i :=
        fun hi => Set.disjoint_left.mp (hmiss i hpno) (hsub ⟨hx, hxc⟩) hi
      exact iff_of_false hxno (by rintro ⟨a, ha, _⟩; cases ha)
    | some a =>
      constructor
      · intro hi
        exact ⟨a, rfl, (hcurve i a hai x hx).mp hi⟩
      · rintro ⟨b, hb, hxb⟩
        have hab : a = b := Option.some.inj hb
        subst b
        exact (hcurve i a hai x hx).mpr hxb
  · intro i x hx hxc
    cases hai : axis (some i) with
    | none =>
      have hpno : p ∉ (d i).circleAtRadius (r i) := by
        intro hi
        exact ((hactive (some i)).mpr hi) hai
      exact hsign i hpno x (hsub ⟨hx, hxc⟩)
    | some a => exact hnegative i a hai x hx
  · intro i a hai
    exact endpoint_germ_of_axis S p c hc hpc hcenter ρ hρ
      (arrangementCurve B.carrier d r i) a (fun x hx _ => hcurve i a hai x hx)

/-- A sole incident curve with a genuine regular scalar defining function
has the complete sign-preserving normal form. -/
theorem normalForm_of_one_defining
    (S : SmoothManifold 2 .euclidean X) {n : ℕ}
    {A : Set (OpenPartialHomeomorph X Plane)}
    (B : CompactSmoothSeam S) (d : Fin n → ChartDisk X A) (r : Fin n → ℝ)
    (hpos : ∀ i, 0 < r i) (houter : ∀ i, r i ≤ (d i).outerRadius)
    (p : X) (e : ModelChart 2 .euclidean X)
    (he : e ∈ S.smoothStructure.val) (hpe : p ∈ e.source)
    (i₀ : Option (Fin n))
    (hincident : ∀ i, p ∈ arrangementCurve B.carrier d r i ↔ i = i₀)
    (F : LocalDefiningData S (arrangementCurve B.carrier d r i₀) e p)
    (hnegative : ∀ j, i₀ = some j → ∀ x ∈ e.source, (e x).val ∈ F.domain →
      (x ∈ (d j).openAtRadius (r j) ↔ F.function (e x).val < 0))
    (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    Nonempty (ArrangementNormalForm S B.carrier d r p O) := by
  classical
  have hderiv := (F.smooth.contDiffAt (F.isOpen_domain.mem_nhds F.mem_domain)).differentiableAt
    (by simp)
  obtain ⟨c, hc, hpc, hcsub, hcenter, hcU, hcf⟩ :=
    exists_one_defining_coordinateChart S e he p hpe F.function F.domain
      F.isOpen_domain F.smooth F.mem_domain F.zero _ hderiv.hasFDerivAt F.regular
  have hcenter' : coordinates c p = 0 := by
    change toPlane (c p).val = 0
    rw [hcenter, map_zero]
  let axis : Option (Fin n) → Option (Fin 2) := fun i => if i = i₀ then some 0 else none
  apply normalForm_of_chart_axes S B d r hpos houter p c hc hpc hcenter' axis
  · intro i j a hi hj
    by_cases hii : i = i₀
    · by_cases hji : j = i₀
      · exact hii.trans hji.symm
      · simp [axis, hji] at hj
    · simp [axis, hii] at hi
  · intro i
    rw [hincident]
    by_cases hi : i = i₀ <;> simp [axis, hi]
  · intro i a hi x hx
    have hii : i = i₀ := by
      by_contra h
      simp [axis, h] at hi
    subst i
    have ha : a = 0 := by simpa [axis] using hi.symm
    subst a
    change (x ∈ arrangementCurve B.carrier d r i₀ ↔ (c x).val 0 = 0)
    rw [hcf]
    exact F.curve_eq x (hcsub hx) (hcU x hx)
  · intro j a hj x hx
    have hji : some j = i₀ := by
      by_contra h
      simp [axis, h] at hj
    have ha : a = 0 := by simpa [axis, hji] using hj.symm
    subst a
    change (x ∈ (d j).openAtRadius (r j) ↔ (c x).val 0 < 0)
    rw [hcf]
    exact hnegative j hji.symm x (hcsub hx) (hcU x hx)
  · exact hO
  · exact hpO

/-- Two incident curves with transverse genuine defining submersions have a
complete simultaneous normal form. Each circle retains its own negative sign. -/
theorem normalForm_of_two_defining
    (S : SmoothManifold 2 .euclidean X) {n : ℕ}
    {A : Set (OpenPartialHomeomorph X Plane)}
    (B : CompactSmoothSeam S) (d : Fin n → ChartDisk X A) (r : Fin n → ℝ)
    (hpos : ∀ i, 0 < r i) (houter : ∀ i, r i ≤ (d i).outerRadius)
    (p : X) (e : ModelChart 2 .euclidean X)
    (he : e ∈ S.smoothStructure.val) (hpe : p ∈ e.source)
    (i₀ i₁ : Option (Fin n)) (hne : i₀ ≠ i₁)
    (hincident : ∀ i, p ∈ arrangementCurve B.carrier d r i ↔ i = i₀ ∨ i = i₁)
    (F : LocalDefiningData S (arrangementCurve B.carrier d r i₀) e p)
    (G : LocalDefiningData S (arrangementCurve B.carrier d r i₁) e p)
    (hker : LinearMap.ker (fderiv ℝ F.function (e p).val).toLinearMap ⊔
      LinearMap.ker (fderiv ℝ G.function (e p).val).toLinearMap = ⊤)
    (hnegativeF : ∀ j, i₀ = some j → ∀ x ∈ e.source, (e x).val ∈ F.domain →
      (x ∈ (d j).openAtRadius (r j) ↔ F.function (e x).val < 0))
    (hnegativeG : ∀ j, i₁ = some j → ∀ x ∈ e.source, (e x).val ∈ G.domain →
      (x ∈ (d j).openAtRadius (r j) ↔ G.function (e x).val < 0))
    (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    Nonempty (ArrangementNormalForm S B.carrier d r p O) := by
  classical
  have hFderiv := (F.smooth.contDiffAt (F.isOpen_domain.mem_nhds F.mem_domain)).differentiableAt
    (by simp)
  have hGderiv := (G.smooth.contDiffAt (G.isOpen_domain.mem_nhds G.mem_domain)).differentiableAt
    (by simp)
  let U := F.domain ∩ G.domain
  obtain ⟨c, hc, hpc, hcsub, hcU, hcf⟩ := exists_two_defining_coordinateChart S e he p hpe
    F.function G.function U (F.isOpen_domain.inter G.isOpen_domain)
    (F.smooth.mono inter_subset_left) (G.smooth.mono inter_subset_right)
    ⟨F.mem_domain, G.mem_domain⟩ _ _ hFderiv.hasFDerivAt hGderiv.hasFDerivAt
    F.regular G.regular hker
  have hcenter : coordinates c p = 0 := by
    have hzero : (c p).val = 0 := by
      ext a
      fin_cases a
      · exact (hcf p).1.trans F.zero
      · exact (hcf p).2.trans G.zero
    change toPlane (c p).val = 0
    rw [hzero, map_zero]
  let axis : Option (Fin n) → Option (Fin 2) :=
    fun i => if i = i₀ then some 0 else if i = i₁ then some 1 else none
  apply normalForm_of_chart_axes S B d r hpos houter p c hc hpc hcenter axis
  · intro i j a hi hj
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    by_cases hii : i = i₀
    · by_cases hji : j = i₀
      · exact hii.trans hji.symm
      · have hji' : j = i₁ := by
          by_contra h
          simp [axis, hji, h] at hj
        have hi0 : (0 : Fin 2) = a := by simpa [axis, hii] using hi
        have hj1 : (1 : Fin 2) = a := by simpa [axis, hji, hji', hne.symm] using hj
        exact (h01 (hi0.trans hj1.symm)).elim
    · have hii' : i = i₁ := by
        by_contra h
        simp [axis, hii, h] at hi
      by_cases hji : j = i₀
      · have hi1 : (1 : Fin 2) = a := by simpa [axis, hii, hii', hne.symm] using hi
        have hj0 : (0 : Fin 2) = a := by simpa [axis, hji] using hj
        exact (h01 (hj0.trans hi1.symm)).elim
      · have hji' : j = i₁ := by
          by_contra h
          simp [axis, hji, h] at hj
        exact hii'.trans hji'.symm
  · intro i
    rw [hincident]
    by_cases hi : i = i₀
    · simp [axis, hi]
    · by_cases hi' : i = i₁
      · simp [axis, hi', hne.symm]
      · simp [axis, hi, hi']
  · intro i a hi x hx
    by_cases hii : i = i₀
    · subst i
      have ha : a = 0 := by simpa [axis] using hi.symm
      subst a
      change (x ∈ arrangementCurve B.carrier d r i₀ ↔ (c x).val 0 = 0)
      rw [(hcf x).1]
      exact F.curve_eq x (hcsub hx) (hcU x hx).1
    · have hii' : i = i₁ := by
        by_contra h
        simp [axis, hii, h] at hi
      subst i
      have ha : a = 1 := by simpa [axis, hne.symm] using hi.symm
      subst a
      change (x ∈ arrangementCurve B.carrier d r i₁ ↔ (c x).val 1 = 0)
      rw [(hcf x).2]
      exact G.curve_eq x (hcsub hx) (hcU x hx).2
  · intro j a hj x hx
    by_cases hji : some j = i₀
    · have ha : a = 0 := by simpa [axis, hji] using hj.symm
      subst a
      change (x ∈ (d j).openAtRadius (r j) ↔ (c x).val 0 < 0)
      rw [(hcf x).1]
      exact hnegativeF j hji.symm x (hcsub hx) (hcU x hx).1
    · have hji' : some j = i₁ := by
        by_contra h
        simp [axis, hji, h] at hj
      have ha : a = 1 := by simpa [axis, hji, hji', hne.symm] using hj.symm
      subst a
      change (x ∈ (d j).openAtRadius (r j) ↔ (c x).val 1 < 0)
      rw [(hcf x).2]
      exact hnegativeG j hji'.symm x (hcsub hx) (hcU x hx).2
  · exact hO
  · exact hpO

end LocalGeometry

namespace FiniteArrangement
open LocalGeometry
variable {X : Type u} [TopologicalSpace X]

/-- The transverse finite family has exact, sign-preserving local normal
forms at every ambient point, in every prescribed open neighborhood. -/
theorem normal_forms (S : SmoothManifold 2 .euclidean X)
    (A : Set (ModelChart 2 .euclidean X)) (hAS : A ⊆ S.smoothStructure.val)
    (B : CompactSmoothSeam S) {n : ℕ}
    {d : Fin n → ChartDisk X (planeChartFamily A)} (D : Data S B d)
    (p : X) (O : Set X) (hO : IsOpen O) (hpO : p ∈ O) :
    Nonempty (ArrangementNormalForm S B.carrier d D.radius p O) := by
  have hpos : ∀ i, 0 < D.radius i := fun i => (d i).inner_pos.trans (D.bounds i).1
  have houter : ∀ i, D.radius i ≤ (d i).outerRadius := fun i => (D.bounds i).2.le
  rcases incident_cases (arrangementCurve B.carrier d D.radius) p D.no_triple with
    hnone | ⟨i, hpi, hsingle⟩ | ⟨i, j, hij, hpi, hpj, hpair⟩
  · exact normalForm_of_no_incident S B d D.radius hpos houter p hnone O hO hpO
  · obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
    obtain ⟨F, hnegative⟩ := exists_arrangement_curve_localDefiningData
      S hAS B d D.radius hpos houter i p hpi e he hpe
    have hincident : ∀ k, p ∈ arrangementCurve B.carrier d D.radius k ↔ k = i := by
      intro k
      constructor
      · exact hsingle k
      · intro hki
        subst k
        exact hpi
    exact normalForm_of_one_defining S B d D.radius hpos houter p e he hpe
      i hincident F hnegative O hO hpO
  · obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
    obtain ⟨F, hnegativeF⟩ := exists_arrangement_curve_localDefiningData
      S hAS B d D.radius hpos houter i p hpi e he hpe
    obtain ⟨G, hnegativeG⟩ := exists_arrangement_curve_localDefiningData
      S hAS B d D.radius hpos houter j p hpj e he hpe
    have hincident : ∀ k, p ∈ arrangementCurve B.carrier d D.radius k ↔ k = i ∨ k = j := by
      intro k
      constructor
      · exact hpair k
      · rintro (rfl | rfl)
        · exact hpi
        · exact hpj
    have hker := LocalDefiningData.transverse_kernels S (curveManifold S B D i)
      (curveManifold S B D j) (curveEmbedding S B D i).1 (curveEmbedding S B D j).1
      (curve_transverse S B D i j hij) p hpi hpj e he hpe F G
    exact normalForm_of_two_defining S B d D.radius hpos houter p e he hpe
      i j hij hincident F G hker hnegativeF hnegativeG O hO hpO

end FiniteArrangement

/-- Successive Sard selection and local inverse charts construct the full
arrangement from the original compact subset, supplied charts and optional seam. -/
theorem transverseDiskArrangement :
    P202Specs.SurfaceRegionConstruction.Expected.transverseDiskArrangement.{u} := by
  intro X _ S K hK A hAS hcover B
  obtain ⟨n, d, D, hinner, _⟩ :=
    FiniteArrangement.exists_finite_data S K hK A hAS hcover B
  exact ⟨FiniteArrangement.Data.toArrangement S K A B D hinner
    (FiniteArrangement.normal_forms S A hAS B D)⟩


theorem suppliedDiskCover : P202Specs.SurfaceRegionConstruction.Expected.suppliedDiskCover.{u} := by
  intro X _ K hK A hA
  exact finite_supplied_smooth_chartDisk_cover K hK A hA

theorem chartCircleConstruction :
    P202Specs.SurfaceRegionConstruction.Expected.chartCircleConstruction.{u} := by
  intro X _ S A d e he hde r hr houter
  exact SmoothCircles.exists_smoothChartCircle S d e he hde hr houter

end P202.SurfaceRegionConstruction
