import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalGaussBonnetLocalization

/-!
Independent geometric refinement interface for paper.tex 5053–5076 and 5107–5117.
All occurrences are literal arcs of the given regional and boundary presentations.
The finite subdivision is expressed here directly; no implementation-level
`FiniteGap`, arrangement provenance, normal or curvature certificate is imported.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.BoundaryData
open P202.MetricData P202.SurfaceBoundaryData
open P202Specs.SurfaceRegionConstruction P202Specs.SurfaceRegionsEuler
open P202Specs.PlanarRegionTopology P202Specs.GlobalGaussBonnet
universe u

namespace P202Specs.RegionalBoundaryRefinement
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

abbrev Presentations (D : RegionDecomposition S) :=
  ∀ (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount),
    P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i)

/-- Actual regular arcs in the original tangent fibers, with the literal
assigned chart coordinates. Regularity at both endpoints comes from A.
No endpoint regularity of the original graph parametrizations is required. -/
structure RegionalRepresentatives (g : RiemannianMetric S)
    (D : RegionDecomposition S) (A : Presentations D) where
  arc : ∀ (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount),
    Fin (A j i).count → RegularArc g
  left : ∀ j i k, (arc j i k).left = 0
  right : ∀ j i k, (arc j i k).right = 1
  literal : ∀ j i k t, t ∈ Icc (0 : ℝ) 1 →
    (arc j i k).curve t ∈ regionClosure D j ∩ D.graph.carrier ∧
    (arc j i k).curve t ∈ (D.chart j).source ∧
    coordinates (D.chart j) ((arc j i k).curve t) = (A j i).arc k t
  injective : ∀ j i k, InjOn (arc j i k).curve (Ioo (0 : ℝ) 1)
  embedding : ∀ j i k, Topology.IsEmbedding
    (fun t : Ioo (0 : ℝ) 1 => (arc j i k).curve t.val)
  disjoint : ∀ j, Pairwise
    (fun a b : Σ i : Fin (D.region j).boundaryCount, Fin (A j i).count =>
      Disjoint ((arc j a.1 a.2).curve '' Ioo (0 : ℝ) 1)
        ((arc j b.1 b.2).curve '' Ioo (0 : ℝ) 1))

abbrev RegionalIndex (D : RegionDecomposition S) (A : Presentations D) :=
  Σ j : Fin D.regionCount, Σ i : Fin (D.region j).boundaryCount, Fin (A j i).count

abbrev Occurrence {g : RiemannianMetric S} {D : RegionDecomposition S}
    (A : Presentations D) (B : BoundaryPresentation g) :=
  RegionalIndex D A ⊕ Fin B.count

def occurrenceArc {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) : Occurrence A B → RegularArc g
  | .inl ⟨j, i, k⟩ => R.arc j i k
  | .inr b => B.arc b

/-- The exact indices of regional closures through an original surface point. -/
def incidentRegions (D : RegionDecomposition S) (p : M) : Set (Fin D.regionCount) :=
  {j | p ∈ regionClosure D j}

/-- Simultaneous subdivision, covering every open parameter interval away from
its finite cuts. All pieces are nontrivial and remain in their original intervals.
A mate is another occurrence of the identical trace, rather than an identification
of parameter values or a multiplicity-free union of the original curves. -/
structure FiniteSubdivision {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) where
  cuts : Occurrence A B → Finset ℝ
  cuts_left : ∀ o, (occurrenceArc R B o).left ∈ cuts o
  cuts_right : ∀ o, (occurrenceArc R B o).right ∈ cuts o
  cuts_bounds : ∀ o, (cuts o : Set ℝ) ⊆
    Icc (occurrenceArc R B o).left (occurrenceArc R B o).right
  cuts_vertices : ∀ o t, t ∈ Icc (occurrenceArc R B o).left (occurrenceArc R B o).right →
    (occurrenceArc R B o).curve t ∈ range D.graph.vertex → t ∈ cuts o
  cuts_endpoints : ∀ o t,
    t ∈ Icc (occurrenceArc R B o).left (occurrenceArc R B o).right →
    ∀ z, ((occurrenceArc R B o).curve t =
      (occurrenceArc R B z).curve (occurrenceArc R B z).left ∨
      (occurrenceArc R B o).curve t =
      (occurrenceArc R B z).curve (occurrenceArc R B z).right) → t ∈ cuts o
  cuts_joins : ∀ o t,
    t ∈ Icc (occurrenceArc R B o).left (occurrenceArc R B o).right →
    ∀ j i q, q ∈ ((D.region j).curve i).joins →
      (occurrenceArc R B o).curve t ∈ (D.chart j).source →
      coordinates (D.chart j) ((occurrenceArc R B o).curve t) =
        ((D.region j).curve i).parametrization q → t ∈ cuts o
  count : ℕ
  occurrence : Fin count → Occurrence A B
  left : Fin count → ℝ
  right : Fin count → ℝ
  ordered : ∀ h, left h < right h
  left_cut : ∀ h, left h ∈ cuts (occurrence h)
  right_cut : ∀ h, right h ∈ cuts (occurrence h)
  cut_free : ∀ h t, t ∈ Ioo (left h) (right h) → t ∉ cuts (occurrence h)
  disjoint : ∀ h k, h ≠ k → occurrence h = occurrence k →
    Disjoint (Ioo (left h) (right h)) (Ioo (left k) (right k))
  covers : ∀ o t, t ∈ Ioo (occurrenceArc R B o).left (occurrenceArc R B o).right →
    t ∉ cuts o → ∃ h, occurrence h = o ∧ t ∈ Ioo (left h) (right h)

/-- A finite subdivision together with exact geometric mates and occupied germs. -/
structure CommonRefinement {g : RiemannianMetric S} {D : RegionDecomposition S}
    {A : Presentations D} (R : RegionalRepresentatives g D A)
    (B : BoundaryPresentation g) extends FiniteSubdivision R B where
  mate : Fin count → Fin count
  involutive : Function.Involutive mate
  fixed_point_free : ∀ h, mate h ≠ h
  no_boundary_boundary : ∀ h b c,
    occurrence h = .inr b → occurrence (mate h) ≠ .inr c
  edge : Fin count → Fin D.graph.edgeCount
  edge_mate : ∀ h, edge (mate h) = edge h
  in_edge : ∀ h, (occurrenceArc R B (occurrence h)).curve '' Ioo (left h) (right h) ⊆
    D.graph.edge (edge h) '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
  trace_eq : ∀ h,
    (occurrenceArc R B (occurrence h)).curve '' Ioo (left h) (right h) =
      (occurrenceArc R B (occurrence (mate h))).curve '' Ioo (left (mate h)) (right (mate h))
  transition : Fin count → ℝ → ℝ
  continuous : ∀ h, ContinuousOn (transition h) (Icc (left h) (right h))
  monotone : ∀ h, StrictMonoOn (transition h) (Icc (left h) (right h)) ∨
    StrictAntiOn (transition h) (Icc (left h) (right h))
  image_open : ∀ h, transition h '' Ioo (left h) (right h) =
    Ioo (left (mate h)) (right (mate h))
  image_closed : ∀ h, transition h '' Icc (left h) (right h) =
    Icc (left (mate h)) (right (mate h))
  point_eq : ∀ h t, t ∈ Icc (left h) (right h) →
    (occurrenceArc R B (occurrence h)).curve t =
      (occurrenceArc R B (occurrence (mate h))).curve (transition h t)
  hasDerivAt : ∀ h t, t ∈ Ioo (left h) (right h) →
    HasDerivAt (transition h) (deriv (transition h) t) t
  derivative_sign : ∀ h,
    (∀ t ∈ Ioo (left h) (right h), 0 < deriv (transition h) t) ∨
    (∀ t ∈ Ioo (left h) (right h), deriv (transition h) t < 0)
  interior_incidence : ∀ h j i k j' i' k',
    occurrence h = .inl ⟨j, i, k⟩ → occurrence (mate h) = .inl ⟨j', i', k'⟩ →
    j ≠ j' ∧ ∀ p ∈ (occurrenceArc R B (occurrence h)).curve '' Ioo (left h) (right h),
      p ∉ intrinsicBoundary S ∧ incidentRegions D p = {j, j'} ∧
        regionClosure D j ∪ regionClosure D j' ∈ 𝓝 p
  boundary_incidence : ∀ h j i k b,
    occurrence h = .inl ⟨j, i, k⟩ → occurrence (mate h) = .inr b →
    ∀ p ∈ (occurrenceArc R B (occurrence h)).curve '' Ioo (left h) (right h),
      p ∈ intrinsicBoundary S ∧ incidentRegions D p = {j} ∧ regionClosure D j ∈ 𝓝 p

namespace Expected

def regionalRepresentatives : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold 2 kind M) (g : RiemannianMetric S)
    (D : RegionDecomposition S) (A : Presentations D),
    Nonempty (RegionalRepresentatives g D A)

/-- All finite cuts and their exact parameter-interval partition, before pairing. -/
def finiteSubdivision : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold 2 kind M) (g : RiemannianMetric S)
    (D : RegionDecomposition S) (A : Presentations D) (B : BoundaryPresentation g),
    ∃ R : RegionalRepresentatives g D A, Nonempty (FiniteSubdivision R B)

/-- The full assigned obligation. No incidence, occupied-side, endpoint-germ,
orientation, connection, normal, curvature or integral premise is introduced. -/
def commonRefinement : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold 2 kind M) (g : RiemannianMetric S)
    (D : RegionDecomposition S) (A : Presentations D) (B : BoundaryPresentation g),
    ∃ R : RegionalRepresentatives g D A, Nonempty (CommonRefinement R B)

end Expected
end P202Specs.RegionalBoundaryRefinement
