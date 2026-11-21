import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.SimplexTriangulation
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions

/-! Geometric simplex and finite triangulation interfaces for Chapter 17.
`GeometricComplex` includes the empty face. `facets` means codimension one;
`maximalCells` means maximal under inclusion. All carriers and distances are
in Euclidean L2 space, including when the simplex has lower ambient dimension.
The independent Specs supply the shared data structures. -/
noncomputable section
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace D10Topology.Ch17

abbrev Euclidean : Specs.D10Topology.Ch17.SimplexTriangulation.EuclideanType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.EuclideanValue

abbrev AffineSimplex : Specs.D10Topology.Ch17.SimplexTriangulation.AffineSimplexType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.AffineSimplexValue

abbrev GeometricComplex : Specs.D10Topology.Ch17.SimplexTriangulation.GeometricComplexType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.GeometricComplexValue

abbrev Triangulation : Specs.D10Topology.Ch17.SimplexTriangulation.TriangulationType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.TriangulationValue

abbrev standardSimplex : Specs.D10Topology.Ch17.SimplexTriangulation.standardSimplexType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.standardSimplexValue

abbrev standardVertex : Specs.D10Topology.Ch17.SimplexTriangulation.standardVertexType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.standardVertexValue

abbrev standardAffineSimplex : Specs.D10Topology.Ch17.SimplexTriangulation.standardAffineSimplexType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.standardAffineSimplexValue

abbrev cellHull : Specs.D10Topology.Ch17.SimplexTriangulation.cellHullType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.cellHullValue

abbrev cellDimension : Specs.D10Topology.Ch17.SimplexTriangulation.cellDimensionType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.cellDimensionValue

abbrev IsFace : Specs.D10Topology.Ch17.SimplexTriangulation.IsFaceType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.IsFaceValue

abbrev simplexHull : Specs.D10Topology.Ch17.SimplexTriangulation.simplexHullType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.simplexHullValue

abbrev simplexFace : Specs.D10Topology.Ch17.SimplexTriangulation.simplexFaceType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.simplexFaceValue

abbrev simplexBoundary : Specs.D10Topology.Ch17.SimplexTriangulation.simplexBoundaryType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.simplexBoundaryValue

abbrev complexSupport : Specs.D10Topology.Ch17.SimplexTriangulation.complexSupportType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.complexSupportValue

abbrev maximalCells : Specs.D10Topology.Ch17.SimplexTriangulation.maximalCellsType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.maximalCellsValue

abbrev vertices : Specs.D10Topology.Ch17.SimplexTriangulation.verticesType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.verticesValue

abbrev topCells : Specs.D10Topology.Ch17.SimplexTriangulation.topCellsType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.topCellsValue

abbrev facets : Specs.D10Topology.Ch17.SimplexTriangulation.facetsType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.facetsValue

abbrev boundaryFacets : Specs.D10Topology.Ch17.SimplexTriangulation.boundaryFacetsType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.boundaryFacetsValue

abbrev internalFacets : Specs.D10Topology.Ch17.SimplexTriangulation.internalFacetsType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.internalFacetsValue

abbrev Incident : Specs.D10Topology.Ch17.SimplexTriangulation.IncidentType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.IncidentValue

abbrev inducedCells : Specs.D10Topology.Ch17.SimplexTriangulation.inducedCellsType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.inducedCellsValue

abbrev cellDiameter : Specs.D10Topology.Ch17.SimplexTriangulation.cellDiameterType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.cellDiameterValue

abbrev mesh : Specs.D10Topology.Ch17.SimplexTriangulation.meshType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.meshValue

abbrev VertexLabeling : Specs.D10Topology.Ch17.SimplexTriangulation.VertexLabelingType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.VertexLabelingValue

abbrev FaceRespecting : Specs.D10Topology.Ch17.SimplexTriangulation.FaceRespectingType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.FaceRespectingValue

abbrev inducedComplex : Specs.D10Topology.Ch17.SimplexTriangulation.inducedComplexType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.inducedComplexValue

abbrev cellLabels : Specs.D10Topology.Ch17.SimplexTriangulation.cellLabelsType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.cellLabelsValue

abbrev FullyLabeled : Specs.D10Topology.Ch17.SimplexTriangulation.FullyLabeledType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.FullyLabeledValue

abbrev fullyLabeledCells : Specs.D10Topology.Ch17.SimplexTriangulation.fullyLabeledCellsType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.fullyLabeledCellsValue

abbrev toMathlib : Specs.D10Topology.Ch17.SimplexTriangulation.toMathlibType :=
  @Specs.D10Topology.Ch17.SimplexTriangulation.toMathlibValue

theorem mem_standardSimplex :
  ∀ (n : ℕ) (x : Euclidean (n + 1)),
  x ∈ standardSimplex n ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := by intros; rfl

theorem standardAffineSimplex_hull :
  ∀ n : ℕ, simplexHull (standardAffineSimplex n) = standardSimplex n := by
  intro n
  let e := (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm
  have hv : (standardAffineSimplex n).points = fun i => e (Pi.single i 1) := by
    funext i
    change EuclideanSpace.basisFun (Fin (n + 1)) ℝ i = _
    rw [EuclideanSpace.basisFun_apply]
    rfl
  change convexHull ℝ (Set.range (standardAffineSimplex n).points) = _
  rw [hv]
  change convexHull ℝ (Set.range (e ∘ fun i => Pi.single i 1)) = _
  rw [Set.range_comp]
  have heq : convexHull ℝ (e '' Set.range (fun i : Fin (n + 1) => Pi.single i (1 : ℝ))) =
      e '' convexHull ℝ (Set.range (fun i : Fin (n + 1) => Pi.single i (1 : ℝ))) :=
    (e.toLinearMap.image_convexHull _).symm
  rw [heq, convexHull_rangle_single_eq_stdSimplex]
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩

theorem simplexFace_empty :
  ∀ {m n : ℕ} (S : AffineSimplex m n), simplexFace S ∅ = ∅ := by
  intros
  simp [simplexFace, Specs.D10Topology.Ch17.SimplexTriangulation.simplexFaceValue]

theorem simplexFace_univ :
  ∀ {m n : ℕ} (S : AffineSimplex m n), simplexFace S Finset.univ = simplexHull S := by
  intros
  simp [simplexFace, simplexHull, Specs.D10Topology.Ch17.SimplexTriangulation.simplexFaceValue,
    Specs.D10Topology.Ch17.SimplexTriangulation.simplexHullValue,
    Specs.D10Topology.Ch17.SimplexTriangulation.simplexHull]

theorem simplexHull_face :
  ∀ {m n : ℕ} (S : AffineSimplex m n) (I : Finset (Fin (n + 1)))
  {k : ℕ} (h : I.card = k + 1), simplexHull (S.face h) = simplexFace S I := by
  intros
  change convexHull ℝ (Set.range _ ) = _
  rw [Affine.Simplex.range_face_points]
  rfl

theorem cellHull_empty :
  ∀ m : ℕ, cellHull (∅ : Finset (Euclidean m)) = ∅ := by
  intro m
  change convexHull ℝ ((∅ : Finset (Euclidean m)) : Set (Euclidean m)) = ∅
  simp

theorem cellHull_mono :
  ∀ {m : ℕ} {s t : Finset (Euclidean m)}, IsFace s t → cellHull s ⊆ cellHull t := by
  intro m s t h
  exact convexHull_mono h

theorem cell_intersection_common_face :
  ∀ {m : ℕ} (K : GeometricComplex m) (s : Finset (Euclidean m)), s ∈ K.cells →
  ∀ t : Finset (Euclidean m), t ∈ K.cells →
    s ∩ t ∈ K.cells ∧ IsFace (s ∩ t) s ∧ IsFace (s ∩ t) t ∧
      cellHull s ∩ cellHull t = cellHull (s ∩ t) := by
  intro m K s hs t ht
  exact ⟨K.face_closed s hs (s ∩ t) Finset.inter_subset_left,
    Finset.inter_subset_left, Finset.inter_subset_right, K.inter_eq s hs t ht⟩

theorem toMathlib_faces :
  ∀ {m : ℕ} (K : GeometricComplex m), (toMathlib K).faces =
  (K.cells : Set (Finset (Euclidean m))) \ {∅} := by intros; rfl

theorem toMathlib_space :
  ∀ {m : ℕ} (K : GeometricComplex m), (toMathlib K).space = complexSupport K := by
  intro m K
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff]
  change (∃ s, s ∈ (K.cells : Set (Finset (Euclidean m))) \ {∅} ∧
    x ∈ cellHull s) ↔ x ∈ ⋃ s ∈ K.cells, cellHull s
  simp only [Set.mem_iUnion, exists_prop, Set.mem_sdiff, Set.mem_singleton_iff,
    Finset.mem_coe]
  constructor
  · rintro ⟨s, ⟨hs, _⟩, hx⟩
    exact ⟨s, hs, hx⟩
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, ⟨hs, ?_⟩, hx⟩
    intro he
    subst s
    simp [cellHull_empty] at hx

theorem triangulation_cover :
  ∀ {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S),
  (toMathlib T.complex).space = simplexHull S := by
  intro m n S T
  rw [toMathlib_space]
  exact T.covers

theorem inducedCells_iff :
  ∀ {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S)
  (I : Finset (Fin (n + 1))) (s : Finset (Euclidean m)),
    s ∈ inducedCells T I ↔ s ∈ T.complex.cells ∧ cellHull s ⊆ simplexFace S I := by
  intro m n S T I s
  change (s ∈ T.complex.cells.filter _) ↔ _
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hs, hsub⟩
    exact ⟨hs, convexHull_min hsub (convex_convexHull ℝ _)⟩
  · rintro ⟨hs, hsub⟩
    exact ⟨hs, (subset_convexHull ℝ _).trans hsub⟩

theorem inducedComplex_cells :
  ∀ {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S)
  (I : Finset (Fin (n + 1))), (inducedComplex T I).cells = inducedCells T I := by intros; rfl

theorem cellHull_bounded :
  ∀ {m : ℕ} (s : Finset (Euclidean m)), Bornology.IsBounded (cellHull s) := by
  intro m s
  exact isBounded_convexHull.mpr s.finite_toSet.isBounded

theorem cellDiameter_eq_vertex_diameter :
  ∀ {m : ℕ} (s : Finset (Euclidean m)), cellDiameter s = Metric.diam (s : Set (Euclidean m)) := by
  intro m s
  exact convexHull_diam _

theorem cellDiameter_eq_extended :
  ∀ {m : ℕ} (s : Finset (Euclidean m)),
  ENNReal.ofReal (cellDiameter s) =
    Specs.D10Topology.Ch09.MetricConventions.diameter
      (inferInstance : PseudoMetricSpace (Euclidean m)) (cellHull s) := by
  intro m s
  change ENNReal.ofReal (cellDiameter s) = D10Topology.Ch09.diameter
    (inferInstance : PseudoMetricSpace (Euclidean m)) (cellHull s)
  rw [D10Topology.Ch09.diameter_eq_mathlib]
  change ENNReal.ofReal (Metric.ediam (cellHull s)).toReal = Metric.ediam (cellHull s)
  exact ENNReal.ofReal_toReal (cellHull_bounded s).ediam_ne_top

theorem cellDiameter_le_mesh :
  ∀ {m : ℕ} (K : GeometricComplex m) (s : Finset (Euclidean m)),
  s ∈ K.cells → cellDiameter s ≤ mesh K := by
  intro m K s hs
  exact Finset.le_sup' _ hs

theorem mesh_attained :
  ∀ {m : ℕ} (K : GeometricComplex m), ∃ s ∈ K.cells, mesh K = cellDiameter s := by
  intro m K
  exact Finset.exists_mem_eq_sup' _ _

theorem dist_le_mesh :
  ∀ {m : ℕ} (K : GeometricComplex m) (s : Finset (Euclidean m)), s ∈ K.cells →
  ∀ x ∈ cellHull s, ∀ y ∈ cellHull s, dist x y ≤ mesh K := by
  intro m K s hs x hx y hy
  exact (Metric.dist_le_diam_of_mem (cellHull_bounded s) hx hy).trans
    (cellDiameter_le_mesh K s hs)

theorem cellDimension_eq_finrank :
  ∀ {m : ℕ} (K : GeometricComplex m) (s : Finset (Euclidean m)),
  s ∈ K.cells → s.Nonempty →
    cellDimension s = (Module.finrank ℝ (vectorSpan ℝ (s : Set (Euclidean m))) : ℤ) := by
  intro m K s hs hne
  have : Nonempty s := hne.to_subtype
  have hr : Set.range ((↑) : s → Euclidean m) = (s : Set (Euclidean m)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hf := congrArg (fun A : Set (Euclidean m) => Module.finrank ℝ (vectorSpan ℝ A)) hr
  have h := (K.independent s hs).finrank_vectorSpan_add_one
  simp only [Fintype.card_coe] at h
  rw [hf] at h
  change (s.card : ℤ) - 1 = _
  omega

theorem maximal_cell_dimension :
  ∀ {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S)
  (s : Finset (Euclidean m)), s ∈ maximalCells T.complex → cellDimension s = (n : ℤ) := by
  intro m n S T s hs
  have h := T.pure s hs
  change (s.card : ℤ) - 1 = _
  rw [h]
  simp

theorem boundary_internal_partition :
  ∀ {m n : ℕ} {S : AffineSimplex m n} (T : Triangulation S),
  Disjoint (boundaryFacets T) (internalFacets T) ∧
    boundaryFacets T ∪ internalFacets T = facets T := by
  intro m n S T
  change Disjoint ((facets T).filter _) (facets T \ (facets T).filter _) ∧ _
  exact ⟨Finset.disjoint_left.mpr (fun a ha hb => (Finset.mem_sdiff.mp hb).2 ha), Finset.union_sdiff_of_subset (Finset.filter_subset _ _)⟩

theorem face_iff_hull_subset {m : ℕ} (K : GeometricComplex m) (s t : Finset (Euclidean m))
    (hs : s ∈ K.cells) (ht : t ∈ K.cells) :
    IsFace s t ↔ cellHull s ⊆ cellHull t := by
  classical
  by_cases hs0 : s = ∅
  · subst s
    constructor
    · exact cellHull_mono
    · intro _
      exact Finset.empty_subset _
  by_cases ht0 : t = ∅
  · subst t
    constructor
    · exact cellHull_mono
    · intro h
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hs0
      have hh := h (subset_convexHull ℝ (s : Set (Euclidean m)) hx)
      rw [cellHull_empty] at hh
      exact False.elim hh
  have hs' : s ∈ (toMathlib K).faces := ⟨hs, hs0⟩
  have ht' : t ∈ (toMathlib K).faces := ⟨ht, ht0⟩
  exact (Geometry.SimplicialComplex.face_subset_face_iff hs' ht').symm

theorem intersection_iff_common_face {m : ℕ} (s t : Finset (Euclidean m)) :
    cellHull s ∩ cellHull t = cellHull (s ∩ t) ↔
      ∃ u : Finset (Euclidean m), IsFace u s ∧ IsFace u t ∧
        cellHull s ∩ cellHull t = cellHull u := by
  classical
  constructor
  · intro h
    exact ⟨s ∩ t, Finset.inter_subset_left, Finset.inter_subset_right, h⟩
  · rintro ⟨u, hus, hut, h⟩
    apply le_antisymm
    · rw [h]
      exact cellHull_mono (Finset.subset_inter hus hut)
    · change convexHull ℝ ((s ∩ t : Finset (Euclidean m)) : Set (Euclidean m)) ⊆ _
      rw [Finset.coe_inter]
      exact subset_inter (convexHull_mono Set.inter_subset_left)
        (convexHull_mono Set.inter_subset_right)


end D10Topology.Ch17
