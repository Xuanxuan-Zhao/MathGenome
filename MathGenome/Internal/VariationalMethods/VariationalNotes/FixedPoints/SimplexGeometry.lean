import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.FixedPoints.SimplexGeometry

/-! Shared specializations of the finite geometric triangulation interface.
The standard simplex uses d+1 nonnegative coordinates summing to one, in the
Euclidean L2 metric. Faces, labels and mesh reuse the same geometric objects. -/
noncomputable section
open Set
open scoped BigOperators
namespace VariationalNotes.FixedPoints.SimplexGeometry

abbrev Point : Specs.VariationalNotes.FixedPoints.SimplexGeometry.PointType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.Point

abbrev Cell : Specs.VariationalNotes.FixedPoints.SimplexGeometry.CellType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.Cell

abbrev standardSimplex : Specs.VariationalNotes.FixedPoints.SimplexGeometry.standardSimplexType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.standardSimplex

abbrev standardVertex : Specs.VariationalNotes.FixedPoints.SimplexGeometry.standardVertexType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.standardVertex

abbrev standardAffineSimplex : Specs.VariationalNotes.FixedPoints.SimplexGeometry.standardAffineSimplexType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.standardAffineSimplex

abbrev face : Specs.VariationalNotes.FixedPoints.SimplexGeometry.faceType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.face

abbrev GeometricComplex : Specs.VariationalNotes.FixedPoints.SimplexGeometry.GeometricComplexType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.GeometricComplex

abbrev Triangulation : Specs.VariationalNotes.FixedPoints.SimplexGeometry.TriangulationType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.Triangulation

abbrev cellHull : Specs.VariationalNotes.FixedPoints.SimplexGeometry.cellHullType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.cellHull

abbrev cellDiameter : Specs.VariationalNotes.FixedPoints.SimplexGeometry.cellDiameterType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.cellDiameter

abbrev mesh : Specs.VariationalNotes.FixedPoints.SimplexGeometry.meshType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.mesh

abbrev vertices : Specs.VariationalNotes.FixedPoints.SimplexGeometry.verticesType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.vertices

abbrev Vertex : Specs.VariationalNotes.FixedPoints.SimplexGeometry.VertexType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.Vertex

abbrev topCells : Specs.VariationalNotes.FixedPoints.SimplexGeometry.topCellsType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.topCells

abbrev inducedComplex : Specs.VariationalNotes.FixedPoints.SimplexGeometry.inducedComplexType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.inducedComplex

abbrev VertexLabeling : Specs.VariationalNotes.FixedPoints.SimplexGeometry.VertexLabelingType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.VertexLabeling

abbrev FaceRespecting : Specs.VariationalNotes.FixedPoints.SimplexGeometry.FaceRespectingType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.FaceRespecting

abbrev SpernerLabeling : Specs.VariationalNotes.FixedPoints.SimplexGeometry.SpernerLabelingType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.SpernerLabeling

abbrev FullyLabeled : Specs.VariationalNotes.FixedPoints.SimplexGeometry.FullyLabeledType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.FullyLabeled

abbrev fullyLabeledCells : Specs.VariationalNotes.FixedPoints.SimplexGeometry.fullyLabeledCellsType :=
  @Specs.VariationalNotes.FixedPoints.SimplexGeometry.fullyLabeledCells

theorem mem_standardSimplex (d : ℕ) (x : Point d) :
    x ∈ standardSimplex d ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := Iff.rfl

/-- A face consists exactly of simplex points whose excluded coordinates vanish. -/
theorem mem_face (d : ℕ) (I : Finset (Fin (d + 1))) (x : Point d) :
    x ∈ face d I ↔ x ∈ standardSimplex d ∧ ∀ i, i ∉ I → x i = 0 := by
  classical
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · change x ∈ D10Topology.Ch17.standardSimplex d
      rw [← D10Topology.Ch17.standardAffineSimplex_hull]
      exact convexHull_mono (Set.image_subset_range _ _) hx
    · intro i hi
      apply convexHull_min (t := {y : Point d | y i = 0}) ?_ ?_ hx
      · rintro _ ⟨j, hj, rfl⟩
        have hji : j ≠ i := fun h => hi (h ▸ hj)
        change EuclideanSpace.basisFun (Fin (d + 1)) ℝ j i = 0
        simp [EuclideanSpace.basisFun_apply, hji]
      · exact convex_hyperplane (EuclideanSpace.projₗ i).isLinear 0
  · rintro ⟨hx, hz⟩
    have hsum : ∑ i ∈ I, x i = 1 := by
      rw [← hx.2]
      exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hz i hi)
    have hrepr : ∑ i ∈ I, x i • standardVertex d i = x := by
      apply PiLp.ext
      intro j
      by_cases hj : j ∈ I
      · simp [standardVertex, Specs.VariationalNotes.FixedPoints.SimplexGeometry.standardVertex,
          D10Topology.Ch17.standardVertex,
          Specs.D10Topology.Ch17.SimplexTriangulation.standardVertexValue,
          EuclideanSpace.basisFun_apply, hj, Pi.single_apply]
      · simp [standardVertex, Specs.VariationalNotes.FixedPoints.SimplexGeometry.standardVertex,
          D10Topology.Ch17.standardVertex,
          Specs.D10Topology.Ch17.SimplexTriangulation.standardVertexValue,
          EuclideanSpace.basisFun_apply, hj, hz j hj, Pi.single_apply]
    rw [← hrepr]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hx.1 i) hsum
      (fun i hi => subset_convexHull ℝ _ ⟨i, hi, rfl⟩)

theorem vertex_mem_standardSimplex {d : ℕ} (T : Triangulation d) (v : Vertex T) :
    v.val ∈ standardSimplex d := by
  obtain ⟨s, hs, hv⟩ := Finset.mem_biUnion.mp v.property
  change v.val ∈ D10Topology.Ch17.standardSimplex d
  rw [← D10Topology.Ch17.standardAffineSimplex_hull]
  apply T.covers.subset
  exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hs,
    subset_convexHull ℝ (s : Set (Point d)) hv⟩⟩

/-- This equivalence does not require positive dimension. -/
theorem spernerLabeling_iff_faceRespecting {d : ℕ} (T : Triangulation d)
    (ℓ : VertexLabeling T) : SpernerLabeling T ℓ ↔ FaceRespecting T ℓ := by
  classical
  constructor
  · intro h I v hv
    by_contra hi
    have hz := ((mem_face d I v.val).mp hv).2 (ℓ v) hi
    exact (ne_of_gt (h v)) hz
  · intro h v
    have hx := vertex_mem_standardSimplex T v
    apply lt_of_le_of_ne (hx.1 (ℓ v))
    intro hz
    have hv : v.val ∈ face d (Finset.univ.erase (ℓ v)) := by
      apply (mem_face _ _ _).mpr
      refine ⟨hx, ?_⟩
      intro i hi
      have he : i = ℓ v := by simpa using hi
      simpa [he] using hz.symm
    have hm := h (Finset.univ.erase (ℓ v)) v hv
    simp at hm

theorem mesh_attained {d : ℕ} (T : Triangulation d) :
    ∃ s ∈ T.complex.cells, mesh T = cellDiameter s :=
  D10Topology.Ch17.mesh_attained T.complex

theorem dist_le_mesh {d : ℕ} (T : Triangulation d) (s : Cell d) (hs : s ∈ T.complex.cells)
    (x : Point d) (hx : x ∈ cellHull s) (y : Point d) (hy : y ∈ cellHull s) :
    dist x y ≤ mesh T :=
  D10Topology.Ch17.dist_le_mesh T.complex s hs x hx y hy

theorem fullyLabeled_iff {d : ℕ} (T : Triangulation d) (ℓ : VertexLabeling T) (s : Cell d) :
    FullyLabeled T ℓ s ↔ s ∈ topCells T ∧
      ∀ i : Fin (d + 1), ∃ v : Vertex T, v.val ∈ s ∧ ℓ v = i := by
  classical
  constructor
  · rintro ⟨hs, hcard, hl⟩
    refine ⟨Finset.mem_filter.mpr ⟨hs, hcard⟩, ?_⟩
    intro i
    have hi : i ∈ Specs.D10Topology.Ch17.SimplexTriangulation.cellLabels T ℓ s hs := by
      rw [hl]
      exact Finset.mem_univ i
    change i ∈ s.attach.image _ at hi
    obtain ⟨v, _, hvi⟩ := Finset.mem_image.mp hi
    exact ⟨⟨v.val, Finset.mem_biUnion.mpr ⟨s, hs, v.property⟩⟩, v.property, hvi⟩
  · rintro ⟨htop, hl⟩
    obtain ⟨hs, hc⟩ := Finset.mem_filter.mp htop
    refine ⟨hs, hc, Finset.eq_univ_of_forall ?_⟩
    intro i
    obtain ⟨v, hv, hi⟩ := hl i
    change i ∈ s.attach.image _
    exact Finset.mem_image.mpr ⟨⟨v.val, hv⟩, Finset.mem_attach _ _, hi⟩

end VariationalNotes.FixedPoints.SimplexGeometry
