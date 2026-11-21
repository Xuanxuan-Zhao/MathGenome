import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.SimplexTriangulation

/-! Canonical Euclidean simplex geometry for paper.tex §v10-01 (4589–4594).
Cells are actual finite sets of Euclidean points. The imported triangulation
requires affine independence, closure under faces, exact convex-hull intersections,
coverage and purity. No incidence, parity or subdivision conclusion is assumed.
The empty face is included; all dimensions d : ℕ, including zero, are allowed. -/
noncomputable section
open scoped BigOperators
namespace Specs.VariationalNotes.FixedPoints.SimplexGeometry

abbrev PointType := ℕ → Type
abbrev Point : PointType := fun d => D10Topology.Ch17.Euclidean (d + 1)

abbrev CellType := ℕ → Type
abbrev Cell : CellType := fun d => Finset (Point d)

abbrev standardSimplexType := (d : ℕ) → Set (Point d)
abbrev standardSimplex : standardSimplexType := D10Topology.Ch17.standardSimplex

abbrev standardVertexType := (d : ℕ) → Fin (d + 1) → Point d
abbrev standardVertex : standardVertexType := D10Topology.Ch17.standardVertex

abbrev standardAffineSimplexType := (d : ℕ) → D10Topology.Ch17.AffineSimplex (d + 1) d
abbrev standardAffineSimplex : standardAffineSimplexType := D10Topology.Ch17.standardAffineSimplex

abbrev faceType := (d : ℕ) → Finset (Fin (d + 1)) → Set (Point d)
abbrev face : faceType := fun d I => D10Topology.Ch17.simplexFace (standardAffineSimplex d) I

abbrev GeometricComplexType := ℕ → Type
abbrev GeometricComplex : GeometricComplexType := fun d => D10Topology.Ch17.GeometricComplex (d + 1)

abbrev TriangulationType := ℕ → Type
abbrev Triangulation : TriangulationType := fun d => D10Topology.Ch17.Triangulation (standardAffineSimplex d)

abbrev cellHullType := {d : ℕ} → Cell d → Set (Point d)
abbrev cellHull : cellHullType := fun s => D10Topology.Ch17.cellHull s

abbrev cellDiameterType := {d : ℕ} → Cell d → ℝ
abbrev cellDiameter : cellDiameterType := fun s => D10Topology.Ch17.cellDiameter s

abbrev meshType := {d : ℕ} → Triangulation d → ℝ
abbrev mesh : meshType := fun T => D10Topology.Ch17.mesh T.complex

abbrev verticesType := {d : ℕ} → Triangulation d → Finset (Point d)
abbrev vertices : verticesType := fun T => D10Topology.Ch17.vertices T.complex

abbrev VertexType := {d : ℕ} → Triangulation d → Type
abbrev Vertex : VertexType := fun T => {v : Point _ // v ∈ vertices T}

abbrev topCellsType := {d : ℕ} → Triangulation d → Finset (Cell d)
abbrev topCells : topCellsType := fun T => D10Topology.Ch17.topCells T

abbrev inducedComplexType := {d : ℕ} → Triangulation d → Finset (Fin (d + 1)) → GeometricComplex d
abbrev inducedComplex : inducedComplexType := fun T I => D10Topology.Ch17.inducedComplex T I

abbrev VertexLabelingType := {d : ℕ} → Triangulation d → Type
abbrev VertexLabeling : VertexLabelingType := fun {d} T => Vertex T → Fin (d + 1)

abbrev FaceRespectingType := {d : ℕ} → (T : Triangulation d) → VertexLabeling T → Prop
abbrev FaceRespecting : FaceRespectingType := fun T ℓ => D10Topology.Ch17.FaceRespecting T ℓ

abbrev SpernerLabelingType := {d : ℕ} → (T : Triangulation d) → VertexLabeling T → Prop
abbrev SpernerLabeling : SpernerLabelingType := fun T ℓ => ∀ v : Vertex T, 0 < v.val (ℓ v)

abbrev FullyLabeledType := {d : ℕ} → (T : Triangulation d) → VertexLabeling T → Cell d → Prop
abbrev FullyLabeled : FullyLabeledType := fun T ℓ s => D10Topology.Ch17.FullyLabeled T ℓ s

abbrev fullyLabeledCellsType := {d : ℕ} → (T : Triangulation d) → VertexLabeling T → Finset (Cell d)
abbrev fullyLabeledCells : fullyLabeledCellsType := fun T ℓ => D10Topology.Ch17.fullyLabeledCells T ℓ

def mem_standardSimplex : Prop :=
  ∀ (d : ℕ) (x : Point d),
  x ∈ standardSimplex d ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

def mem_face : Prop :=
  ∀ (d : ℕ) (I : Finset (Fin (d + 1))) (x : Point d),
  x ∈ face d I ↔ x ∈ standardSimplex d ∧ ∀ i, i ∉ I → x i = 0

def vertex_mem_standardSimplex : Prop :=
  ∀ {d : ℕ} (T : Triangulation d) (v : Vertex T), v.val ∈ standardSimplex d

def spernerLabeling_iff_faceRespecting : Prop :=
  ∀ {d : ℕ} (T : Triangulation d) (ℓ : VertexLabeling T),
  SpernerLabeling T ℓ ↔ FaceRespecting T ℓ

def mesh_attained : Prop :=
  ∀ {d : ℕ} (T : Triangulation d),
  ∃ s ∈ T.complex.cells, mesh T = cellDiameter s

def dist_le_mesh : Prop :=
  ∀ {d : ℕ} (T : Triangulation d) (s : Cell d), s ∈ T.complex.cells →
  ∀ x ∈ cellHull s, ∀ y ∈ cellHull s, dist x y ≤ mesh T

def fullyLabeled_iff : Prop :=
  ∀ {d : ℕ} (T : Triangulation d) (ℓ : VertexLabeling T) (s : Cell d),
  FullyLabeled T ℓ s ↔ s ∈ topCells T ∧
    ∀ i : Fin (d + 1), ∃ v : Vertex T, v.val ∈ s ∧ ℓ v = i

end Specs.VariationalNotes.FixedPoints.SimplexGeometry
