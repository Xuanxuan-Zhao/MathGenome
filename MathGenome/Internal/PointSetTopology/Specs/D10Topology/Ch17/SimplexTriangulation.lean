import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions

/-! Independent geometric definitions for paper.tex, d10:17:simplex.
The ambient metric is the Euclidean L2 metric. Empty vertex sets represent
empty faces, of dimension -1. Incidence is vertex inclusion, and all cell
realizations are actual convex hulls in the ambient Euclidean space.
No facet-incidence, parity, or subdivision conclusion is assumed here. -/
noncomputable section
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Specs.D10Topology.Ch17.SimplexTriangulation

abbrev Euclidean (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev AffineSimplex (m n : ℕ) := Affine.Simplex ℝ (Euclidean m) n

def cellHull {m : ℕ} (s : Finset (Euclidean m)) : Set (Euclidean m) :=
  convexHull ℝ (s : Set (Euclidean m))

/-- Finite geometric complexes, with the empty face included. The intersection
field refers to geometric convex hulls, not just combinatorial intersections. -/
structure GeometricComplexData (m : ℕ) where
  cells : Finset (Finset (Euclidean m))
  empty_mem : ∅ ∈ cells
  independent : ∀ s ∈ cells, AffineIndependent ℝ ((↑) : s → Euclidean m)
  face_closed : ∀ s ∈ cells, ∀ t, t ⊆ s → t ∈ cells
  inter_eq : ∀ s ∈ cells, ∀ t ∈ cells,
    cellHull s ∩ cellHull t = cellHull (s ∩ t)

def simplexHull {m n : ℕ} (S : AffineSimplex m n) : Set (Euclidean m) :=
  convexHull ℝ (Set.range S.points)

def complexSupport {m : ℕ} (K : GeometricComplexData m) : Set (Euclidean m) :=
  ⋃ s ∈ K.cells, cellHull s

def maximalCells {m : ℕ} (K : GeometricComplexData m) : Finset (Finset (Euclidean m)) :=
  K.cells.filter (fun s => ∀ t ∈ K.cells, s ⊆ t → s = t)

/-- A finite triangulation of an affine n-simplex. Purity concerns maximal cells;
no pseudomanifold, incidence count, or labeling conclusion is a field. -/
structure TriangulationData {m n : ℕ} (S : AffineSimplex m n) where
  complex : GeometricComplexData m
  covers : complexSupport complex = simplexHull S
  pure : ∀ s ∈ maximalCells complex, s.card = n + 1

abbrev EuclideanType := ℕ → Type
abbrev EuclideanValue : EuclideanType := Euclidean

abbrev AffineSimplexType := ℕ → ℕ → Type
abbrev AffineSimplexValue : AffineSimplexType := AffineSimplex

abbrev GeometricComplexType := ℕ → Type
abbrev GeometricComplexValue : GeometricComplexType := GeometricComplexData

abbrev TriangulationType := {m n : ℕ} → AffineSimplex m n → Type
abbrev TriangulationValue : TriangulationType := fun S => TriangulationData S

abbrev standardSimplexType := (n : ℕ) → Set (Euclidean (n + 1))
noncomputable def standardSimplexValue : standardSimplexType := fun n => {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1}

abbrev standardVertexType := (n : ℕ) → Fin (n + 1) → Euclidean (n + 1)
noncomputable def standardVertexValue : standardVertexType := fun n => EuclideanSpace.basisFun (Fin (n + 1)) ℝ

abbrev standardAffineSimplexType := (n : ℕ) → AffineSimplex (n + 1) n
noncomputable def standardAffineSimplexValue : standardAffineSimplexType := fun n => ⟨standardVertexValue n, (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.linearIndependent.affineIndependent⟩

abbrev cellHullType := {m : ℕ} → Finset (Euclidean m) → Set (Euclidean m)
noncomputable def cellHullValue : cellHullType := cellHull

abbrev cellDimensionType := {m : ℕ} → Finset (Euclidean m) → ℤ
noncomputable def cellDimensionValue : cellDimensionType := fun s => (s.card : ℤ) - 1

abbrev IsFaceType := {m : ℕ} → Finset (Euclidean m) → Finset (Euclidean m) → Prop
noncomputable def IsFaceValue : IsFaceType := fun s t => s ⊆ t

abbrev simplexHullType := {m n : ℕ} → AffineSimplex m n → Set (Euclidean m)
noncomputable def simplexHullValue : simplexHullType := simplexHull

abbrev simplexFaceType := {m n : ℕ} → AffineSimplex m n → Finset (Fin (n + 1)) → Set (Euclidean m)
noncomputable def simplexFaceValue : simplexFaceType := fun S I => convexHull ℝ (S.points '' (I : Set (Fin (_ + 1))))

abbrev simplexBoundaryType := {m n : ℕ} → AffineSimplex m n → Set (Euclidean m)
noncomputable def simplexBoundaryValue : simplexBoundaryType := fun S => ⋃ i, simplexFaceValue S (Finset.univ.erase i)

abbrev complexSupportType := {m : ℕ} → GeometricComplexData m → Set (Euclidean m)
noncomputable def complexSupportValue : complexSupportType := complexSupport

abbrev maximalCellsType := {m : ℕ} → GeometricComplexData m → Finset (Finset (Euclidean m))
noncomputable def maximalCellsValue : maximalCellsType := maximalCells

abbrev verticesType := {m : ℕ} → GeometricComplexData m → Finset (Euclidean m)
noncomputable def verticesValue : verticesType := fun K => K.cells.biUnion id

abbrev topCellsType := {m n : ℕ} → {S : AffineSimplex m n} → TriangulationData S → Finset (Finset (Euclidean m))
noncomputable def topCellsValue : topCellsType := fun {m n S} T => T.complex.cells.filter (fun s => s.card = n + 1)

abbrev facetsType := {m n : ℕ} → {S : AffineSimplex m n} → TriangulationData S → Finset (Finset (Euclidean m))
noncomputable def facetsValue : facetsType := fun {m n S} T => T.complex.cells.filter (fun s => 0 < n ∧ s.card = n)

abbrev boundaryFacetsType := {m n : ℕ} → {S : AffineSimplex m n} → TriangulationData S → Finset (Finset (Euclidean m))
noncomputable def boundaryFacetsValue : boundaryFacetsType := fun {m n S} T => (facetsValue T).filter (fun s => cellHull s ⊆ simplexBoundaryValue S)

abbrev internalFacetsType := {m n : ℕ} → {S : AffineSimplex m n} → TriangulationData S → Finset (Finset (Euclidean m))
noncomputable def internalFacetsValue : internalFacetsType := fun T => facetsValue T \ boundaryFacetsValue T

abbrev IncidentType := {m : ℕ} → Finset (Euclidean m) → Finset (Euclidean m) → Prop
noncomputable def IncidentValue : IncidentType := fun F C => F ⊆ C

abbrev inducedCellsType := {m n : ℕ} → {S : AffineSimplex m n} → TriangulationData S → Finset (Fin (n + 1)) → Finset (Finset (Euclidean m))
noncomputable def inducedCellsValue : inducedCellsType := fun {m n S} T I => T.complex.cells.filter (fun s => (s : Set (Euclidean m)) ⊆ simplexFaceValue S I)

abbrev cellDiameterType := {m : ℕ} → Finset (Euclidean m) → ℝ
noncomputable def cellDiameterValue : cellDiameterType := fun s => Metric.diam (cellHull s)

abbrev meshType := {m : ℕ} → GeometricComplexData m → ℝ
noncomputable def meshValue : meshType := fun K => K.cells.sup' ⟨∅, K.empty_mem⟩ cellDiameterValue

abbrev VertexLabelingType := {m n : ℕ} → {S : AffineSimplex m n} → TriangulationData S → Type
abbrev VertexLabelingValue : VertexLabelingType := fun {m n S} T => {v : Euclidean m // v ∈ verticesValue T.complex} → Fin (n + 1)

abbrev FaceRespectingType := {m n : ℕ} → {S : AffineSimplex m n} → (T : TriangulationData S) → VertexLabelingValue T → Prop
noncomputable def FaceRespectingValue : FaceRespectingType := fun {m n S} T ℓ => ∀ I : Finset (Fin (n + 1)), ∀ v : {v : Euclidean m // v ∈ verticesValue T.complex}, (v : Euclidean m) ∈ simplexFaceValue S I → ℓ v ∈ I


/-- Restrict a complex to a convex original face by retaining its contained cells.
Proving that this covers and triangulates that face is a later obligation. -/
def inducedComplex {m n : ℕ} {S : AffineSimplex m n}
    (T : TriangulationData S) (I : Finset (Fin (n + 1))) : GeometricComplexData m where
  cells := inducedCellsValue T I
  empty_mem := by simp [inducedCellsValue, T.complex.empty_mem]
  independent := by
    intro s hs
    exact T.complex.independent s (Finset.mem_filter.mp hs).1
  face_closed := by
    intro s hs t ht
    obtain ⟨hs, hface⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨T.complex.face_closed s hs t ht,
      fun x hx => hface (ht hx)⟩
  inter_eq := by
    intro s hs t ht
    exact T.complex.inter_eq s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1

abbrev inducedComplexType := {m n : ℕ} → {S : AffineSimplex m n} →
  TriangulationData S → Finset (Fin (n + 1)) → GeometricComplexData m
def inducedComplexValue : inducedComplexType := inducedComplex

/-- Labels on an actual cell; membership supplies membership in the global vertex set. -/
def cellLabels {m n : ℕ} {S : AffineSimplex m n} (T : TriangulationData S)
    (ℓ : VertexLabelingValue T) (s : Finset (Euclidean m)) (hs : s ∈ T.complex.cells) :
    Finset (Fin (n + 1)) :=
  s.attach.image fun v : s => ℓ ⟨v.val, by
    change v.val ∈ T.complex.cells.biUnion id
    exact Finset.mem_biUnion.mpr ⟨s, hs, v.property⟩⟩
abbrev cellLabelsType := {m n : ℕ} → {S : AffineSimplex m n} →
  (T : TriangulationData S) → VertexLabelingValue T →
  (s : Finset (Euclidean m)) → s ∈ T.complex.cells → Finset (Fin (n + 1))
def cellLabelsValue : cellLabelsType := cellLabels

def FullyLabeled {m n : ℕ} {S : AffineSimplex m n} (T : TriangulationData S)
    (ℓ : VertexLabelingValue T) (s : Finset (Euclidean m)) : Prop :=
  ∃ hs : s ∈ T.complex.cells, s.card = n + 1 ∧ cellLabels T ℓ s hs = Finset.univ
abbrev FullyLabeledType := {m n : ℕ} → {S : AffineSimplex m n} →
  (T : TriangulationData S) → VertexLabelingValue T → Finset (Euclidean m) → Prop
def FullyLabeledValue : FullyLabeledType := FullyLabeled

abbrev fullyLabeledCellsType := {m n : ℕ} → {S : AffineSimplex m n} →
  (T : TriangulationData S) → VertexLabelingValue T → Finset (Finset (Euclidean m))
def fullyLabeledCellsValue : fullyLabeledCellsType := fun T ℓ =>
  T.complex.cells.filter (FullyLabeled T ℓ)

/-- The geometric realization bridge to Mathlib. Only the empty face is erased. -/
def toMathlib {m : ℕ} (K : GeometricComplexData m) :
    Geometry.SimplicialComplex ℝ (Euclidean m) :=
  Geometry.SimplicialComplex.ofErase (K.cells : Set (Finset (Euclidean m)))
    (fun s hs => K.independent s hs)
    (fun t s ht hs => K.face_closed t hs s ht)
    (fun s hs t ht => by
      change cellHull s ∩ cellHull t ⊆ convexHull ℝ ((s : Set (Euclidean m)) ∩ t)
      rw [← Finset.coe_inter]
      exact (K.inter_eq s hs t ht).le)
abbrev toMathlibType := {m : ℕ} → GeometricComplexData m →
  Geometry.SimplicialComplex ℝ (Euclidean m)
def toMathlibValue : toMathlibType := toMathlib

def mem_standardSimplex : Prop :=
  ∀ (n : ℕ) (x : EuclideanValue (n + 1)),
  x ∈ standardSimplexValue n ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

def standardAffineSimplex_hull : Prop :=
  ∀ n : ℕ, simplexHullValue (standardAffineSimplexValue n) = standardSimplexValue n

def simplexFace_empty : Prop :=
  ∀ {m n : ℕ} (S : AffineSimplexValue m n), simplexFaceValue S ∅ = ∅

def simplexFace_univ : Prop :=
  ∀ {m n : ℕ} (S : AffineSimplexValue m n), simplexFaceValue S Finset.univ = simplexHullValue S

def simplexHull_face : Prop :=
  ∀ {m n : ℕ} (S : AffineSimplexValue m n) (I : Finset (Fin (n + 1)))
  {k : ℕ} (h : I.card = k + 1), simplexHullValue (S.face h) = simplexFaceValue S I

def cellHull_empty : Prop :=
  ∀ m : ℕ, cellHullValue (∅ : Finset (EuclideanValue m)) = ∅

def cellHull_mono : Prop :=
  ∀ {m : ℕ} {s t : Finset (EuclideanValue m)}, IsFaceValue s t → cellHullValue s ⊆ cellHullValue t

def cell_intersection_common_face : Prop :=
  ∀ {m : ℕ} (K : GeometricComplexValue m) (s : Finset (EuclideanValue m)), s ∈ K.cells →
  ∀ t : Finset (EuclideanValue m), t ∈ K.cells →
    s ∩ t ∈ K.cells ∧ IsFaceValue (s ∩ t) s ∧ IsFaceValue (s ∩ t) t ∧
      cellHullValue s ∩ cellHullValue t = cellHullValue (s ∩ t)

def toMathlib_faces : Prop :=
  ∀ {m : ℕ} (K : GeometricComplexValue m), (toMathlibValue K).faces =
  (K.cells : Set (Finset (EuclideanValue m))) \ {∅}

def toMathlib_space : Prop :=
  ∀ {m : ℕ} (K : GeometricComplexValue m), (toMathlibValue K).space = complexSupportValue K

def triangulation_cover : Prop :=
  ∀ {m n : ℕ} {S : AffineSimplexValue m n} (T : TriangulationValue S),
  (toMathlibValue T.complex).space = simplexHullValue S

def inducedCells_iff : Prop :=
  ∀ {m n : ℕ} {S : AffineSimplexValue m n} (T : TriangulationValue S)
  (I : Finset (Fin (n + 1))) (s : Finset (EuclideanValue m)),
    s ∈ inducedCellsValue T I ↔ s ∈ T.complex.cells ∧ cellHullValue s ⊆ simplexFaceValue S I

def inducedComplex_cells : Prop :=
  ∀ {m n : ℕ} {S : AffineSimplexValue m n} (T : TriangulationValue S)
  (I : Finset (Fin (n + 1))), (inducedComplexValue T I).cells = inducedCellsValue T I

def cellHull_bounded : Prop :=
  ∀ {m : ℕ} (s : Finset (EuclideanValue m)), Bornology.IsBounded (cellHullValue s)

def cellDiameter_eq_vertex_diameter : Prop :=
  ∀ {m : ℕ} (s : Finset (EuclideanValue m)), cellDiameterValue s = Metric.diam (s : Set (EuclideanValue m))

def cellDiameter_eq_extended : Prop :=
  ∀ {m : ℕ} (s : Finset (EuclideanValue m)),
  ENNReal.ofReal (cellDiameterValue s) =
    Specs.D10Topology.Ch09.MetricConventions.diameter
      (inferInstance : PseudoMetricSpace (EuclideanValue m)) (cellHullValue s)

def cellDiameter_le_mesh : Prop :=
  ∀ {m : ℕ} (K : GeometricComplexValue m) (s : Finset (EuclideanValue m)),
  s ∈ K.cells → cellDiameterValue s ≤ meshValue K

def mesh_attained : Prop :=
  ∀ {m : ℕ} (K : GeometricComplexValue m), ∃ s ∈ K.cells, meshValue K = cellDiameterValue s

def dist_le_mesh : Prop :=
  ∀ {m : ℕ} (K : GeometricComplexValue m) (s : Finset (EuclideanValue m)), s ∈ K.cells →
  ∀ x ∈ cellHullValue s, ∀ y ∈ cellHullValue s, dist x y ≤ meshValue K

def cellDimension_eq_finrank : Prop :=
  ∀ {m : ℕ} (K : GeometricComplexValue m) (s : Finset (EuclideanValue m)),
  s ∈ K.cells → s.Nonempty →
    cellDimensionValue s = (Module.finrank ℝ (vectorSpan ℝ (s : Set (EuclideanValue m))) : ℤ)

def maximal_cell_dimension : Prop :=
  ∀ {m n : ℕ} {S : AffineSimplexValue m n} (T : TriangulationValue S)
  (s : Finset (EuclideanValue m)), s ∈ maximalCellsValue T.complex → cellDimensionValue s = (n : ℤ)

def boundary_internal_partition : Prop :=
  ∀ {m n : ℕ} {S : AffineSimplexValue m n} (T : TriangulationValue S),
  Disjoint (boundaryFacetsValue T) (internalFacetsValue T) ∧
    boundaryFacetsValue T ∪ internalFacetsValue T = facetsValue T

def face_iff_hull_subset : Prop :=
  ∀ {m : ℕ} (K : GeometricComplexValue m) (s t : Finset (EuclideanValue m)),
    s ∈ K.cells → t ∈ K.cells → (IsFaceValue s t ↔ cellHullValue s ⊆ cellHullValue t)

def intersection_iff_common_face : Prop :=
  ∀ {m : ℕ} (s t : Finset (EuclideanValue m)),
    cellHullValue s ∩ cellHullValue t = cellHullValue (s ∩ t) ↔
      ∃ u : Finset (EuclideanValue m), IsFaceValue u s ∧ IsFaceValue u t ∧
        cellHullValue s ∩ cellHullValue t = cellHullValue u

end Specs.D10Topology.Ch17.SimplexTriangulation
