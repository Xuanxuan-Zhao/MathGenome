import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.SimplexTriangulation
import Mathlib.Analysis.Convex.Combination

/-! Independent statements for `paper.tex`, Lemma d10:17:subdivision.
All metrics are the inherited Euclidean L2 metrics. A face restriction retains
exactly the cells contained in that face, using the upstream `inducedComplex`.
The empty face is included and has a single empty cell, of cardinality zero.
No existence of a subdivision or shrinking mesh is an assumption below. -/
noncomputable section
open Set
open scoped BigOperators Topology
namespace Specs.D10Topology.Ch17.BarycentricSubdivision
open Specs.D10Topology.Ch17.SimplexTriangulation

/-- The vertices of the original simplex as a finite set in ambient space. -/
def originalVertices {m n : ℕ} (S : AffineSimplex m n) : Finset (Euclidean m) :=
  Finset.univ.image S.points

/-- Each induced complex covers the corresponding face, and all its maximal
cells have that face's number of vertices. This also includes the empty face.
The other geometric-complex axioms are already fields of `inducedComplex`. -/
def FaceCompatible {m n : ℕ} {S : AffineSimplex m n}
    (T : TriangulationData S) : Prop :=
  ∀ I : Finset (Fin (n + 1)),
    complexSupport (inducedComplex T I) = simplexFaceValue S I ∧
    ∀ s ∈ maximalCells (inducedComplex T I), s.card = I.card

/-- Mean of a finite set of vertices; the value at the empty set is zero.
Only nonempty sets are used as barycentric vertices. -/
def faceMean {m : ℕ} (F : Finset (Euclidean m)) : Euclidean m :=
  F.centerMass (fun _ => (1 : ℝ)) id

/-- A chain is a finite set of nonempty faces, pairwise comparable by inclusion.
Pairwise comparability suffices since distinct comparable faces are strictly
nested. The empty chain represents the empty cell. -/
def FaceChain {m : ℕ} (K : GeometricComplexData m)
    (C : Finset (Finset (Euclidean m))) : Prop :=
  (∀ F ∈ C, F ∈ K.cells ∧ F.Nonempty) ∧
    (C : Set (Finset (Euclidean m))).Pairwise (fun F G => F ⊆ G ∨ G ⊆ F)

/-- The proposed geometric barycentric cells; geometric validity is a theorem
to prove, not a field silently imposed on these finite sets. -/
def barycentricCells {m : ℕ} (K : GeometricComplexData m) :
    Finset (Finset (Euclidean m)) := by
  classical
  exact (K.cells.powerset.filter (FaceChain K)).image (fun C => C.image faceMean)

abbrev FaceCompatibleType := {m n : ℕ} → {S : AffineSimplex m n} →
  TriangulationData S → Prop
def FaceCompatibleValue : FaceCompatibleType := @FaceCompatible
abbrev faceMeanType := {m : ℕ} → Finset (Euclidean m) → Euclidean m
def faceMeanValue : faceMeanType := @faceMean

def initial_triangulation : Prop :=
  ∀ {m n : ℕ} (S : AffineSimplex m n),
    ∃ T : TriangulationData S,
      T.complex.cells = (originalVertices S).powerset ∧ FaceCompatible T ∧
      meshValue T.complex = Metric.diam (simplexHull S)

def faceMean_mem : Prop :=
  ∀ {m : ℕ} (F : Finset (Euclidean m)), F.Nonempty → faceMean F ∈ cellHull F

def nested_faceMean_dist : Prop :=
  ∀ {m : ℕ} (F G : Finset (Euclidean m)), F.Nonempty → F ⊆ G →
    dist (faceMean F) (faceMean G) ≤
      (1 - (F.card : ℝ) / (G.card : ℝ)) * cellDiameterValue G

def nested_faceMean_contraction : Prop :=
  ∀ {m n : ℕ} (F G : Finset (Euclidean m)), F.Nonempty → F ⊆ G →
    G.card ≤ n + 1 →
    dist (faceMean F) (faceMean G) ≤
      ((n : ℝ) / ((n : ℝ) + 1)) * cellDiameterValue G

def barycentric_cell_diameter : Prop :=
  ∀ {m n : ℕ} (K : GeometricComplexData m),
    (∀ F ∈ K.cells, F.card ≤ n + 1) →
    ∀ C : Finset (Finset (Euclidean m)), FaceChain K C →
      cellDiameterValue (C.image faceMean) ≤
        ((n : ℝ) / ((n : ℝ) + 1)) * meshValue K

def barycentric_mesh_contraction : Prop :=
  ∀ {m n : ℕ} {S : AffineSimplex m n} (T : TriangulationData S)
    (L : GeometricComplexData m), L.cells = barycentricCells T.complex →
      meshValue L ≤ ((n : ℝ) / ((n : ℝ) + 1)) * meshValue T.complex

def fine_triangulations : Prop :=
  ∀ {m n : ℕ} (S : AffineSimplex m n),
    ∃ T : ℕ → TriangulationData S,
      (∀ r, FaceCompatible (T r)) ∧
      Filter.Tendsto (fun r => meshValue (T r).complex) Filter.atTop (𝓝 0)

def arbitrarily_fine_triangulation : Prop :=
  ∀ {m n : ℕ} (S : AffineSimplex m n) (ε : ℝ), 0 < ε →
    ∃ T : TriangulationData S, FaceCompatible T ∧ meshValue T.complex < ε

def zero_dimensional_fine_triangulations : Prop :=
  ∀ {m : ℕ} (S : AffineSimplex m 0),
    ∃ T : ℕ → TriangulationData S,
      (∀ r, FaceCompatible (T r)) ∧ (∀ r, meshValue (T r).complex = 0) ∧
      Filter.Tendsto (fun r => meshValue (T r).complex) Filter.atTop (𝓝 0)

/-- The raw face-chain vertices are actual affinely independent simplex vertices. -/
def faceChain_independent : Prop :=
  ∀ {m : ℕ} (K : GeometricComplexData m)
    (C : Finset (Finset (Euclidean m))), FaceChain K C →
      AffineIndependent ℝ ((↑) : C.image faceMean → Euclidean m)

/-- Exact chain-cell geometry, not merely a finite covering by convex sets. -/
def barycentricCells_inter_eq : Prop :=
  ∀ {m : ℕ} (K : GeometricComplexData m)
    (s : Finset (Euclidean m)), s ∈ barycentricCells K →
    ∀ t : Finset (Euclidean m), t ∈ barycentricCells K →
      cellHull s ∩ cellHull t = cellHull (s ∩ t)

/-- Subdivision exists for every finite geometric complex and retains its support.
The geometric-complex fields express independence, faces and exact intersections. -/
def barycentric_complex_exists : Prop :=
  ∀ {m : ℕ} (K : GeometricComplexData m),
    ∃ L : GeometricComplexData m, L.cells = barycentricCells K ∧
      complexSupport L = complexSupport K

end Specs.D10Topology.Ch17.BarycentricSubdivision
