import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Coordinate slices use the first k coordinates; the last of those k
coordinates is the boundary coordinate of a half-slice. All equalities below
are on the actual chart image, with no rectangular-image assumption.

The ambient model kind may be either accepted kind: boundarylessness is a
condition on the intrinsic boundary, not on its chosen uniform model. Mixed
model charts are compared using the existing local extension convention.
-/
namespace SmoothManifolds.SliceData
open ModelData AtlasData MapData BoundaryData MapClassData Set
universe u v

/-- Inclusion into the first k coordinates, followed by zero coordinates. -/
def sliceEmbedding (k n : ℕ) (x : Euclidean k) : Euclidean n :=
  fun j => if h : j.val < k then x ⟨j.val, h⟩ else 0

/-- Projection onto the slice coordinates. -/
def sliceProjection {k n : ℕ} (hkn : k ≤ n) (x : Euclidean n) : Euclidean k :=
  fun i => x (i.castLE hkn)

def coordinateSlice (k n : ℕ) (q : ModelKind) : Set (Euclidean n) :=
  sliceEmbedding k n '' modelSet k q

/-- Compatibility with every original smooth chart, in both directions.
This also permits Euclidean charts on a manifold represented by half-spaces. -/
def CompatibleChart {k : ℕ} {a q : ModelKind} {P : Type u} [TopologicalSpace P]
    (S : SmoothManifold k a P) (c : ModelChart k q P) : Prop :=
  ∀ e ∈ S.smoothStructure.val, ∀ p, p ∈ c.source → p ∈ e.source →
    ChartContDiffAt ⊤ c e id p ∧ ChartContDiffAt ⊤ e c id p

/-- The subset is precisely the indicated slice inside the actual chart image.
A genuine half-slice is only used in positive dimension. -/
def IsSliceChart {n : ℕ} {N : Type u} [TopologicalSpace N]
    (s : Set N) (k : ℕ) (q : ModelKind) (d : ModelChart n .euclidean N) : Prop :=
  k ≤ n ∧ (q = .halfSpace → 0 < k) ∧
    d '' (s ∩ d.source) = d.target ∩ Subtype.val ⁻¹' coordinateSlice k n q

/-- A full slice can occur in either global model. A half-slice is admitted
only when that global model allows boundary points. The empty subset imposes
no chart or nonemptiness requirement. -/
def HasSliceCharts {n : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
    (T : SmoothManifold n b N) (s : Set N) (k : ℕ) (a : ModelKind) : Prop :=
  k ≤ n ∧ ∀ p ∈ s, ∃ q : ModelKind, (q = .euclidean ∨ q = a) ∧
    ∃ d : ModelChart n .euclidean N,
      CompatibleChart T d ∧ p ∈ d.source ∧ IsSliceChart s k q d

/-- The chart on the subspace obtained by projecting the ambient slice.
Its source and target are specified exactly. -/
def IsSliceRestriction {k n : ℕ} {q : ModelKind} {N : Type u}
    [TopologicalSpace N] {s : Set N} (hkn : k ≤ n)
    (d : ModelChart n .euclidean N) (c : ModelChart k q s) : Prop :=
  c.source = Subtype.val ⁻¹' d.source ∧
    c.target = (fun x : ModelSpace k q =>
      (⟨sliceEmbedding k n x.val, mem_univ _⟩ : ModelSpace n .euclidean)) ⁻¹' d.target ∧
    ∀ p ∈ c.source, (c p).val = sliceProjection hkn (d p.val).val

/-- The usual unit circle in the real Euclidean plane with its subspace topology. -/
def standardCircle : Set (EuclideanSpace ℝ (Fin 2)) := Metric.sphere 0 1

/-- An ambient structure on the plane is the ordinary Euclidean one when it
contains the global linear coordinate chart. This is data about its atlas,
not an assumed manifold or embedding certificate. -/
def HasStandardPlaneChart (T : SmoothManifold 2 .euclidean
    (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ e ∈ T.smoothStructure.val, e.source = univ ∧
    ∀ x, (e x).val = EuclideanSpace.equiv (Fin 2) ℝ x

end SmoothManifolds.SliceData

namespace Specs.SmoothManifolds.Ch03.SliceStructures
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.SliceData Set
universe u v

/-- A general embedding formulation also covers an embedded submanifold given
with an initially arbitrary topology: specialize f to its inclusion. -/
def interior_sliceType : Prop :=
  ∀ {k n : ℕ} {a b : ModelKind} {P : Type u} {N : Type v}
    [TopologicalSpace P] [TopologicalSpace N]
    (S : SmoothManifold k a P) (T : SmoothManifold n b N) (f : P → N),
    intrinsicBoundary T = ∅ → IsSmoothEmbedding S T f →
    ∀ p, p ∈ manifoldInterior S →
    ∃ d : ModelChart n .euclidean N,
      CompatibleChart T d ∧ f p ∈ d.source ∧
      IsSliceChart (range f) k .euclidean d

def boundary_sliceType : Prop :=
  ∀ {k n : ℕ} {a b : ModelKind} {P : Type u} {N : Type v}
    [TopologicalSpace P] [TopologicalSpace N]
    (S : SmoothManifold k a P) (T : SmoothManifold n b N) (f : P → N),
    intrinsicBoundary T = ∅ → IsSmoothEmbedding S T f →
    ∀ p, p ∈ intrinsicBoundary S →
    ∃ d : ModelChart n .euclidean N, CompatibleChart T d ∧ f p ∈ d.source ∧
      IsSliceChart (range f) k .halfSpace d ∧
      ∃ hkn : k ≤ n, sliceProjection hkn (d (f p)).val ∈ halfSpaceFace k

/-- Existence uses exactly the subspace topology. Every ambient slice chart
induces compatible subset coordinates. Uniqueness is equality of maximal
atlases on this same underlying set, hence is identification by the identity. -/
def slice_structureType : Prop :=
  ∀ {k n : ℕ} {a b : ModelKind} {N : Type u} [TopologicalSpace N]
    (T : SmoothManifold n b N) (s : Set N),
    intrinsicBoundary T = ∅ → HasSliceCharts T s k a →
    ∃ S : SmoothManifold k a s,
      IsSmoothEmbedding S T Subtype.val ∧
      (∀ (q : ModelKind) (d : ModelChart n .euclidean N),
        (q = .euclidean ∨ q = a) → CompatibleChart T d → IsSliceChart s k q d →
        Nonempty {p : s // p.val ∈ d.source} →
        ∃ (hkn : k ≤ n) (c : ModelChart k q s),
          IsSliceRestriction hkn d c ∧ CompatibleChart S c) ∧
      ∀ R : SmoothManifold k a s, IsSmoothEmbedding R T Subtype.val →
        R.smoothStructure = S.smoothStructure

/-- Uniqueness across different permitted global model kinds is smoothness
of the identity in both directions, on the same subspace and topology. -/
def embedded_structure_identityType : Prop :=
  ∀ {k n : ℕ} {a a' b : ModelKind} {N : Type u} [TopologicalSpace N]
    (T : SmoothManifold n b N) (s : Set N)
    (S : SmoothManifold k a s) (R : SmoothManifold k a' s),
    intrinsicBoundary T = ∅ → IsSmoothEmbedding S T Subtype.val →
    IsSmoothEmbedding R T Subtype.val →
    IsSmoothMap S R id ∧ IsSmoothMap R S id

def circle_boundary_distinctionType : Prop :=
  ∃ T : SmoothManifold 2 .euclidean (EuclideanSpace ℝ (Fin 2)),
    HasStandardPlaneChart T ∧
    ∃ C : SmoothManifold 1 .euclidean standardCircle,
      IsSmoothEmbedding C T Subtype.val ∧ intrinsicBoundary C = ∅ ∧
        frontier standardCircle = standardCircle

-- Useful independently checkable portions of the construction.
def sliceProjection_embeddingType : Prop :=
  ∀ {k n : ℕ} (hkn : k ≤ n) (x : Euclidean k),
    sliceProjection hkn (sliceEmbedding k n x) = x

def sliceEmbedding_injectiveType : Prop :=
  ∀ {k n : ℕ}, k ≤ n → Function.Injective (sliceEmbedding k n)

def coordinateSlice_zeroType : Prop :=
  ∀ (n : ℕ) (q : ModelKind), coordinateSlice 0 n q = {0}

def coordinateSlice_fullType : Prop :=
  ∀ (n : ℕ) (q : ModelKind), coordinateSlice n n q = modelSet n q

def halfSlice_positiveType : Prop :=
  ∀ {k n : ℕ} {N : Type u} [TopologicalSpace N] {s : Set N}
    {d : ModelChart n .euclidean N}, IsSliceChart s k .halfSpace d → 0 < k

def circle_frontierType : Prop := frontier standardCircle = standardCircle

def empty_slice_structureType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {N : Type u} [TopologicalSpace N]
    (T : SmoothManifold n b N) (k : ℕ),
    ∃ S : SmoothManifold k a (∅ : Set N),
      IsSmoothEmbedding S T Subtype.val ∧
        ∀ R : SmoothManifold k a (∅ : Set N), R.smoothStructure = S.smoothStructure

def exists_sliceRestrictionType : Prop :=
  ∀ {k n : ℕ} {q : ModelKind} {N : Type u} [TopologicalSpace N] {s : Set N}
    (d : ModelChart n .euclidean N), IsSliceChart s k q d →
    Nonempty {p : s // p.val ∈ d.source} →
    ∃ (hkn : k ≤ n) (c : ModelChart k q s), IsSliceRestriction hkn d c

def projected_slice_transitionsType : Prop :=
  ∀ {k n : ℕ} {a q q' : ModelKind} {N : Type u} [TopologicalSpace N]
    (T : SmoothManifold n a N) {s : Set N}
    (d d' : ModelChart n .euclidean N),
    CompatibleChart T d → CompatibleChart T d' →
    IsSliceChart s k q d → IsSliceChart s k q' d' →
    Nonempty {p : s // p.val ∈ d.source} →
    Nonempty {p : s // p.val ∈ d'.source} →
    ∃ (hkn : k ≤ n) (c : ModelChart k q s) (c' : ModelChart k q' s),
      IsSliceRestriction hkn d c ∧ IsSliceRestriction hkn d' c' ∧
        ∀ p ∈ c.source, p ∈ c'.source → ChartContDiffAt ⊤ c c' id p

def localize_embedding_sliceType : Prop :=
  ∀ {k n : ℕ} {q : ModelKind} {P : Type u} {N : Type v}
    [TopologicalSpace P] [TopologicalSpace N]
    (f : P → N), Topology.IsEmbedding f →
    ∀ (e : ModelChart k q P) (d : ModelChart n .euclidean N)
      (p : P), p ∈ e.source → k ≤ n → (q = .halfSpace → 0 < k) →
      MapsTo f e.source d.source →
      (∀ x ∈ e.source, (d (f x)).val = sliceEmbedding k n (e x).val) →
      ∃ (A : Set N) (hA : IsOpen A), f p ∈ (d.restrOpen A hA).source ∧
        IsSliceChart (range f) k q (d.restrOpen A hA)

end Specs.SmoothManifolds.Ch03.SliceStructures
