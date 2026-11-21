import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.SmoothMaps
import Mathlib.Topology.Constructions

/-! Intrinsic boundary: independent statements using the canonical atlas and
ambient-extension conventions. The face always uses the last coordinate.
No boundary invariance or manifold structure on the boundary is assumed. -/
namespace SmoothManifolds.BoundaryData
open ModelData AtlasData MapData Set
universe u

/-- The Euclidean model has no face, including in dimension zero. -/
def modelFace (n : ℕ) : ModelKind → Set (Euclidean n)
  | .halfSpace => halfSpaceFace n
  | .euclidean => ∅

/-- A point has boundary coordinates in at least one chart of the smooth atlas.
Theorems below establish independence of that choice. -/
def intrinsicBoundary {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M) : Set M :=
  {p | ∃ c ∈ S.smoothStructure.val, p ∈ c.source ∧ (c p).val ∈ modelFace n kind}

/-- Interior coordinates in an ambient Euclidean open set. -/
def manifoldInterior {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M) : Set M :=
  {p | ∃ c ∈ S.smoothStructure.val, p ∈ c.source ∧
    (c p).val ∈ interior (modelSet n kind)}

/-- Insert a zero in the final coordinate, and view the result in either model. -/
def faceEmbedding {n : ℕ} (kind : ModelKind) (z : ModelSpace n .euclidean) :
    ModelSpace (n + 1) kind :=
  ⟨Fin.snoc z.val 0, by cases kind <;> simp [modelSet, halfSpaceSet]⟩

/-- An actual chart on the boundary obtained by restricting a given chart and
then deleting its last coordinate. The equalities specify the whole source and
image; agreement of coordinate maps is required on the source. -/
def IsFaceRestriction {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) kind M) (c : ModelChart (n + 1) kind M)
    (b : ModelChart n .euclidean (intrinsicBoundary S)) : Prop :=
  b.source = Subtype.val ⁻¹' c.source ∧
  b.target = faceEmbedding kind ⁻¹' c.target ∧
  ∀ p ∈ b.source, ∀ i : Fin n, (b p).val i = (c p.val).val i.castSucc

end SmoothManifolds.BoundaryData

namespace Specs.SmoothManifolds.Foundations.Boundary
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData Set
universe u v

-- Full types and values of the canonical definitions.
def modelFaceType := (n : ℕ) → ModelKind → Set (Euclidean n)
def modelFaceValue : modelFaceType := BoundaryData.modelFace

def intrinsicBoundaryType := {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n kind M → Set M
def intrinsicBoundaryValue : intrinsicBoundaryType := @BoundaryData.intrinsicBoundary

def manifoldInteriorType := {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n kind M → Set M
def manifoldInteriorValue : manifoldInteriorType := @BoundaryData.manifoldInterior

def faceEmbeddingType := {n : ℕ} → (kind : ModelKind) →
  ModelSpace n .euclidean → ModelSpace (n + 1) kind
def faceEmbeddingValue : faceEmbeddingType := @BoundaryData.faceEmbedding

def IsFaceRestrictionType := {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold (n + 1) kind M) →
  ModelChart (n + 1) kind M → ModelChart n .euclidean (intrinsicBoundary S) → Prop
def IsFaceRestrictionValue : IsFaceRestrictionType := @BoundaryData.IsFaceRestriction

/-- Mixed-model chart comparison uses actual smooth identity-coordinate germs
in both directions, not a presumed topological invariance certificate. -/
def modelFace_chart_independentType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M : Type u} [TopologicalSpace M]
    (c : ModelChart n a M) (d : ModelChart n b M) (p : M),
    p ∈ c.source → p ∈ d.source →
    ChartContDiffAt (⊤ : ℕ∞) c d id p → ChartContDiffAt (⊤ : ℕ∞) d c id p →
    ((c p).val ∈ modelFace n a ↔ (d p).val ∈ modelFace n b)

def intrinsicBoundary_iff_chartType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M) (c : ModelChart n kind M),
    c ∈ S.smoothStructure.val → ∀ p ∈ c.source,
    (p ∈ intrinsicBoundary S ↔ (c p).val ∈ modelFace n kind)

def isOpen_manifoldInteriorType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M), IsOpen (manifoldInterior S)

def compl_intrinsicBoundaryType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M), (intrinsicBoundary S)ᶜ = manifoldInterior S

def isClosed_intrinsicBoundaryType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M), IsClosed (intrinsicBoundary S)

def intrinsicBoundary_zeroType : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 kind M), intrinsicBoundary S = ∅

def intrinsicBoundary_euclideanType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M), intrinsicBoundary S = ∅

/-- The maximal atlas contains all nonempty face restrictions of the original
charts, and its inclusion is smooth with the existing local extension calculus.
An empty source needs no chart (a partial homeomorphism into a nonempty model
cannot have an empty base type). The original chart cover ensures these
restrictions cover the boundary. -/
def exists_boundary_smoothManifoldType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) kind M),
    ∃ B : SmoothManifold n .euclidean (intrinsicBoundary S),
      IsSmoothMap B S Subtype.val ∧
      ∀ c ∈ S.smoothStructure.val,
        Nonempty {p : intrinsicBoundary S // p.val ∈ c.source} →
        ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S c b

/-- Diffeomorphisms, including between the two permitted
models, preserve both the intrinsic boundary and its interior complement. -/
def diffeomorph_boundary_iffType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (h : Diffeomorph S.smoothStructure.val T.smoothStructure.val) (p : M),
    (h.toEquiv p ∈ intrinsicBoundary T ↔ p ∈ intrinsicBoundary S)

def diffeomorph_interior_iffType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (h : Diffeomorph S.smoothStructure.val T.smoothStructure.val) (p : M),
    (h.toEquiv p ∈ manifoldInterior T ↔ p ∈ manifoldInterior S)

end Specs.SmoothManifolds.Foundations.Boundary
