import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.BoundaryCones
import Mathlib.Topology.Homeomorph.Lemmas

/-! M02.05. The ambient space has its standard global coordinate chart.
Full rank is expressed as dimension n of the range of the local derivative. Local extensions are Euclidean extensions;
at a face their domain is not required to stay in the half-space.
The results are stated for arbitrary maps with full-rank parametrizations,
so in particular apply to inclusion of any subset carrying the stated charts.
No topological embedding or smooth inverse to a parametrization is assumed. -/
namespace SmoothManifolds.EmbeddedData
open ModelData AtlasData MapData TangentData DifferentialData
open Set Filter
open scoped Topology

/-- The standard chart, including the singleton coordinate space in dimension zero. -/
def euclideanChart (N : ℕ) : ModelChart N .euclidean (Euclidean N) :=
  (Homeomorph.Set.univ (Euclidean N)).symm.toOpenPartialHomeomorph

/-- An ambient extension of the local parametrization `j ∘ e.symm` at `e p`.
Germ agreement on the manifold is equivalent to agreement on a relatively open
coordinate neighborhood, because `e` is a chart at `p`. -/
def IsParametrizationAt {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (j : M → Euclidean N) (e : ModelChart n a M)
    (p : M) (V : Set (Euclidean n)) (H : Euclidean n → Euclidean N) : Prop :=
  IsOpen V ∧ (e p).val ∈ V ∧ ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
    (fun y => H (e y).val) =ᶠ[𝓝 p] j

/-- Exactly the smooth, full-rank local parametrization hypothesis. -/
def HasFullRankParametrizations {n N : ℕ} {a : ModelKind} {M : Type}
    [TopologicalSpace M] (S : SmoothManifold n a M) (j : M → Euclidean N) : Prop :=
  ∀ (p : M) (e : ModelChart n a M),
    e ∈ S.smoothStructure.val → p ∈ e.source →
    ∃ (V : Set (Euclidean n)) (H : Euclidean n → Euclidean N),
      IsParametrizationAt j e p V H ∧
      Module.finrank ℝ (LinearMap.range (fderiv ℝ H (e p).val).toLinearMap) = n

/-- The tangent hyperplane of the last-coordinate half-space. -/
def faceHyperplane (n : ℕ) : Submodule ℝ (Euclidean (n + 1)) :=
  LinearMap.ker (LinearMap.proj (Fin.last n))
end SmoothManifolds.EmbeddedData

namespace Specs.SmoothManifolds.Tangent.EmbeddedComparison
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.BoundaryConeData
  _root_.SmoothManifolds.EmbeddedData
open Set

def euclideanChartType := (N : ℕ) → ModelChart N .euclidean (Euclidean N)
def euclideanChartValue : euclideanChartType := EmbeddedData.euclideanChart

def IsParametrizationAtType := {n N : ℕ} → {a : ModelKind} → {M : Type} →
  [TopologicalSpace M] → (M → Euclidean N) → ModelChart n a M → M →
  Set (Euclidean n) → (Euclidean n → Euclidean N) → Prop
def IsParametrizationAtValue : IsParametrizationAtType := @EmbeddedData.IsParametrizationAt

def HasFullRankParametrizationsType := {n N : ℕ} → {a : ModelKind} → {M : Type} →
  [TopologicalSpace M] → SmoothManifold n a M → (M → Euclidean N) → Prop
def HasFullRankParametrizationsValue : HasFullRankParametrizationsType :=
  @EmbeddedData.HasFullRankParametrizations

def faceHyperplaneType := (n : ℕ) → Submodule ℝ (Euclidean (n + 1))
def faceHyperplaneValue : faceHyperplaneType := EmbeddedData.faceHyperplane

/-- This supplies the ambient standard structure used in the comparison. -/
def standardEuclidean_existsType : Prop :=
  ∀ N, ∃ T : SmoothManifold N .euclidean (Euclidean N),
    euclideanChart N ∈ T.smoothStructure.val

/-- The hypotheses on local parametrizations imply smoothness of the inclusion.
The intrinsic differential and its Euclidean coordinate realization both exist. -/
def embedded_differential_existsType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (j : M → Euclidean N),
    HasFullRankParametrizations S j →
    ∀ T : SmoothManifold N .euclidean (Euclidean N),
    euclideanChart N ∈ T.smoothStructure.val →
    IsSmoothMap S T j ∧ ∀ p,
      ∃ (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
        (F : TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N),
        IsDifferential S T j p L ∧ IsChartCoordinates T (j p) (euclideanChart N) F

/-- Every local parametrization, with every allowed ambient extension, gives
the same image. The displayed equivalence is the actual inclusion differential
in ambient coordinates, not an arbitrary vector-space equivalence. -/
def embedded_tangent_comparisonType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (j : M → Euclidean N),
    HasFullRankParametrizations S j →
    ∀ (T : SmoothManifold N .euclidean (Euclidean N)),
    euclideanChart N ∈ T.smoothStructure.val → ∀ (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (j p))
    (F : TangentSpace T (j p) ≃ₗ[ℝ] Euclidean N),
    IsDifferential S T j p L → IsChartCoordinates T (j p) (euclideanChart N) F →
    Function.Injective L ∧ Function.Injective (F.toLinearMap.comp L) ∧
      ∀ (e : ModelChart n a M), e ∈ S.smoothStructure.val → p ∈ e.source →
      ∀ (V : Set (Euclidean n)) (H : Euclidean n → Euclidean N),
      IsParametrizationAt j e p V H →
        LinearMap.range (F.toLinearMap.comp L) =
          LinearMap.range (fderiv ℝ H (e p).val).toLinearMap ∧
        ∃ I : TangentSpace S p ≃ₗ[ℝ] LinearMap.range (fderiv ℝ H (e p).val).toLinearMap,
          ∀ v, (I v).val = F (L v)

/-- Explicit independence of two parametrizations and their extensions. -/
def embedded_image_independentType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n a M) (j : M → Euclidean N),
    HasFullRankParametrizations S j → ∀ (p : M)
    (e d : ModelChart n a M), e ∈ S.smoothStructure.val →
    d ∈ S.smoothStructure.val → p ∈ e.source → p ∈ d.source →
    ∀ (V W : Set (Euclidean n)) (H K : Euclidean n → Euclidean N),
      IsParametrizationAt j e p V H → IsParametrizationAt j d p W K →
      LinearMap.range (fderiv ℝ H (e p).val).toLinearMap =
        LinearMap.range (fderiv ℝ K (d p).val).toLinearMap

/-- The embedded boundary tangent is the image of the source face hyperplane,
and is a proper subspace of the full embedded tangent, for every face chart. -/
def embedded_boundary_tangentType : Prop :=
  ∀ {n N : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold (n + 1) .halfSpace M) (j : M → Euclidean N),
    HasFullRankParametrizations S j →
    ∀ (T : SmoothManifold N .euclidean (Euclidean N)),
    euclideanChart N ∈ T.smoothStructure.val →
    ∃ B : SmoothManifold n .euclidean (intrinsicBoundary S), IsBoundaryStructure S B ∧
      ∀ (p : intrinsicBoundary S)
      (L : TangentSpace S p.val →ₗ[ℝ] TangentSpace T (j p.val))
      (F : TangentSpace T (j p.val) ≃ₗ[ℝ] Euclidean N)
      (K : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
      IsDifferential S T j p.val L →
      IsChartCoordinates T (j p.val) (euclideanChart N) F →
      IsDifferential B S Subtype.val p K →
      IsDifferential B T (j ∘ Subtype.val) p (L.comp K) ∧
      ∀ (e : ModelChart (n + 1) .halfSpace M), e ∈ S.smoothStructure.val →
      p.val ∈ e.source → ∀ (V : Set (Euclidean (n + 1)))
      (H : Euclidean (n + 1) → Euclidean N), IsParametrizationAt j e p.val V H →
        LinearMap.range ((F.toLinearMap.comp L).comp K) =
          (faceHyperplane n).map (fderiv ℝ H (e p.val).val).toLinearMap ∧
        LinearMap.range ((F.toLinearMap.comp L).comp K) <
          LinearMap.range (F.toLinearMap.comp L)
end Specs.SmoothManifolds.Tangent.EmbeddedComparison
