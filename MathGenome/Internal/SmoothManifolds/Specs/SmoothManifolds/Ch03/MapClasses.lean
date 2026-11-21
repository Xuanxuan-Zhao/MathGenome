import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.FiniteRegularity
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Map classes use the full coordinate-quotient tangent spaces of Chapter 2.
The existential witnesses below are vector-space realizations, not extra input
hypotheses on a manifold. Their existence and independence are proved in the
implementation. In particular normal vectors are retained at a face. -/
namespace SmoothManifolds.MapClassData
open ModelData AtlasData MapData FiniteRegularityData Set
universe u v

section Maps
variable {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
  [TopologicalSpace M] [TopologicalSpace N]
  (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N) (p : M)

/-- The dimension of the image of an actual full tangent differential is k. -/
def HasRankAt (k : ℕ) : Prop :=
  ∃ (F : FiberModel S.smoothStructure.val p)
    (G : FiberModel T.smoothStructure.val (f p)),
    letI := F.group; letI := F.module; letI := G.group; letI := G.module
    ∃ L : CoordinateTangent S.smoothStructure.val p →ₗ[ℝ]
      CoordinateTangent T.smoothStructure.val (f p),
      IsCoordinateDifferential f p F G L ∧ Module.finrank ℝ (LinearMap.range L) = k

/-- On C¹ maps the possible image dimensions form a nonempty singleton.
The default only makes rank total outside that domain. -/
noncomputable def rankAt : ℕ := by
  classical
  exact if h : ∃ k, HasRankAt S T f p k then Nat.find h else 0

/-- C¹ at p, with injective full differential. -/
def IsImmersionAt : Prop :=
  ManifoldContDiffAt 1 S.smoothStructure.val T.smoothStructure.val f p ∧
  ∃ (F : FiberModel S.smoothStructure.val p)
    (G : FiberModel T.smoothStructure.val (f p)),
    letI := F.group; letI := F.module; letI := G.group; letI := G.module
    ∃ L : CoordinateTangent S.smoothStructure.val p →ₗ[ℝ]
      CoordinateTangent T.smoothStructure.val (f p),
      IsCoordinateDifferential f p F G L ∧ Function.Injective L

/-- C¹ at p, with surjective full differential. -/
def IsSubmersionAt : Prop :=
  ManifoldContDiffAt 1 S.smoothStructure.val T.smoothStructure.val f p ∧
  ∃ (F : FiberModel S.smoothStructure.val p)
    (G : FiberModel T.smoothStructure.val (f p)),
    letI := F.group; letI := F.module; letI := G.group; letI := G.module
    ∃ L : CoordinateTangent S.smoothStructure.val p →ₗ[ℝ]
      CoordinateTangent T.smoothStructure.val (f p),
      IsCoordinateDifferential f p F G L ∧ Function.Surjective L

def IsImmersion : Prop := ∀ p, IsImmersionAt S T f p

def IsSubmersion : Prop := ∀ p, IsSubmersionAt S T f p

/-- Smoothness, injectivity, immersion, and the homeomorphism onto the image
with exactly the target subspace topology. -/
def IsSmoothEmbedding : Prop :=
  IsSmoothMap S T f ∧ Function.Injective f ∧ IsImmersion S T f ∧
    ∃ h : M ≃ₜ Set.range f, ∀ x, (h x).val = f x

/-- In particular every point outside the image is regular. -/
def IsRegularValue (y : N) : Prop :=
  ∀ p, f p = y → IsSubmersionAt S T f p

end Maps

/-- Properness is compactness of inverse images of all compact target sets. -/
def IsProper {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (f : M → N) : Prop :=
  ∀ K : Set N, IsCompact K → IsCompact (f ⁻¹' K)

section Submanifolds
variable {n : ℕ} {b : ModelKind} {N : Type v} [TopologicalSpace N]
  (T : SmoothManifold n b N) (s : Set N) (k : ℕ) (a : ModelKind)

/-- A topology on the underlying set, allowed to be finer than the ambient
subspace topology, and a smooth structure making inclusion an immersion.
Inclusion is automatically injective as a map of underlying sets. -/
def IsImmersedSubmanifold : Prop :=
  ∃ t : TopologicalSpace s,
    ∃ S : @SmoothManifold k a s t,
      @IsSmoothMap k n a b s N t _ S T Subtype.val ∧
      @IsImmersion k n a b s N t _ S T Subtype.val

/-- The embedding requirement enforces the subspace topology. -/
def IsEmbeddedSubmanifold : Prop :=
  ∃ t : TopologicalSpace s,
    ∃ S : @SmoothManifold k a s t,
      @IsSmoothEmbedding k n a b s N t _ S T Subtype.val

end Submanifolds
end SmoothManifolds.MapClassData

namespace Specs.SmoothManifolds.Ch03.MapClasses
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.FiniteRegularityData _root_.SmoothManifolds.MapClassData
open Set
universe u v

def HasRankAtType :=
  {m n : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → SmoothManifold m a M → SmoothManifold n b N → (M → N) → M → ℕ → Prop
noncomputable def HasRankAtValue : HasRankAtType := @MapClassData.HasRankAt

def rankAtType :=
  {m n : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → SmoothManifold m a M → SmoothManifold n b N → (M → N) → M → ℕ
noncomputable def rankAtValue : rankAtType := @MapClassData.rankAt

def IsImmersionAtType :=
  {m n : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → SmoothManifold m a M → SmoothManifold n b N → (M → N) → M → Prop
noncomputable def IsImmersionAtValue : IsImmersionAtType := @MapClassData.IsImmersionAt

def IsSubmersionAtType :=
  {m n : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → SmoothManifold m a M → SmoothManifold n b N → (M → N) → M → Prop
noncomputable def IsSubmersionAtValue : IsSubmersionAtType := @MapClassData.IsSubmersionAt

def IsImmersionType :=
  {m n : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → SmoothManifold m a M → SmoothManifold n b N → (M → N) → Prop
noncomputable def IsImmersionValue : IsImmersionType := @MapClassData.IsImmersion

def IsSubmersionType :=
  {m n : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → SmoothManifold m a M → SmoothManifold n b N → (M → N) → Prop
noncomputable def IsSubmersionValue : IsSubmersionType := @MapClassData.IsSubmersion

def IsSmoothEmbeddingType :=
  {m n : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → SmoothManifold m a M → SmoothManifold n b N → (M → N) → Prop
noncomputable def IsSmoothEmbeddingValue : IsSmoothEmbeddingType := @MapClassData.IsSmoothEmbedding

def IsRegularValueType :=
  {m n : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → SmoothManifold m a M → SmoothManifold n b N → (M → N) → N → Prop
noncomputable def IsRegularValueValue : IsRegularValueType := @MapClassData.IsRegularValue

def IsProperType :=
  {M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] → (M → N) → Prop
noncomputable def IsProperValue : IsProperType := @MapClassData.IsProper

def IsImmersedSubmanifoldType :=
  {n : ℕ} → {b : ModelKind} → {N : Type v} → [TopologicalSpace N] → SmoothManifold n b N → Set N → ℕ → ModelKind → Prop
noncomputable def IsImmersedSubmanifoldValue : IsImmersedSubmanifoldType := @MapClassData.IsImmersedSubmanifold

def IsEmbeddedSubmanifoldType :=
  {n : ℕ} → {b : ModelKind} → {N : Type v} → [TopologicalSpace N] → SmoothManifold n b N → Set N → ℕ → ModelKind → Prop
noncomputable def IsEmbeddedSubmanifoldValue : IsEmbeddedSubmanifoldType := @MapClassData.IsEmbeddedSubmanifold

section Maps

/-- All three coordinate quantities are the intrinsic full tangent quantities. -/
def chart_invariantsType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N],
  ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
  ManifoldContDiff 1 S.smoothStructure.val T.smoothStructure.val f →
  ∀ (p : M) (e : ModelChart m a M) (d : ModelChart n b N),
  e ∈ S.smoothStructure.val → d ∈ T.smoothStructure.val →
  p ∈ e.source → f p ∈ d.source →
    rankAt S T f p = Module.finrank ℝ (LinearMap.range (chartDerivative e d f p).toLinearMap) ∧
    (IsImmersionAt S T f p ↔ Function.Injective (chartDerivative e d f p)) ∧
    (IsSubmersionAt S T f p ↔ Function.Surjective (chartDerivative e d f p))

/-- Rank really is the dimension of the image of every realization of df_p. -/
def full_tangent_invariantsType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N],
  ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
  ManifoldContDiff 1 S.smoothStructure.val T.smoothStructure.val f →
  ∀ (p : M) (F : FiberModel S.smoothStructure.val p)
    (G : FiberModel T.smoothStructure.val (f p)),
  letI := F.group; letI := F.module; letI := G.group; letI := G.module
  ∀ L : CoordinateTangent S.smoothStructure.val p →ₗ[ℝ]
      CoordinateTangent T.smoothStructure.val (f p),
    IsCoordinateDifferential f p F G L →
    rankAt S T f p = Module.finrank ℝ (LinearMap.range L) ∧
    (IsImmersionAt S T f p ↔ Function.Injective L) ∧
    (IsSubmersionAt S T f p ↔ Function.Surjective L)

/-- Independence under arbitrary legitimate source and target chart changes. -/
def chart_change_invariantsType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N],
  ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
  ManifoldContDiff 1 S.smoothStructure.val T.smoothStructure.val f →
  ∀ (p : M) (e e' : ModelChart m a M) (d d' : ModelChart n b N),
  e ∈ S.smoothStructure.val → e' ∈ S.smoothStructure.val →
  d ∈ T.smoothStructure.val → d' ∈ T.smoothStructure.val →
  p ∈ e.source → p ∈ e'.source → f p ∈ d.source → f p ∈ d'.source →
    Module.finrank ℝ (LinearMap.range (chartDerivative e d f p).toLinearMap) =
      Module.finrank ℝ (LinearMap.range (chartDerivative e' d' f p).toLinearMap) ∧
    (Function.Injective (chartDerivative e d f p) ↔ Function.Injective (chartDerivative e' d' f p)) ∧
    (Function.Surjective (chartDerivative e d f p) ↔ Function.Surjective (chartDerivative e' d' f p))

def rank_exists_uniqueType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N],
  ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
  ManifoldContDiff 1 S.smoothStructure.val T.smoothStructure.val f →
  ∀ p : M, ∃! k, HasRankAt S T f p k

def regularValue_empty_fiberType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N],
  ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N) (y : N),
    y ∉ Set.range f → IsRegularValue S T f y

end Maps

/-- Compatibility with the original smooth germ-derivation tangent model. -/
def smooth_tangent_invariantsType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
  IsSmoothMap S T f → ∀ (p : M)
    (L : TangentData.TangentSpace S p →ₗ[ℝ] TangentData.TangentSpace T (f p)),
  DifferentialData.IsDifferential S T f p L →
    rankAt S T f p = Module.finrank ℝ (LinearMap.range L) ∧
    (IsImmersionAt S T f p ↔ Function.Injective L) ∧
    (IsSubmersionAt S T f p ↔ Function.Surjective L)

def embedded_is_immersedType : Prop :=
  ∀ {n : ℕ} {b : ModelKind} {N : Type v} [TopologicalSpace N]
    (T : SmoothManifold n b N) (s : Set N) (k : ℕ) (a : ModelKind),
    IsEmbeddedSubmanifold T s k a → IsImmersedSubmanifold T s k a

end Specs.SmoothManifolds.Ch03.MapClasses
