import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.BoundaryRegularLevels

/-! Independent specification of M04.06 (paper.tex, transverse inverse image).
All subset manifolds use their ambient subspace topologies. The target subset
is supplied with its boundaryless embedded structure; no closedness or global
level-set presentation is assumed. Full and boundary transversality are separate.
The natural boundary structure is an existing interface, whose existence is the
upstream `natural_boundary_exists` obligation, not an extra geometric assumption.
-/
set_option autoImplicit false

namespace SmoothManifolds.TransversePreimageData
open ModelData AtlasData MapData MapClassData BoundaryData TangentData DifferentialData Set
universe u

/-- Transversality in the full ambient tangent space. Quantifying over the
actual differentials makes the definition independent of a choice of coordinates.
Existence and uniqueness of these differentials follow from smoothness. -/
def IsTransverseAt {m n k : ℕ} {a b c : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    {s : Set N} (R : SmoothManifold k c s) (f : M → N)
    (p : M) (hp : f p ∈ s) : Prop :=
  ∀ (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (I : TangentSpace R ⟨f p, hp⟩ →ₗ[ℝ] TangentSpace T (f p)),
    IsDifferential S T f p L →
    IsDifferential R T Subtype.val ⟨f p, hp⟩ I →
    LinearMap.range L ⊔ LinearMap.range I = ⊤

/-- There is no condition at points outside the inverse image. For the boundary
hypothesis this is applied to the restriction of f to the natural boundary. -/
def IsTransverse {m n k : ℕ} {a b c : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    {s : Set N} (R : SmoothManifold k c s) (f : M → N) : Prop :=
  ∀ p (hp : f p ∈ s), IsTransverseAt S T R f p hp

end SmoothManifolds.TransversePreimageData

namespace Specs.SmoothManifolds.Ch04.TransversePreimage
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.BoundaryRegularLevelData
  _root_.SmoothManifolds.TransversePreimageData Set
universe u

/-- The codimension inequality is imposed only when the inverse image is
nonempty. A point of its boundary forces the stronger bound by m-1. -/
def transverse_preimage_dimensionType : Prop :=
  ∀ {m n k : ℕ} {a b c : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (s : Set N) (R : SmoothManifold k c s) (f : M → N)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S)),
    intrinsicBoundary T = ∅ → intrinsicBoundary R = ∅ →
    IsSmoothEmbedding R T Subtype.val → IsSmoothMap S T f →
    IsNaturalBoundaryStructure S B → IsTransverse S T R f →
    IsTransverse B T R (fun q => f q.val) →
      ((f ⁻¹' s).Nonempty → n - k ≤ m) ∧
      (m < n - k → f ⁻¹' s = ∅) ∧
      ((f ⁻¹' s ∩ intrinsicBoundary S).Nonempty → 0 < m ∧ n - k ≤ m - 1)

/-- The full transverse inverse image theorem on the exact inverse-image
subspace, including empty inverse images and codimension zero. The uniform
model kind is inherited from M. Boundary is intrinsic, rather than frontier. -/
def transverse_preimage_structureType : Prop :=
  ∀ {m n k : ℕ} {a b c : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (s : Set N) (R : SmoothManifold k c s) (f : M → N)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S)),
    intrinsicBoundary T = ∅ → intrinsicBoundary R = ∅ →
    IsSmoothEmbedding R T Subtype.val → IsSmoothMap S T f →
    IsNaturalBoundaryStructure S B → IsTransverse S T R f →
    IsTransverse B T R (fun q => f q.val) →
    ∃ P : SmoothManifold (m - (n - k)) a (f ⁻¹' s),
      IsSmoothEmbedding P S Subtype.val ∧
      intrinsicBoundary P = Subtype.val ⁻¹' intrinsicBoundary S ∧
      ((f ⁻¹' s).Nonempty → (m - (n - k)) + (n - k) = m)

/-- Once an expected-dimensional embedded structure has been constructed,
full transversality identifies its full tangent image. This applies even at
boundary points and keeps all normal vectors; the boundary hypothesis is used
for constructing the structure, not for this stronger tangent assertion. -/
def transverse_preimage_tangentType : Prop :=
  ∀ {m n k : ℕ} {a b c d : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (s : Set N) (R : SmoothManifold k c s) (f : M → N),
    intrinsicBoundary T = ∅ → intrinsicBoundary R = ∅ →
    IsSmoothEmbedding R T Subtype.val → IsSmoothMap S T f →
    IsTransverse S T R f →
    ∀ P : SmoothManifold (m - (n - k)) d (f ⁻¹' s),
    IsSmoothEmbedding P S Subtype.val → ∀ p : f ⁻¹' s,
    ∀ (L : TangentSpace S p.val →ₗ[ℝ] TangentSpace T (f p.val))
      (I : TangentSpace R ⟨f p.val, p.property⟩ →ₗ[ℝ] TangentSpace T (f p.val))
      (K : TangentSpace P p →ₗ[ℝ] TangentSpace S p.val),
      IsDifferential S T f p.val L →
      IsDifferential R T Subtype.val ⟨f p.val, p.property⟩ I →
      IsDifferential P S Subtype.val p K →
        Function.Injective K ∧ LinearMap.range K = (LinearMap.range I).comap L

end Specs.SmoothManifolds.Ch04.TransversePreimage
