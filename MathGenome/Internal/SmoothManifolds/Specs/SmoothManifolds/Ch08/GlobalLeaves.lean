import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.LeafStructures
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary

/-! M08.03: the universal property of the intrinsic leaves. The source of
an integral immersion may have boundary; local inverses are required only in
its intrinsic interior. No ambient subspace topology on a leaf is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SmoothManifolds.GlobalLeafData
open ModelData AtlasData MapData MapClassData TangentData DifferentialData
  BundleOperationsData CovectorData DistributionData FrobeniusData LeafData BoundaryData Set
universe u

/-- Integral immersions use the full tangent spaces also at source boundary points. -/
def IsIntegralImmersion {n k : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) {a : ModelKind} (R : SmoothManifold k a N)
    (f : N → M) : Prop :=
  IsSmoothMap R S f ∧ IsImmersion R S f ∧
  ∃ L : (x : N) → TangentSpace R x →ₗ[ℝ] TangentSpace S (f x),
    (∀ x, IsDifferential R S f x (L x)) ∧
    ∀ x, LinearMap.range (L x) = D.fiber (f x)

/-- An actual local inverse on open neighborhoods, smooth in both directions. -/
def HasLocalSmoothInverse {k : ℕ} {N P : Type u}
    [TopologicalSpace N] [TopologicalSpace P] {a : ModelKind}
    (R : SmoothManifold k a N) (T : SmoothManifold k .euclidean P)
    (g : N → P) (x : N) : Prop :=
  ∃ h : OpenPartialHomeomorph N P,
    x ∈ h.source ∧ h.source ⊆ manifoldInterior R ∧
    EqOn h g h.source ∧
    ManifoldContDiffOn (⊤ : ℕ∞) R.smoothStructure.val T.smoothStructure.val g h.source ∧
    ManifoldContDiffOn (⊤ : ℕ∞) T.smoothStructure.val R.smoothStructure.val h.symm h.target

/-- Every connected integral immersion through this class has exactly one
smooth lift. Its differential is an isomorphism everywhere, and it has a local
smooth inverse at each interior point (hence everywhere for a Euclidean source). -/
def UniversalIntegralLeaf {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (A : Set (ModelChart n .euclidean M)) (p : M)
    (T : @SmoothManifold k .euclidean (leafSet A k p) (leafTopology A k p)) : Prop :=
  letI := leafTopology A k p
  ∀ {N : Type u} [TopologicalSpace N] [ConnectedSpace N] {a : ModelKind}
    (R : SmoothManifold k a N) (f : N → M), IsIntegralImmersion D R f →
    ∀ x₀ : N, f x₀ ∈ leafSet A k p →
    ∃! g : N → leafSet A k p,
      IsSmoothMap R T g ∧ (∀ x, (g x).val = f x) ∧
      (∀ x, ∃ E : TangentSpace R x ≃ₗ[ℝ] TangentSpace T (g x),
        IsDifferential R T g x E.toLinearMap) ∧
      (∀ x ∈ manifoldInterior R, HasLocalSmoothInverse R T g x) ∧
      (a = .euclidean → ∀ x, HasLocalSmoothInverse R T g x)
end SmoothManifolds.GlobalLeafData

namespace Specs.SmoothManifolds.Ch08.GlobalLeaves
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.DistributionData _root_.SmoothManifolds.FrobeniusData
  _root_.SmoothManifolds.LeafData _root_.SmoothManifolds.GlobalLeafData Set
universe u

/-- The original closed target: existence, partition, full intrinsic structure,
and the universal maximality and uniqueness property. -/
def global_leavesType : Prop :=
  ∀ {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k), IsInvolutive D →
    ∃ A : Set (ModelChart n .euclidean M), IsCountableAdaptedAtlas D A ∧
      (∀ p : M, p ∈ leafSet A k p) ∧
      (∀ p q : M, leafSet A k p = leafSet A k q ∨ Disjoint (leafSet A k p) (leafSet A k q)) ∧
      ∀ p : M,
        ∃ T : @SmoothManifold k .euclidean (leafSet A k p) (leafTopology A k p),
          @ConnectedSpace (leafSet A k p) (leafTopology A k p) ∧
          @TopologicalSpace.IsTopologicalBasis (leafSet A k p) (leafTopology A k p)
            (plaqueBasis A k p) ∧
          HasPlaqueCharts A p T ∧ IsIntegralLeaf D A p T ∧
          UniversalIntegralLeaf D A p T
end Specs.SmoothManifolds.Ch08.GlobalLeaves
