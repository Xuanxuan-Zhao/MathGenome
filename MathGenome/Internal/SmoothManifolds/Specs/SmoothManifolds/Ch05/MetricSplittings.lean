import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleMetrics
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleOperations
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Projection

/-! Independent statements for M05.05, orthogonal splitting, exact sequences,
and metric duality. All smoothness is the shared ambient-extension smoothness.
No restriction on the base model, its nonemptiness, or the bundle ranks is made. -/
namespace SmoothManifolds.MetricSplittingData
open ModelData AtlasData MapData BundleData BundleMetricData BundleOperationsData
  ConstantRankData Bundle
universe u v w z t

section
variable {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {κ : Type t}
  {E : M → Type w} {F : M → Type z}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  [TopologicalSpace (TotalSpace (Euclidean s) F)]

/-- A genuine fiberwise linear isomorphism whose two actual total-space maps
are smooth, over the identity of the specified base. -/
structure SmoothBundleIso (B : SmoothVectorBundle S r ι E)
    (D : SmoothVectorBundle S s κ F) where
  equiv : (p : M) → E p ≃ₗ[ℝ] F p
  smooth : IsSmoothMap B.totalManifold D.totalManifold
    (fun q => (⟨q.proj, equiv q.proj q.snd⟩ : TotalSpace (Euclidean s) F))
  inverse_smooth : IsSmoothMap D.totalManifold B.totalManifold
    (fun q => (⟨q.proj, (equiv q.proj).symm q.snd⟩ : TotalSpace (Euclidean r) E))

end

section
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

/-- The actual metric orthogonal subspaces. -/
def orthogonal (g : SmoothFiberMetric B) (K : (p : M) → Submodule ℝ (E p))
    (p : M) : Submodule ℝ (E p) := (g.form p).orthogonal (K p)

/-- The canonical sum isomorphism, together with smooth induced bundles on the
actual two subspaces. The inclusion of each summand is smooth in the ambient
bundle. The direct-sum structure is the canonical construction of M05.04. -/
structure OrthogonalSplitting (g : SmoothFiberMetric B)
    (K : (p : M) → Submodule ℝ (E p)) (k : ℕ) where
  complement_smooth : IsSmoothSubbundle B (r-k) (orthogonal B g K)
  complementary : ∀ p, IsCompl (K p) (orthogonal B g K p)
  left : BundleSpace S k M (fun p => K p)
  right : BundleSpace S (r-k) M (fun p => orthogonal B g K p)
  left_inclusion : letI := left.topology
    IsSmoothMap left.bundle.totalManifold B.totalManifold
      (fun q => (⟨q.proj, q.snd.val⟩ : TotalSpace (Euclidean r) E))
  right_inclusion : letI := right.topology
    IsSmoothMap right.bundle.totalManifold B.totalManifold
      (fun q => (⟨q.proj, q.snd.val⟩ : TotalSpace (Euclidean r) E))
  sum : letI := left.topology; letI := right.topology
    DirectSumBundle left.bundle right.bundle
  iso : letI := left.topology; letI := right.topology; letI := sum.space.topology
    SmoothBundleIso sum.space.bundle B
  canonical : letI := left.topology; letI := right.topology; letI := sum.space.topology
    ∀ p v, iso.equiv p v = v.1.val + v.2.val

end
end SmoothManifolds.MetricSplittingData

namespace Specs.SmoothManifolds.Ch05.MetricSplittings
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BundleData _root_.SmoothManifolds.BundleMetricData
  _root_.SmoothManifolds.ConstantRankData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.MetricSplittingData Bundle
universe u v w z t x y

/-- Orthogonal complements and the canonical smooth direct-sum isomorphism. -/
def orthogonal_splittingType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (g : SmoothFiberMetric B)
    (K : (p : M) → Submodule ℝ (E p)) (k : ℕ),
    IsSmoothSubbundle B k K → Nonempty (OrthogonalSplitting B g K k)

/-- Every short exact sequence splits by a smooth right inverse. Its canonical
map L ⊕ F → E is moreover a smooth bundle isomorphism. Only fiberwise exactness,
injectivity and surjectivity are assumed, in addition to smoothness. -/
def shortExact_splittingType : Prop :=
  ∀ {n l r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type t} {κ : Type v} {τ : Type y}
    {L : M → Type z} {E : M → Type w} {F : M → Type x}
    [∀ p, AddCommGroup (L p)] [∀ p, Module ℝ (L p)]
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (F p)] [∀ p, Module ℝ (F p)]
    [TopologicalSpace (TotalSpace (Euclidean l) L)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    [TopologicalSpace (TotalSpace (Euclidean s) F)]
    (A : SmoothVectorBundle S l ι L) (B : SmoothVectorBundle S r κ E)
    (D : SmoothVectorBundle S s τ F)
    (i : SmoothBundleMorphism A B) (q : SmoothBundleMorphism B D),
    (∀ p, Function.Injective (i.linearMap p)) →
    (∀ p, Function.Surjective (q.linearMap p)) →
    (∀ p, LinearMap.range (i.linearMap p) = LinearMap.ker (q.linearMap p)) →
    ∃ t : SmoothBundleMorphism D B,
      (∀ p, (q.linearMap p).comp (t.linearMap p) = LinearMap.id) ∧
      ∀ V : DirectSumBundle A D, letI := V.space.topology
      ∃ e : SmoothBundleIso V.space.bundle B,
        ∀ p v, e.equiv p v = i.linearMap p v.1 + t.linearMap p v.2

/-- Specialization to the actual sigma tangent bundle and the canonical
cotangent fibers, using the smooth realization maps of M05.04. -/
def tangentMetricDualityType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S),
    letI := C.realization.space.topology
    ∀ g : SmoothFiberMetric C.realization.space.bundle,
    letI := C.tangent.topology
    letI := C.dual.space.topology
    ∃ e : (p : M) → TangentData.TangentSpace S p ≃ₗ[ℝ] CotangentFiber S p,
      (∀ p x y, e p x y = g.form p x y) ∧
      IsSmoothMap C.tangent.manifold C.dual.space.bundle.totalManifold
        (fun q : TangentBundleData.TotalSpace S =>
          (⟨q.1, e q.1 q.2⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S))) ∧
      IsSmoothMap C.dual.space.bundle.totalManifold C.tangent.manifold
        (fun q : Bundle.TotalSpace (Euclidean n) (CotangentFiber S) =>
          (⟨q.proj, (e q.proj).symm q.snd⟩ : TangentBundleData.TotalSpace S))

/-- The metric map is prescribed on all vectors and covectors. Smoothness of
both directions is asserted for any dual bundle with the canonical coordinates. -/
def metric_dualityType : Prop :=
  (∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (g : SmoothFiberMetric B) (D : DualBundle B),
    letI := D.space.topology
    ∃ e : SmoothBundleIso B D.space.bundle,
      ∀ p x y, e.equiv p x y = g.form p x y) ∧ tangentMetricDualityType.{u}

end Specs.SmoothManifolds.Ch05.MetricSplittings
