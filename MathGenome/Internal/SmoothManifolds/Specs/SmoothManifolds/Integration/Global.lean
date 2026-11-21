import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.LocalSigned
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.Partitions
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.ProductsAndSigns
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import Mathlib.Topology.Compactness.LocallyFinite

/-! Independent statements of M10.02 and the support paragraph following it.
All sections are the original exterior covector fields. Linearity is stated
on the existing bundled `CompactTopForm`, by equations of their fields, so no
second representation of compactly supported forms is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Topology BigOperators

namespace SmoothManifolds.GlobalIntegrationData
open ModelData AtlasData TangentData TangentBundleData ExteriorData FormPullbackData
  OrientationData LocalIntegrationData Set
universe u v

/-- Continuous localizers; their closed supports are subordinate and locally
finite. They need sum to one only on an open neighborhood of this form's support.
Nonnegativity and differentiability are not required by the localization identity. -/
def IsLocalization {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} (c : ι → ModelChart n a M)
    (ρ : ι → M → ℝ) (ω : CompactTopForm S) : Prop :=
  (∀ i, Continuous (ρ i)) ∧ LocallyFinite (fun i => sectionSupport (ρ i)) ∧
  (∀ i, sectionSupport (ρ i) ⊆ (c i).source) ∧
  ∃ V : Set M, IsOpen V ∧ sectionSupport ω.field ⊆ V ∧
    ∀ p ∈ V, ∑ᶠ i, ρ i p = 1

/-- A real linear integral agreeing with every signed coordinate integral.
The field equations express the existing pointwise vector-space operations. -/
def IsIntegral {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (o : Orientation S) (I : CompactTopForm S → ℝ) : Prop :=
  (∀ (α β γ : CompactTopForm S), γ.field = α.field + β.field → I γ = I α + I β) ∧
  (∀ (r : ℝ) (α β : CompactTopForm S), β.field = r • α.field → I β = r * I α) ∧
  ∀ (s : SignedCharts S), RepresentsSignedCharts o.val s →
    ∀ (K : FiberCoordinates S) (c : ModelChart n a M)
      (hc : c ∈ S.smoothStructure.val) (ω : CompactTopForm S),
      sectionSupport ω.field ⊆ c.source → I ω = coordinateIntegral s K c hc ω.field

end SmoothManifolds.GlobalIntegrationData

namespace Specs.SmoothManifolds.Integration.Global
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.FormPullbackData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.OrientationProductData _root_.SmoothManifolds.LocalIntegrationData
  _root_.SmoothManifolds.GlobalIntegrationData _root_.SmoothManifolds.BoundaryData Set
universe u v

/-- Sums and continuous scalar localizers stay in the original space of forms. -/
def algebraType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (α β : CompactTopForm S),
    (∃ γ : CompactTopForm S, γ.field = α.field + β.field) ∧
    ∀ (ρ : M → ℝ), Continuous ρ →
      ∃ γ : CompactTopForm S, γ.field = fun p => ρ p • α.field p

def weight_supportType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (k : ℕ) (ω : Field S k) (ρ : M → ℝ),
    sectionSupport (fun p => ρ p • ω p) ⊆ sectionSupport ρ ∩ sectionSupport ω

def finite_localizersType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) {ι : Type v} (ρ : ι → M → ℝ),
    LocallyFinite (fun i => sectionSupport (ρ i)) → ∀ ω : CompactTopForm S,
      {i | (sectionSupport (ρ i) ∩ sectionSupport ω.field).Nonempty}.Finite

/-- Existence and uniqueness hold on empty manifolds, boundary manifolds, and in
all dimensions, including dimension zero. -/
def exists_integralType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (o : Orientation S),
    ∃! I : CompactTopForm S → ℝ, IsIntegral o I

/-- Uniqueness for every linear coordinate-compatible integral. -/
def uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (o : Orientation S) (I J : CompactTopForm S → ℝ),
    IsIntegral o I → IsIntegral o J → I = J

/-- This includes arbitrary locally finite smooth subordinate partitions, and
continuous weights summing to one only near the particular compact support. -/
def localizationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (o : Orientation S) (I : CompactTopForm S → ℝ),
    IsIntegral o I → ∀ (s : SignedCharts S), RepresentsSignedCharts o.val s →
    ∀ (K : FiberCoordinates S) {ι : Type v} (c : ι → ModelChart n a M)
      (hc : ∀ i, c i ∈ S.smoothStructure.val) (ρ : ι → M → ℝ) (ω : CompactTopForm S),
      IsLocalization c ρ ω → I ω =
        ∑ᶠ i, coordinateIntegral s K (c i) (hc i) (fun p => ρ i p • ω.field p)

/-- The opposite orientation is expressed on the actual determinant rays. -/
def reversalType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (o q : Orientation S),
    (∀ p, q.val p = -o.val p) → ∀ (I J : CompactTopForm S → ℝ),
      IsIntegral o I → IsIntegral q J → ∀ ω, J ω = -I ω

def zero_dimensionType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (o : Orientation S) (I : CompactTopForm S → ℝ),
    IsIntegral o I → ∀ ω, I ω = zeroIntegral o ω.field

/-- Explicit finite-sum interpretation of the zero-dimensional integral. -/
def zero_finite_sumType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (o : Orientation S) (I : CompactTopForm S → ℝ),
    IsIntegral o I → ∀ ω : CompactTopForm S,
    ∃ h : (sectionSupport ω.field).Finite,
      I ω = ∑ p ∈ h.toFinset, zeroSign o p * zeroCoefficient ω.field p

/-- Support inclusion is valid for every continuous map and every family of
linear fiber maps, without claiming compactness of arbitrary inverse images. -/
def pullback_supportType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N),
    Continuous f → ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
      (k : ℕ) (ω : Field T k),
      sectionSupport (pullbackField S T f L ω) ⊆ f ⁻¹' sectionSupport ω

/-- Compactness for diffeomorphisms: no arbitrary smooth pullback claim. -/
def diffeomorphism_supportType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (F.toEquiv p))
    (k : ℕ) (ω : Field T k), IsCompact (sectionSupport ω) →
      IsCompact (sectionSupport (pullbackField S T F.toEquiv L ω))

/-- This general closed-embedding version includes closed embedded submanifolds.
It is stronger than the smooth case because support only needs topology and
linearity of the fiber maps. -/
def closed_embedding_supportType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (i : M → N),
    Topology.IsClosedEmbedding i →
    ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (i p))
      (k : ℕ) (ω : Field T k),
      sectionSupport (pullbackField S T i L ω) ⊆ i ⁻¹' sectionSupport ω ∧
      (IsCompact (sectionSupport ω) →
        IsCompact (sectionSupport (pullbackField S T i L ω)))

/-- In the induced subspace topology the support lies in the intersection with
the ambient compact support. This applies explicitly to the intrinsic boundary. -/
def boundary_supportType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M) (B : SmoothManifold n .euclidean (intrinsicBoundary S))
    (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (k : ℕ) (ω : Field S k),
    sectionSupport (pullbackField B S Subtype.val L ω) ⊆ Subtype.val ⁻¹' sectionSupport ω ∧
    (IsCompact (sectionSupport ω) →
      IsCompact (sectionSupport (pullbackField B S Subtype.val L ω)))

/-- Continuous top forms pull back continuously along a diffeomorphism. The
actual full intrinsic differential is explicit; its existence is upstream. -/
def diffeomorphism_formType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (E : (p : M) → TangentSpace S p ≃ₗ[ℝ] TangentSpace T (F.toEquiv p)),
    (∀ p, IsDifferential S T F.toEquiv p (E p).toLinearMap) →
    ∀ η : CompactTopForm T, ∃ ξ : CompactTopForm S,
      ξ.field = pullbackField S T F.toEquiv (fun p => (E p).toLinearMap) η.field

/-- The variable sign is locally constant, hence constant on each component. -/
def component_signType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (o : Orientation S) (q : Orientation T)
    (E : (p : M) → TangentSpace S p ≃ₗ[ℝ] TangentSpace T (F.toEquiv p)),
    (∀ p, IsDifferential S T F.toEquiv p (E p).toLinearMap) →
    IsLocallyConstant (orientationSign o q E) ∧
    ∀ p x, x ∈ connectedComponent p → orientationSign o q E x = orientationSign o q E p

/-- Componentwise substitution means integrating the target form multiplied by
the sign on the source component of its inverse image. -/
def substitutionType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (o : Orientation S) (q : Orientation T)
    (E : (p : M) → TangentSpace S p ≃ₗ[ℝ] TangentSpace T (F.toEquiv p)),
    (∀ p, IsDifferential S T F.toEquiv p (E p).toLinearMap) →
    ∀ (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ),
    IsIntegral o I → IsIntegral q J → ∀ (η : CompactTopForm T) (ξ : CompactTopForm S),
    ξ.field = pullbackField S T F.toEquiv (fun p => (E p).toLinearMap) η.field →
    ∃ θ : CompactTopForm T,
      θ.field = (fun y => signValue (orientationSign o q E (F.toEquiv.symm y)) • η.field y) ∧
      I ξ = J θ

/-- The two constant-sign cases, for the original diffeomorphism and orientations. -/
def constant_sign_substitutionType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (o : Orientation S) (q : Orientation T)
    (E : (p : M) → TangentSpace S p ≃ₗ[ℝ] TangentSpace T (F.toEquiv p)),
    (∀ p, IsDifferential S T F.toEquiv p (E p).toLinearMap) →
    ∀ (ε : Bool), (∀ p, orientationSign o q E p = ε) →
    ∀ (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ),
    IsIntegral o I → IsIntegral q J → ∀ (η : CompactTopForm T) (ξ : CompactTopForm S),
    ξ.field = pullbackField S T F.toEquiv (fun p => (E p).toLinearMap) η.field →
      I ξ = signValue ε * J η

end Specs.SmoothManifolds.Integration.Global
