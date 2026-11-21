import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.CompactSupport
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.Global

/-! Independent original statements for the oriented compact-support and compact
clauses of M11.07 (paper.tex:2503–2541). The model may be either uniform model;
absence of the intrinsic boundary is explicit. ConnectedSpace includes
nonemptiness. No compactness or global-coordinate assumption occurs in the
compact-support assertion.

The integral interface uses compact continuous top forms. Existentially bundling
each smooth representative in that SAME interface avoids introducing a second
integral. Equality of fields determines the bundle uniquely. -/
set_option autoImplicit false
noncomputable section
namespace Specs.SmoothManifolds.DeRham.OrientedTopDegree
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.DeRhamData _root_.SmoothManifolds.MayerVietorisData
  _root_.SmoothManifolds.CompactSupportData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.LocalIntegrationData
  _root_.SmoothManifolds.GlobalIntegrationData _root_.SmoothManifolds.BoundaryData
universe u

/-- Integration itself induces the isomorphism on the full compact complex. -/
def top_degreeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n a M), intrinsicBoundary S = ∅ →
    ∀ (o : Orientation S) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
      (K : Calculus C B) (D : CompactCalculus K ⊤) (I : CompactTopForm S → ℝ),
      IsIntegral o I → ∃ e : D.Cohomology n ≃ₗ[ℝ] ℝ,
        ∀ ω : D.complex.closed n, ∃ η : CompactTopForm S,
          η.field = (D.inclusion.map n ω.val).val ∧
          e (D.complex.classOf n ω) = I η

/-- Exactness is in the COMPACT complex. At n=0 its exact submodule is zero. -/
def exact_iff_integral_zeroType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n a M), intrinsicBoundary S = ∅ →
    ∀ (o : Orientation S) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
      (K : Calculus C B) (D : CompactCalculus K ⊤) (I : CompactTopForm S → ℝ),
      IsIntegral o I → ∀ ω : D.complex.Obj n, ∃ η : CompactTopForm S,
        η.field = (D.inclusion.map n ω).val ∧
        (ω ∈ D.complex.exact n ↔ I η = 0)

/-- On a compact manifold the inclusion identifies the ENTIRE complexes,
with the corresponding representative formula on cohomology, in every degree. -/
def compact_comparisonType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (D : CompactCalculus K ⊤),
    (∀ k, Function.Bijective (D.inclusion.map k)) ∧
    ∀ k, ∃ e : D.Cohomology k ≃ₗ[ℝ] K.Cohomology k,
      ∀ ω : D.complex.closed k,
        e (D.complex.classOf k ω) = K.classOf k (D.inclusion.onClosed k ω)

/-- Integration on the ordinary de Rham quotient of a compact manifold. -/
def compact_top_degreeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [ConnectedSpace M] [CompactSpace M]
    (S : SmoothManifold n a M), intrinsicBoundary S = ∅ →
    ∀ (o : Orientation S) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
      (K : Calculus C B) (I : CompactTopForm S → ℝ), IsIntegral o I →
      ∃ e : K.Cohomology n ≃ₗ[ℝ] ℝ, ∀ ω : K.closed n,
        ∃ η : CompactTopForm S, η.field = ω.val.val ∧ e (K.classOf n ω) = I η

/-- A connected zero-manifold is a point. Its integral is SIGNED evaluation,
and a compact zero-form is exact precisely when its actual field vanishes. -/
def zero_dimensionType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold 0 a M) (o : Orientation S) (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (K : Calculus C B) (D : CompactCalculus K ⊤)
    (I : CompactTopForm S → ℝ), IsIntegral o I →
    Subsingleton M ∧ ∀ (ω : D.complex.Obj 0) (p : M),
      ∃ η : CompactTopForm S, η.field = (D.inclusion.map 0 ω).val ∧
        I η = zeroSign o p * zeroCoefficient η.field p ∧
        (ω ∈ D.complex.exact 0 ↔ (D.inclusion.map 0 ω).val = 0)

end Specs.SmoothManifolds.DeRham.OrientedTopDegree
