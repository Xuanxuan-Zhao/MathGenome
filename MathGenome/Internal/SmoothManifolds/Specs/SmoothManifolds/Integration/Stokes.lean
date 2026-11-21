import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.Global
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.ExteriorDerivative
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Boundary

/-! Independent statements for paper.tex:1885–1925 (M10.04).
The forms are the original intrinsic exterior sections. C¹ means local C¹
extensions of their coordinate coefficients, including at the true boundary.
The derivative and boundary restriction are required to be actual compact
continuous top forms, so both integrals use the existing global integral.
No localization or Stokes certificate is part of the hypotheses.
-/
set_option autoImplicit false
noncomputable section

namespace Specs.SmoothManifolds.Integration.Stokes
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.ExteriorDerivativeData
  _root_.SmoothManifolds.FormPullbackData _root_.SmoothManifolds.LocalIntegrationData
  _root_.SmoothManifolds.GlobalIntegrationData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.BoundaryOrientationData Set
universe u

/-- C¹ exterior differentiation produces a unique compact continuous top form,
with its support contained in the original closed support. -/
def derivative_top_formType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M) (C : CotangentBundle S) (ω : Field S n),
    IsRegularField C 1 n ω → IsCompact (sectionSupport ω) →
    ∃! η : CompactTopForm S, HasExteriorDerivative C ω η.field ∧
      sectionSupport η.field ⊆ sectionSupport ω

/-- Boundary restriction is C¹ and compactly supported on the actual closed
boundary, and is an integrable top form there. -/
def boundary_top_formType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M) (C : CotangentBundle S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (A : CotangentBundle B),
    IsNaturalBoundary S B →
    ∀ (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
    (∀ p, IsDifferential B S Subtype.val p (L p)) → ∀ (ω : Field S n),
    IsRegularField C 1 n ω → IsCompact (sectionSupport ω) →
    ∃ β : CompactTopForm B, β.field = pullbackField B S Subtype.val L ω ∧
      IsRegularField A 1 n β.field ∧
      sectionSupport β.field ⊆ Subtype.val ⁻¹' sectionSupport ω

/-- Abstract Stokes in every positive dimension, including n+1=1. Natural
boundary structures, their actual inclusion differentials, and the existing
coordinate-compatible integral are explicit representations of the canonical
objects supplied upstream. No interior-support assumption is imposed. -/
def stokesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M) (C : CotangentBundle S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (A : CotangentBundle B),
    IsNaturalBoundary S B → ∀ (o : Orientation S) (q : Orientation B),
    IsInducedOrientation o q →
    ∀ (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
    (∀ p, IsDifferential B S Subtype.val p (L p)) →
    ∀ (I : CompactTopForm S → ℝ) (J : CompactTopForm B → ℝ),
    IsIntegral o I → IsIntegral q J → ∀ (ω : Field S n),
    IsRegularField C 1 n ω → IsCompact (sectionSupport ω) →
    ∃ (η : CompactTopForm S) (β : CompactTopForm B),
      HasExteriorDerivative C ω η.field ∧
      sectionSupport η.field ⊆ sectionSupport ω ∧
      β.field = pullbackField B S Subtype.val L ω ∧ I η = J β

/-- Compactness of M makes the original support hypothesis automatic, for all
fields and hence for every C¹ form. -/
def compact_supportType : Prop :=
  ∀ {d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold d a M) (k : ℕ) (ω : Field S k),
    IsCompact (sectionSupport ω)

/-- The integral over an empty intrinsic boundary is zero, in every dimension
and for the original coordinate-compatible functional. -/
def empty_boundary_integralType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold (n+1) a M)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (q : Orientation B)
    (J : CompactTopForm B → ℝ), IsIntegral q J → intrinsicBoundary S = ∅ →
      ∀ β : CompactTopForm B, J β = 0

end Specs.SmoothManifolds.Integration.Stokes
