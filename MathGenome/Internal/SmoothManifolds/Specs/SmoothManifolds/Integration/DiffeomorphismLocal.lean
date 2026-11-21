import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.LocalSigned
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.ProductsAndSigns

/-! Local diffeomorphism naturality used in M10.02 (paper.tex 1820–1846).
Both model kinds, all dimensions, true boundaries, and arbitrary continuous
compactly supported top forms are included. -/
set_option autoImplicit false
noncomputable section

namespace Specs.SmoothManifolds.Integration.DiffeomorphismLocal
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.FormPullbackData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.OrientationProductData _root_.SmoothManifolds.LocalIntegrationData
universe u

/-- Continuity is required only of the original form, not its derivatives. -/
def continuous_pullbackType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (F.toEquiv p)),
    (∀ p, IsDifferential S T F.toEquiv p (E p).toLinearMap) →
    ∀ η : CompactTopForm T,
    IsContinuousTopForm (pullbackField S T F.toEquiv (fun p => (E p).toLinearMap) η.field)

/-- The determinant-ray sign is evaluated at the inverse image of the target
point and remains inside the target integral. No constancy hypothesis is added. -/
def coordinate_naturalityType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (F : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (F.toEquiv p)),
    (∀ p, IsDifferential S T F.toEquiv p (E p).toLinearMap) →
    ∀ (η : CompactTopForm T) (o : Orientation S) (q : Orientation T)
    (s : SignedCharts S) (t : SignedCharts T),
    RepresentsSignedCharts o.val s → RepresentsSignedCharts q.val t →
    ∀ (K : FiberCoordinates S) (L : FiberCoordinates T)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val),
    sectionSupport (pullbackField S T F.toEquiv (fun p => (E p).toLinearMap) η.field)
      ⊆ c.source →
    sectionSupport η.field ⊆ d.source →
    coordinateIntegral s K c hc
      (pullbackField S T F.toEquiv (fun p => (E p).toLinearMap) η.field) =
    coordinateIntegral t L d hd
      (fun y => signValue (orientationSign o q E (F.toEquiv.symm y)) • η.field y)

end Specs.SmoothManifolds.Integration.DiffeomorphismLocal
