import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.LocalSigned
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.Partitions

/-! Existence part of M10.02. No chosen localization or integral is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Specs.SmoothManifolds.Integration.GlobalConstruction
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.LocalIntegrationData
universe u

def exists_integralType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (o : Orientation S),
    ∃ I : CompactTopForm S → ℝ,
      (∀ (α β γ : CompactTopForm S), γ.field = α.field + β.field → I γ = I α + I β) ∧
      (∀ (r : ℝ) (α β : CompactTopForm S), β.field = r • α.field → I β = r * I α) ∧
      ∀ (s : SignedCharts S), RepresentsSignedCharts o.val s →
        ∀ (K : FiberCoordinates S) (c : ModelChart n a M)
          (hc : c ∈ S.smoothStructure.val) (ω : CompactTopForm S),
          sectionSupport ω.field ⊆ c.source →
            I ω = coordinateIntegral s K c hc ω.field

end Specs.SmoothManifolds.Integration.GlobalConstruction
