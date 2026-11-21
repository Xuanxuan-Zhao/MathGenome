import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.EmbeddedAtlas
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.ExteriorDerivative

/-! Independent statements for the analytic part of M10.08.
The hypotheses describe the original induced smooth structure and the inclusion
identification. They assume no regularity or derivative compatibility. D04's
predicates below retain their quantifiers over every C² embedded chart.
These statements include empty manifolds, dimension zero, degree zero and all
higher degrees, without compactness or orientation assumptions. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace Specs.SmoothManifolds.Integration.EmbeddedDerivative
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.ExteriorDerivativeData
  _root_.SmoothManifolds.EmbeddedCalculusData _root_.SmoothManifolds.EmbeddedAtlasData
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model

/-- Local C¹ extendibility of coefficients agrees in the original two models.
In particular the right side tests all C² charts, including nonsmooth ones. -/
def regularity_transportType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ n M →
    ∀ (S : SmoothManifold n a M), IsInducedSmoothStructure S →
    ∀ (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val),
    IsInclusionIdentification S I → ∀ (C : CotangentBundle S) (k : ℕ) (ξ : Field S k),
      IsRegularField C 1 k ξ ↔
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicC1
          (transportField S I k ξ)

/-- The continuity bridge does not require differentiability of the field. -/
def continuous_transportType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ n M →
    ∀ (S : SmoothManifold n a M), IsInducedSmoothStructure S →
    ∀ (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val),
    IsInclusionIdentification S I → ∀ (C : CotangentBundle S) (k : ℕ) (ξ : Field S k),
      IsContinuousField C k ξ ↔
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicContinuous
          (transportField S I k ξ)

/-- Equality of the full chart characterizations. Continuity of the derivative
is a conclusion on the D04 side; the intrinsic C¹ theorem supplies it on the
abstract side. No assumed derivative or coefficient compatibility is added. -/
def hasDerivative_transportType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ n M →
    ∀ (S : SmoothManifold n a M), IsInducedSmoothStructure S →
    ∀ (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val),
    IsInclusionIdentification S I → ∀ (C : CotangentBundle S) (k : ℕ)
    (ξ : Field S k) (η : Field S (k+1)), IsRegularField C 1 k ξ →
      (HasExteriorDerivative C ξ η ↔
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicContinuous
          (transportField S I (k+1) η) ∧
        Specs.D04.C15.IntrinsicExteriorDerivative.Model.HasIntrinsicExteriorDerivative
          (transportField S I k ξ) (transportField S I (k+1) η))

/-- Agreement with the literal D04 total selector, on its common C¹ domain.
The derivative field exists uniquely and has continuous intrinsic coefficients. -/
def intrinsicExteriorDerivative_transportType : Prop :=
  ∀ {n N : ℕ} {a : ModelKind} {M : Set (E N)}, IsEmbeddedManifold ∞ n M →
    ∀ (S : SmoothManifold n a M), IsInducedSmoothStructure S →
    ∀ (I : (p : M) → TangentSpace S p ≃ₗ[ℝ] tangentSpace 2 n M p.val),
    IsInclusionIdentification S I → ∀ (C : CotangentBundle S) (k : ℕ)
    (ξ : Field S k), IsRegularField C 1 k ξ →
      ∃! η : Field S (k+1),
        IsContinuousField C (k+1) η ∧ HasExteriorDerivative C ξ η ∧
        transportField S I (k+1) η =
          Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicExteriorDerivative
            (transportField S I k ξ)

end Specs.SmoothManifolds.Integration.EmbeddedDerivative
