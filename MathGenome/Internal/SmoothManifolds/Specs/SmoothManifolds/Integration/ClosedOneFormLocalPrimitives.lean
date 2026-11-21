import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.PeriodCriterion

/-! Independent local degree-one Poincaré statement used for M10.07.
The smooth potential is global; its differential agrees with the closed form
on an open neighborhood. The model may be Euclidean or a half-space. -/
set_option autoImplicit false
noncomputable section
namespace Specs.SmoothManifolds.Integration.ClosedOneFormLocalPrimitives
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.ExteriorDerivativeData
  _root_.SmoothManifolds.BundleOperationsData
universe u

def local_primitivesType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C),
    HasExteriorDerivative C (PeriodData.oneField S α.field) 0 →
    ∀ p : M, ∃ (U : Set M) (f : M → ℝ)
      (hf : PartitionData.ScalarSmooth S.smoothStructure.val f),
      IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U, dFunction S f hf q = α.field q

end Specs.SmoothManifolds.Integration.ClosedOneFormLocalPrimitives
