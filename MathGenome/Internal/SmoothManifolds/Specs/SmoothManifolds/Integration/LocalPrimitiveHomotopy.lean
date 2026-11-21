import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.PathIntegration
import Mathlib.Topology.UnitInterval

/-! M10.07: the continuous-homotopy bridge from local smooth potentials.
The homotopy has no differentiability hypothesis. All intervals may degenerate,
and every upstream model kind and dimension is permitted. -/
set_option autoImplicit false
noncomputable section
namespace Specs.SmoothManifolds.Integration.LocalPrimitiveHomotopy
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.PartitionData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.PathIntegrationData Set
universe u

def homotopy_invarianceType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (α : CovectorField S),
    (∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ (f : M → ℝ) (hf : ScalarSmooth S.smoothStructure.val f),
        ∀ q ∈ U, dFunction S f hf q = α q) →
    ∀ (γ η : ℝ → M) (a b c d : ℝ), a ≤ b → c ≤ d →
      PiecewiseSmoothOn S γ a b → PiecewiseSmoothOn S η c d →
      ∀ H : unitInterval × unitInterval → M, Continuous H →
        (∀ s, H (0, s) = γ (a + (b-a) * s.val)) →
        (∀ s, H (1, s) = η (c + (d-c) * s.val)) →
        (∀ t, H (t, 0) = γ a) → (∀ t, H (t, 1) = γ b) →
        pathIntegral S α γ a b = pathIntegral S α η c d

/-- FTC localized only along the image of the path. -/
def integral_local_potentialType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (α : CovectorField S)
    (f : M → ℝ) (hf : ScalarSmooth S.smoothStructure.val f)
    (γ : ℝ → M) (a b : ℝ), PiecewiseSmoothOn S γ a b →
    (∀ t ∈ Icc a b, dFunction S f hf (γ t) = α (γ t)) →
      pathIntegral S α γ a b = f (γ b) - f (γ a)

end Specs.SmoothManifolds.Integration.LocalPrimitiveHomotopy
