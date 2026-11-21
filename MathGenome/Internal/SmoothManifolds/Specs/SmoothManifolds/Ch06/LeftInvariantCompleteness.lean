import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.LieBracket
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.MaximalFlow

/-! The Lie-group example at paper.tex:1446. Smoothness below is the all-chart
C-infinity condition for a real-parameter curve, with continuity included.
The family is arbitrary, so the assertions apply to every maximal solution,
independently of its total representative outside the interval. -/
namespace Specs.SmoothManifolds.Ch06.LeftInvariantCompleteness
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.VectorFieldData
  _root_.SmoothManifolds.LieBracketData _root_.SmoothManifolds.MaximalFlowData Set
universe u

def completeType : Prop :=
  ∀ {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    (S : SmoothManifold n .euclidean G) (B : TangentBundleStructure S),
    LieGroupStructure S → ∀ X : SmoothField B, IsLeftInvariant X →
    ∀ F : CurveFamily G, IsMaximalFamily X F →
    ∀ g : G, (F.interval g).carrier = univ

def oneParameterType : Prop :=
  ∀ {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    (S : SmoothManifold n .euclidean G) (B : TangentBundleStructure S),
    LieGroupStructure S → ∀ X : SmoothField B, IsLeftInvariant X →
    ∀ F : CurveFamily G, IsMaximalFamily X F →
      Continuous (F.curve 1) ∧
      (∀ t : ℝ, ∀ e ∈ S.smoothStructure.val, F.curve 1 t ∈ e.source →
        ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (e (F.curve 1 s)).val) t) ∧
      F.curve 1 0 = 1 ∧
      (∀ s t : ℝ, F.curve 1 (s + t) = F.curve 1 s * F.curve 1 t) ∧
      (∀ (g : G) (t : ℝ), F.curve g t = g * F.curve 1 t)

end Specs.SmoothManifolds.Ch06.LeftInvariantCompleteness
