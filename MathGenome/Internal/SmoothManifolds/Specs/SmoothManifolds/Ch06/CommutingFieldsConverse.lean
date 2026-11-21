import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.CommutingFields

namespace Specs.SmoothManifolds.Ch06.CommutingFieldsConverse

open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.VectorFieldData
  _root_.SmoothManifolds.LieBracketData _root_.SmoothManifolds.MaximalFlowData
  _root_.SmoothManifolds.CommutingFieldsData

universe u

def bracket_zero_of_commute_nearType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ (X Y : SmoothField B) (F G : CurveFamily M),
      IsMaximalFamily X F → IsMaximalFamily Y G →
      ∀ p : M, CommuteNear F G p → (b X Y).val p = 0

end Specs.SmoothManifolds.Ch06.CommutingFieldsConverse
