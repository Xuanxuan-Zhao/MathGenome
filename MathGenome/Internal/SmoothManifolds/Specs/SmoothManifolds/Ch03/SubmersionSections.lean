import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary

/-! Sections are represented by total maps whose restriction to the indicated
open neighborhood is smooth and a right inverse. No condition is imposed outside
that neighborhood. Boundarylessness means empty intrinsic boundary, so either
permitted chart model and dimension zero are covered. -/
set_option autoImplicit false
namespace Specs.SmoothManifolds.Ch03.SubmersionSections
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.MapClassData Set
universe u v

def local_sectionType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N),
    intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ →
    IsSmoothMap S T q → IsSubmersion S T q →
    ∀ x : M, ∃ U : Set N, IsOpen U ∧ q x ∈ U ∧
      ∃ s : N → M, ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val s U ∧
        (∀ y ∈ U, q (s y) = y) ∧ s (q x) = x

def isOpenMapType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N),
    intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ →
    IsSmoothMap S T q → IsSubmersion S T q → IsOpenMap q
end Specs.SmoothManifolds.Ch03.SubmersionSections
