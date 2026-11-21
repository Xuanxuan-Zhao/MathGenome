import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Topology.Instances.Nat

/-! Independent statements of Sobczyk's theorem, paper.tex:6424–6431.
The scalars include ℝ and ℂ. On the discrete natural numbers C₀(ℕ, 𝕜)
is precisely the space of scalar null sequences, with its supremum norm.
Index n represents manuscript coordinate n + 1.
The extension clause imposes neither closedness of Y nor completeness of E.
-/

noncomputable section
namespace ExpandedFA.Supplements.Sobczyk

universe u v

/-- Scalar null sequences on the discrete natural numbers, with supremum norm. -/
abbrev C0 (𝕜 : Type u) [RCLike 𝕜] := ZeroAtInftyContinuousMap ℕ 𝕜

/-- A bounded projection onto the given subspace: its range is Y, it is the
identity there, and it is idempotent. -/
def IsProjectionOnto {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Y : Submodule 𝕜 E) (P : E →L[𝕜] E) : Prop :=
  LinearMap.range P.toLinearMap = Y ∧
  (∀ y : Y, P (y : E) = (y : E)) ∧ P.comp P = P

namespace Spec

/-- Explicit bridge to the manuscript's scalar null sequences and supremum norm. -/
def SequenceIdentification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ x : ℕ → 𝕜,
      (∃ y : C0 𝕜, (y : ℕ → 𝕜) = x) ↔ Filter.Tendsto x Filter.atTop (nhds 0)) ∧
    ∀ y : C0 𝕜, IsLUB (Set.range fun n => ‖y n‖) ‖y‖

def Extension : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace.SeparableSpace E]
    (Y : Submodule 𝕜 E) (T : Y →L[𝕜] C0 𝕜),
    ∃ S : E →L[𝕜] C0 𝕜,
      (∀ y : Y, S (y : E) = T y) ∧ ‖S‖ ≤ 2 * ‖T‖

def ComplementedCopies : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (Y : Submodule 𝕜 E), IsClosed (Y : Set E) →
    (C0 𝕜 ≃L[𝕜] Y) →
    Y.ClosedComplemented ∧ ∃ P : E →L[𝕜] E, IsProjectionOnto Y P

def IsometricCopies : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (Y : Submodule 𝕜 E), IsClosed (Y : Set E) →
    (C0 𝕜 ≃ₗᵢ[𝕜] Y) →
    ∃ P : E →L[𝕜] E, IsProjectionOnto Y P ∧ ‖P‖ ≤ 2

end Spec
end ExpandedFA.Supplements.Sobczyk
