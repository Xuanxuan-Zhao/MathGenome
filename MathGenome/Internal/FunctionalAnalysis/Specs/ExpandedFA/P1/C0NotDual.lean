import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import Mathlib.Topology.Algebra.Module.Complement

/-! Consequences of `fa2:p1:czero-uncomplemented`, paper.tex 4489–4520.
All duals are continuous scalar-linear duals over either scalar field. No
completeness assumption is imposed on a proposed predual. -/
namespace ExpandedFA.P1.C0NotDual

universe u v w
/-- Elaboration alias for the shared continuous dual, retaining the normed
domain instance at each level of iteration. The carrier is exactly E →L[𝕜] 𝕜. -/
abbrev Dual (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] := E →L[𝕜] 𝕜

/-- The shared evaluation map with its normed dual instances explicit. -/
noncomputable abbrev evaluation (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : E →L[𝕜] Dual 𝕜 (Dual 𝕜 E) :=
  C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E

namespace Spec
local notation "D" => Dual
open C01SequenceSpaces

/-- The sequence-dual isometries identify evaluation with the usual inclusion.
The pairing equations fix the identifications, including over complex scalars. -/
def SequenceBidualIdentification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ (U : SequenceLp 𝕜 1 ≃ₗᵢ[𝕜] (D 𝕜 (SequenceC0 𝕜)))
      (V : SequenceLInfinity 𝕜 ≃ₗᵢ[𝕜] (D 𝕜 (SequenceLp 𝕜 1)))
      (W : (D 𝕜 (D 𝕜 (SequenceC0 𝕜))) ≃ₗᵢ[𝕜] SequenceLInfinity 𝕜),
      (∀ a x, U a x = ∑' n, a n * x.val n) ∧
      (∀ b a, V b a = ∑' n, b n * a n) ∧
      (∀ ξ a, V (W ξ) a = ξ (U a)) ∧
      (∀ x, W (evaluation 𝕜 _ x) = x.val)

/-- Every dual has the canonical retraction J_Y′, without assuming Y complete. -/
def DualCanonicalComplement : Prop :=
  ∀ (𝕜 : Type u) (Y : Type v) [RCLike 𝕜]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    ∃ R : (D 𝕜 (D 𝕜 (D 𝕜 (Y)))) →L[𝕜] (D 𝕜 (Y)),
      (∀ ξ y, R ξ y = ξ (evaluation 𝕜 Y y)) ∧
      (∀ f, R (evaluation 𝕜 _ f) = f) ∧
      (evaluation 𝕜 (D 𝕜 (Y))).range.ClosedComplemented

/-- Canonical complementability passes through arbitrary bounded linear
isomorphisms, with no isometry or completeness assumptions. -/
def CanonicalComplementInvariance : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (_T : E ≃L[𝕜] F),
    (evaluation 𝕜 E).range.ClosedComplemented ↔
      (evaluation 𝕜 F).range.ClosedComplemented

def CanonicalImageNotComplemented : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ (evaluation 𝕜 (SequenceC0 𝕜)).range.ClosedComplemented

def NotIsomorphicToDual : Prop :=
  ∀ (𝕜 : Type u) (Y : Type v) [RCLike 𝕜]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    ¬ Nonempty (SequenceC0 𝕜 ≃L[𝕜] (D 𝕜 (Y)))

end Spec
end ExpandedFA.P1.C0NotDual
