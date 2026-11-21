import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
Independent specifications for compactness, weak compactness, and complete continuity
in paper.tex:9423–9430,9458–9486,9573–9609,10321–10326.

Scalars are real or complex and duals are scalar-linear norm-continuous duals.
Compact closure is taken in the original target, including when it is incomplete.
Weak closure uses the previously specified topology of the evaluation pairing.
Complete continuity concerns sequences with their specified limit.

The definitions make sense for normed spaces; in particular they apply to all
Banach spaces in the compactness chapter. No completeness, nonzero-space, or
nonempty-set assumptions are needed for these definitions or the bridges below.
-/

namespace ExpandedFA.Compactness.DefinitionsSpec

universe u v w
open Filter
open scoped Topology
noncomputable section

def IsCompactLinearMapType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], (E →ₗ[𝕜] F) → Prop

def IsCompactLinearMapValue : IsCompactLinearMapType :=
  fun {_} _ {E} {_} _ _ _ _ T =>
    IsCompact (closure (T '' Metric.closedBall (0 : E) 1))

def IsWeaklyCompactOperatorType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], (E →L[𝕜] F) → Prop

/-- Both closure and compactness use σ(F,F'); the dual is formed using the norm. -/
def IsWeaklyCompactOperatorValue : IsWeaklyCompactOperatorType :=
  fun {𝕜} _ {E} {F} _ _ _ _ T =>
    @IsCompact F (P1.C12DualPairSpec.DualPairTopologyValue
      𝕜 F (F →L[𝕜] 𝕜) (topDualPairing 𝕜 F))
      (@closure F (P1.C12DualPairSpec.DualPairTopologyValue
        𝕜 F (F →L[𝕜] 𝕜) (topDualPairing 𝕜 F))
        (T '' Metric.closedBall (0 : E) 1))

def IsCompletelyContinuousType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], (E →L[𝕜] F) → Prop

/-- Scalar tests use the original continuous linear dual; the conclusion has
norm limit T x, not merely an unspecified convergent image sequence. -/
def IsCompletelyContinuousValue : IsCompletelyContinuousType :=
  fun {𝕜} _ {E} {_} _ _ _ _ T =>
    ∀ (s : ℕ → E) (x : E),
      (∀ f : E →L[𝕜] 𝕜, Tendsto (fun n => f (s n)) atTop (𝓝 (f x))) →
      Tendsto (fun n => T (s n)) atTop (𝓝 (T x))

def CompactIffNative : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  ∀ (T : E →ₗ[𝕜] F), IsCompactLinearMapValue T ↔ IsCompactOperator T

def CompactIffBoundedImages : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  ∀ (T : E →ₗ[𝕜] F), IsCompactLinearMapValue T ↔
    ∀ S : Set E, Bornology.IsBounded S → IsCompact (closure (T '' S))

/-- Native WeakSpace uses the same scalar-linear evaluation pairing. -/
def WeaklyCompactIffWeakSpace : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  ∀ (T : E →L[𝕜] F), IsWeaklyCompactOperatorValue T ↔
    IsCompact (closure ((fun x : E => toWeakSpace 𝕜 F (T x)) ''
      Metric.closedBall (0 : E) 1))

def WeakConvergenceTests : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
  ∀ (s : ℕ → E) (x : E),
    Tendsto s atTop (@nhds E (P1.C12DualPairSpec.DualPairTopologyValue
      𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) x) ↔
    ∀ f : E →L[𝕜] 𝕜, Tendsto (fun n => f (s n)) atTop (𝓝 (f x))

def CompletelyContinuousIffWeakConvergence : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  ∀ (T : E →L[𝕜] F), IsCompletelyContinuousValue T ↔
    ∀ (s : ℕ → E) (x : E),
      Tendsto s atTop (@nhds E (P1.C12DualPairSpec.DualPairTopologyValue
        𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) x) →
      Tendsto (fun n => T (s n)) atTop (𝓝 (T x))

end
end ExpandedFA.Compactness.DefinitionsSpec
