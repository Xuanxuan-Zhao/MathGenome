import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Analysis.Normed.Operator.Basic

/-!
Independent statements for the compact-ideal part of
`fa2:p2:schauder-adjoint`, paper.tex:9458–9474.

The carrier is defined by compact closure of the closed-unit-ball image in
the original normed target, using the shared upstream specification.
All assertions hold over ℝ and ℂ. Linearity and the two composition properties
need no completeness; operator-norm closedness needs only complete target.
Thus all apply to the Banach spaces of the source, including zero spaces.
Neither finite-rank approximation nor any approximation property is assumed.
-/

namespace ExpandedFA.Compactness.CompactIdealSpec

universe u v w x
open Filter
open scoped Topology
open DefinitionsSpec

def CompactZero : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  IsCompactLinearMapValue (0 : E →ₗ[𝕜] F)

def CompactAdd : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  ∀ (S T : E →ₗ[𝕜] F),
    IsCompactLinearMapValue S → IsCompactLinearMapValue T →
    IsCompactLinearMapValue (S + T)

def CompactSMul : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  ∀ (a : 𝕜) (T : E →ₗ[𝕜] F),
    IsCompactLinearMapValue T → IsCompactLinearMapValue (a • T)

def CompactSubspace : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  ∃ M : Submodule 𝕜 (E →L[𝕜] F),
    ∀ T : E →L[𝕜] F, T ∈ M ↔ IsCompactLinearMapValue T.toLinearMap

def CompactPrecomp : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  ∀ {D : Type x} [NormedAddCommGroup D] [NormedSpace 𝕜 D],
    ∀ (T : E →ₗ[𝕜] F) (A : D →L[𝕜] E),
    IsCompactLinearMapValue T → IsCompactLinearMapValue (T.comp A.toLinearMap)

def CompactPostcomp : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  ∀ {G : Type x} [NormedAddCommGroup G] [NormedSpace 𝕜 G],
    ∀ (T : E →ₗ[𝕜] F) (B : F →L[𝕜] G),
    IsCompactLinearMapValue T → IsCompactLinearMapValue (B.toLinearMap.comp T)

def CompactOperatorsClosed : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  ∀ [CompleteSpace F],
    IsClosed {T : E →L[𝕜] F | IsCompactLinearMapValue T.toLinearMap}

def CompactOfOperatorNormTendsto : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  ∀ [CompleteSpace F] (Tn : ℕ → E →L[𝕜] F) (T : E →L[𝕜] F),
    (∀ n, IsCompactLinearMapValue (Tn n).toLinearMap) →
    Tendsto (fun n => ‖Tn n - T‖) atTop (𝓝 0) →
    IsCompactLinearMapValue T.toLinearMap

def CompactClosedSubspace : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
  ∀ [CompleteSpace F],
    ∃ M : Submodule 𝕜 (E →L[𝕜] F), IsClosed (M : Set (E →L[𝕜] F)) ∧
      ∀ T : E →L[𝕜] F, T ∈ M ↔ IsCompactLinearMapValue T.toLinearMap

end ExpandedFA.Compactness.CompactIdealSpec
