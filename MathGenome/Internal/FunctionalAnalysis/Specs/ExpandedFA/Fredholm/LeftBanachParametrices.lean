import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The left-sided half of fa2:p2:one-sided-fredholm.
Complemented always means a bounded linear projection in the given norm topology.
Finite rank and nullity refer to the actual projection range and operator kernel. -/
noncomputable section
namespace ExpandedFA.Fredholm.LeftBanachParametricesSpec
universe u v w
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

def LeftCondition (T : E →L[𝕜] F) : Prop :=
  IsClosed (T.range : Set F) ∧ T.range.ClosedComplemented ∧
    FiniteDimensional 𝕜 T.ker

def CompactLeftInverse (T : E →L[𝕜] F) : Prop :=
  ∃ (S : F →L[𝕜] E) (K : E →L[𝕜] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap ∧
      S.comp T = ContinuousLinearMap.id 𝕜 E + K

def ProjectionLeftInverse (T : E →L[𝕜] F) : Prop :=
  ∃ (U : F →L[𝕜] E) (P : E →L[𝕜] E),
    P.comp P = P ∧ FiniteDimensional 𝕜 P.range ∧
      U.comp T = ContinuousLinearMap.id 𝕜 E - P

def ExactProjectionLeftInverse (T : E →L[𝕜] F) : Prop :=
  ∃ (U : F →L[𝕜] E) (P : E →L[𝕜] E),
    P.comp P = P ∧ FiniteDimensional 𝕜 P.range ∧
      U.comp T = ContinuousLinearMap.id 𝕜 E - P ∧
      Module.finrank 𝕜 P.range = Module.finrank 𝕜 T.ker

def LeftEquivalences : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F),
    (LeftCondition T ↔ CompactLeftInverse T) ∧
      (LeftCondition T ↔ ProjectionLeftInverse T)

def ExactDefect : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F),
    LeftCondition T → ExactProjectionLeftInverse T
end ExpandedFA.Fredholm.LeftBanachParametricesSpec
