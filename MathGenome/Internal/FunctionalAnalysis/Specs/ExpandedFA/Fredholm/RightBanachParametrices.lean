import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The right-sided half of fa2:p2:one-sided-fredholm.
Complemented always means a bounded linear projection in the given norm topology.
Finite rank and codimension refer to the actual operator range and its quotient. -/
noncomputable section
namespace ExpandedFA.Fredholm.RightBanachParametricesSpec
universe u v w
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

def RightCondition (T : E →L[𝕜] F) : Prop :=
  IsClosed (T.range : Set F) ∧ FiniteDimensional 𝕜 (F ⧸ T.range) ∧
    T.ker.ClosedComplemented

def CompactRightInverse (T : E →L[𝕜] F) : Prop :=
  ∃ (S : F →L[𝕜] E) (K : F →L[𝕜] F),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap ∧
      T.comp S = ContinuousLinearMap.id 𝕜 F + K

def ProjectionRightInverse (T : E →L[𝕜] F) : Prop :=
  ∃ (U : F →L[𝕜] E) (P : F →L[𝕜] F),
    P.comp P = P ∧ FiniteDimensional 𝕜 P.range ∧
      T.comp U = ContinuousLinearMap.id 𝕜 F - P

def ExactProjectionRightInverse (T : E →L[𝕜] F) : Prop :=
  ∃ (U : F →L[𝕜] E) (P : F →L[𝕜] F),
    P.comp P = P ∧ FiniteDimensional 𝕜 P.range ∧
      T.comp U = ContinuousLinearMap.id 𝕜 F - P ∧
      Module.finrank 𝕜 P.range = Module.finrank 𝕜 (F ⧸ T.range)

def RightEquivalences : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F),
    (RightCondition T ↔ CompactRightInverse T) ∧
      (RightCondition T ↔ ProjectionRightInverse T)

def ExactDefect : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F),
    RightCondition T → ExactProjectionRightInverse T
end ExpandedFA.Fredholm.RightBanachParametricesSpec
