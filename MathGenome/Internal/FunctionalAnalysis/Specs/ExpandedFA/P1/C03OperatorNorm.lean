import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
Independent specification of Definition `fa2:p1:c03:operator-norm`, paper.tex
607–617.
All norms and subspace structures below are the original Mathlib structures.
There is no completeness or nontriviality assumption on any vector space.
-/

namespace ExpandedFA.P1.C03OperatorNorm.Spec

universe u v w

/-- The manuscript's L(E,F) is literally the native continuous linear map type. -/
def OperatorType :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], Type (max v w)

def OperatorValue : OperatorType :=
  fun 𝕜 E F _ _ _ _ _ => E →L[𝕜] F

def EndOperatorType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], Type v

def EndOperatorValue : EndOperatorType.{u, v} :=
  fun 𝕜 E _ _ _ => E →L[𝕜] E

/-- The bridge checks precisely bounded linear maps, with no new topology. -/
def BoundedMapIdentification : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (f : E →ₗ[𝕜] F),
    (∃ T : E →L[𝕜] F, T.toLinearMap = f) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖

/-- The unit ball and the scalar values whose supremum is taken are nonempty. -/
def UnitBallNonempty : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    ({x : E | ‖x‖ ≤ 1}).Nonempty ∧
      ((fun x => ‖T x‖) '' {x : E | ‖x‖ ≤ 1}).Nonempty

def NormSupremum : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    ‖T‖ = sSup ((fun x => ‖T x‖) '' {x : E | ‖x‖ ≤ 1})

def NormInfimum : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    ‖T‖ = sInf {C : ℝ | 0 ≤ C ∧ ∀ x, ‖T x‖ ≤ C * ‖x‖}

/-- This also rules out a vacuous or unbounded infimum representation. -/
def BoundsNonempty : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    ({C : ℝ | 0 ≤ C ∧ ∀ x, ‖T x‖ ≤ C * ‖x‖}).Nonempty ∧
      BddBelow {C : ℝ | 0 ≤ C ∧ ∀ x, ‖T x‖ ≤ C * ‖x‖} ∧
      BddAbove ((fun x => ‖T x‖) '' {x : E | ‖x‖ ≤ 1})

def ZeroDomain : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [Subsingleton E] (T : E →L[𝕜] F),
    ((fun x => ‖T x‖) '' {x : E | ‖x‖ ≤ 1}) = {0} ∧ ‖T‖ = 0

end ExpandedFA.P1.C03OperatorNorm.Spec
