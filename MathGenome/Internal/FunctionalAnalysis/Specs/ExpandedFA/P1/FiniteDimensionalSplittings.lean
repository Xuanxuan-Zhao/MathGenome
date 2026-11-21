import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Independent statements of the finite-dimensional one-sided inverse consequences
following Theorem `fa2:p1:c08:splitting`, paper.tex lines 1722–1727.
Both spaces carry their given Banach norms over the same real or complex field.
Continuous linear maps express bounded linear maps. No positive-dimension or
nontriviality hypothesis is imposed; the inverses act on the entire spaces.
-/

namespace ExpandedFA.P1.FiniteDimensionalSplittings.Spec

universe u v w

/-- A bounded surjection onto a finite-dimensional space has a bounded linear
right inverse. -/
def FiniteDimensionalRightInverse : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    [FiniteDimensional 𝕜 F] (T : E →L[𝕜] F),
    Function.Surjective T →
      ∃ S : F →L[𝕜] E, T.comp S = ContinuousLinearMap.id 𝕜 F

/-- A bounded injection from a finite-dimensional space has a bounded linear
left inverse defined on the entire ambient target. -/
def FiniteDimensionalLeftInverse : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    [FiniteDimensional 𝕜 E] (T : E →L[𝕜] F),
    Function.Injective T →
      ∃ S : F →L[𝕜] E, S.comp T = ContinuousLinearMap.id 𝕜 E

end ExpandedFA.P1.FiniteDimensionalSplittings.Spec
