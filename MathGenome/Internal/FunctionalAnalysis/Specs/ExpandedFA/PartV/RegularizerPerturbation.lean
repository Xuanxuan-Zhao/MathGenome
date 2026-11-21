import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.LeftBanachParametrices
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RightBanachParametrices

/-! Independent statements of paper.tex,
`fa2:p5:one-sided-regularizer-perturbation` (22676–22701).
Two inverse identities specify the bounded inverse without choosing an inverse
on singular maps. Compactness is in the original norm topology. Both scalar
fields and zero spaces are retained; in particular R need not be nonzero.
The counterexample works on every infinite-dimensional Banach space, hence on
the infinite-dimensional Hilbert spaces of the manuscript. -/

namespace ExpandedFA.PartV.RegularizerPerturbation.Spec
universe u v w
open ExpandedFA.Fredholm
open ExpandedFA.Compactness.DefinitionsSpec

/-- The inverse of I+RC gives the stated left regularizer and exact defect. -/
def LeftPerturbation : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y]
    (K : X →L[𝕜] Y) (R : Y →L[𝕜] X) (C : X →L[𝕜] Y),
    ‖R‖ * ‖C‖ < 1 →
    IsCompactLinearMapValue (R.comp K - ContinuousLinearMap.id 𝕜 X).toLinearMap →
    ∃ U : X →L[𝕜] X,
      (ContinuousLinearMap.id 𝕜 X + R.comp C).comp U = ContinuousLinearMap.id 𝕜 X ∧
      U.comp (ContinuousLinearMap.id 𝕜 X + R.comp C) = ContinuousLinearMap.id 𝕜 X ∧
      (U.comp R).comp (K + C) = ContinuousLinearMap.id 𝕜 X -
        U.comp (ContinuousLinearMap.id 𝕜 X - R.comp K) ∧
      IsCompactLinearMapValue
        ((U.comp R).comp (K + C) - ContinuousLinearMap.id 𝕜 X).toLinearMap ∧
      LeftBanachParametricesSpec.CompactLeftInverse (K + C)

/-- The inverse of I+CR gives the stated right regularizer and exact defect. -/
def RightPerturbation : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y]
    (K : X →L[𝕜] Y) (R : Y →L[𝕜] X) (C : X →L[𝕜] Y),
    ‖R‖ * ‖C‖ < 1 →
    IsCompactLinearMapValue (K.comp R - ContinuousLinearMap.id 𝕜 Y).toLinearMap →
    ∃ V : Y →L[𝕜] Y,
      (ContinuousLinearMap.id 𝕜 Y + C.comp R).comp V = ContinuousLinearMap.id 𝕜 Y ∧
      V.comp (ContinuousLinearMap.id 𝕜 Y + C.comp R) = ContinuousLinearMap.id 𝕜 Y ∧
      (K + C).comp (R.comp V) = ContinuousLinearMap.id 𝕜 Y -
        (ContinuousLinearMap.id 𝕜 Y - K.comp R).comp V ∧
      IsCompactLinearMapValue
        ((K + C).comp (R.comp V) - ContinuousLinearMap.id 𝕜 Y).toLinearMap ∧
      RightBanachParametricesSpec.CompactRightInverse (K + C)

/-- K=I/2, R=2I, C=-I/2 satisfy the printed inequality and have zero
original defects, while K+C has neither one-sided regularizer. -/
def PrintedThresholdCounterexample : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H] [CompleteSpace H],
    ¬ FiniteDimensional 𝕜 H →
    let I := ContinuousLinearMap.id 𝕜 H
    let K := (1 / 2 : 𝕜) • I
    let R := (2 : 𝕜) • I
    let C := -(1 / 2 : 𝕜) • I
    ‖C‖ < ‖R‖ ∧ R.comp K = I ∧ K.comp R = I ∧
      IsCompactLinearMapValue (R.comp K - I).toLinearMap ∧
      IsCompactLinearMapValue (K.comp R - I).toLinearMap ∧
      K + C = 0 ∧ ¬ IsCompactLinearMapValue I.toLinearMap ∧
      ¬ LeftBanachParametricesSpec.CompactLeftInverse (K + C) ∧
      ¬ RightBanachParametricesSpec.CompactRightInverse (K + C)

end ExpandedFA.PartV.RegularizerPerturbation.Spec
