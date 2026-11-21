import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerDefinitions
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Independent statements of `fa2:p1:c14:reflexive-examples`, paper.tex:2960–2965.
Reflexivity means surjectivity of scalar-linear canonical evaluation. Hilbert
spaces have their given complete norm. The scalar Lᵖ quotient and norm are the
shared canonical ones, with a finite real exponent p > 1 and an arbitrary
positive measure. No finiteness, sigma-finiteness, separability, nonzero-measure,
or nonempty-domain assumption is imposed. The negative examples are the three
canonical spaces of scalar sequences, rather than arbitrary endpoint Lᵖ spaces.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.P1.C14ReflexiveExamples.Spec
universe u v

local instance (𝕜 : Type u) [RCLike 𝕜] :
    NormedAddCommGroup (C01SequenceSpaces.SequenceC0 𝕜) := inferInstance
local instance (𝕜 : Type u) [RCLike 𝕜] :
    NormedSpace 𝕜 (C01SequenceSpaces.SequenceC0 𝕜) := inferInstance

def HilbertReflexive : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 H

def MeasureLpReflexive : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (X : Type v) [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (hp : 1 < p),
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜
      (FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue 𝕜 (ENNReal.ofReal p) μ)

def C0Nonreflexive : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (C01SequenceSpaces.SequenceC0 𝕜)

def L1Nonreflexive : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (C01SequenceSpaces.SequenceLp 𝕜 1)

def LInfinityNonreflexive : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (C01SequenceSpaces.SequenceLInfinity 𝕜)

end ExpandedFA.P1.C14ReflexiveExamples.Spec
