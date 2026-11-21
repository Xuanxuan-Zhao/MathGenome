import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces

/-! Independent statements for `fa2:p2:dunford-pettis`, paper.tex:9633–9669.
The chapter's spaces are Banach, over ℝ or ℂ. The dual is scalar-linear.
In particular the second null sequence below is weakly null in X′, with
all of X″ as tests, rather than only evaluations at vectors of X.

The target universe includes the scalar universe so that it contains c₀;
the extra universe parameter is arbitrary. The operator implication is also
stated for an arbitrary target universe directly. No separability, nonzero,
or nonempty hypotheses are imposed.
-/
namespace ExpandedFA.Compactness.DunfordPettisCriterion.Spec
universe u v w
open Filter
open scoped Topology
noncomputable section

/-- Every weakly compact operator into every Banach target is completely continuous. -/
def DunfordPettisPropertyValue (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∀ (Y : Type (max u w)) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [CompleteSpace Y] (T : X →L[𝕜] Y),
    DefinitionsSpec.IsWeaklyCompactOperatorValue T →
      DefinitionsSpec.IsCompletelyContinuousValue T

def DunfordPettisPropertyType :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X], Prop

/-- The same operator assertion for the literal canonical c₀ ⊆ ℓ∞. -/
def C0TestingPropertyValue (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∀ T : X →L[𝕜] P1.C01SequenceSpaces.SequenceC0 𝕜,
    DefinitionsSpec.IsWeaklyCompactOperatorValue T →
      DefinitionsSpec.IsCompletelyContinuousValue T

def C0TestingPropertyType := DunfordPettisPropertyType.{u,v}

/-- The diagonal pairing of two weakly null sequences tends to zero. -/
def WeakNullTestingPropertyValue (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  ∀ (x : ℕ → X) (f : ℕ → (X →L[𝕜] 𝕜)),
    (∀ g : X →L[𝕜] 𝕜, Tendsto (fun n => g (x n)) atTop (𝓝 0)) →
    (∀ ξ : (X →L[𝕜] 𝕜) →L[𝕜] 𝕜, Tendsto (fun n => ξ (f n)) atTop (𝓝 0)) →
    Tendsto (fun n => f n (x n)) atTop (𝓝 0)

def WeakNullTestingPropertyType := DunfordPettisPropertyType.{u,v}

def Equivalences : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    (DunfordPettisPropertyValue.{u,v,w} 𝕜 X ↔ C0TestingPropertyValue 𝕜 X) ∧
      (C0TestingPropertyValue 𝕜 X ↔ WeakNullTestingPropertyValue 𝕜 X)

/-- The test implies complete continuity with no restriction on target universe. -/
def TestingImpliesOperatorProperty : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y],
    WeakNullTestingPropertyValue 𝕜 X → ∀ T : X →L[𝕜] Y,
      DefinitionsSpec.IsWeaklyCompactOperatorValue T →
        DefinitionsSpec.IsCompletelyContinuousValue T

end
end ExpandedFA.Compactness.DunfordPettisCriterion.Spec
