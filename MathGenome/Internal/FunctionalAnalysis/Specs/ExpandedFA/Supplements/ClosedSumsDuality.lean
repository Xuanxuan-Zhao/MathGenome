import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.ClosedSumEstimates
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators

/-! The full closed-sums theorem, paper.tex:6272–6292. Perpendiculars are
Banach annihilators in the continuous scalar-linear dual, for either scalar
field. Constants need not be optimal; actual decompositions are required. -/

universe u v
namespace ExpandedFA.Supplements.ClosedSumsDuality.Spec

abbrev annihilator {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M : Submodule 𝕜 E) :=
  ExpandedFA.P1.C04Annihilators.Spec.AnnihilatorValue 𝕜 E (M : Set E)

/-- Uniform Hahn–Banach decompositions on the entire intersection annihilator. -/
def AnnihilatorDecompositionBound {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (G L : Submodule 𝕜 E) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : E →L[𝕜] 𝕜, f ∈ annihilator (G ⊓ L) →
    ∃ a ∈ annihilator G, ∃ b ∈ annihilator L,
      a + b = f ∧ ‖a‖ + ‖b‖ ≤ C * ‖f‖

def PrimalEquivalences : Prop := ClosedSumEstimates.Spec.ClosedSumEquivalences.{u,v}

def DualClosedness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (G L : Submodule 𝕜 E), IsClosed (G : Set E) → IsClosed (L : Set E) →
    (IsClosed (↑(G ⊔ L) : Set E) ↔
      IsClosed (↑(annihilator G ⊔ annihilator L) : Set (E →L[𝕜] 𝕜)))

def ClosedAnnihilatorEquality : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (G L : Submodule 𝕜 E), IsClosed (G : Set E) → IsClosed (L : Set E) →
    IsClosed (↑(G ⊔ L) : Set E) →
      annihilator (G ⊓ L) = annihilator G ⊔ annihilator L

def BoundedAnnihilatorDecompositions : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (G L : Submodule 𝕜 E), IsClosed (G : Set E) → IsClosed (L : Set E) →
    (IsClosed (↑(G ⊔ L) : Set E) ∨
      IsClosed (↑(annihilator G ⊔ annihilator L) : Set (E →L[𝕜] 𝕜))) →
      AnnihilatorDecompositionBound G L

end ExpandedFA.Supplements.ClosedSumsDuality.Spec
