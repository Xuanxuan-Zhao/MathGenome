import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.EberleinSmulian
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14BallCharacterization
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-! James's theorem, paper.tex:3701–3715. A maximum at a member of a
nonempty set states both finiteness and attainment of the supremum. All duals
below use the original norm topology, and compactness and closedness use σ(E,E′).
-/
namespace ExpandedFA.P1.James.Spec
universe u v
noncomputable section

abbrev weakTopology := EberleinSmulian.Spec.weakTopology

/-- Every scalar-linear functional has a finite attained absolute supremum. -/
def AbsoluteAttainment (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E) : Prop :=
  ∀ f : E →L[𝕜] 𝕜, ∃ a ∈ A, ∀ x ∈ A, ‖f x‖ ≤ ‖f a‖

/-- Every real-linear functional has a finite attained (signed) supremum. -/
def RealSupremumAttainment (E : Type v) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : Set E) : Prop :=
  ∀ f : E →L[ℝ] ℝ, ∃ a ∈ A, ∀ x ∈ A, f x ≤ f a

/-- The four assertions, including realification in the complex case. -/
def AttainmentEquivalences : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (A : Set E), A.Nonempty → @IsClosed E (weakTopology 𝕜 E) A →
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    (@IsCompact E (weakTopology 𝕜 E) A ↔ AbsoluteAttainment 𝕜 E A) ∧
    (@IsCompact E (weakTopology 𝕜 E) A ↔ AbsoluteAttainment ℝ E A) ∧
    (@IsCompact E (weakTopology 𝕜 E) A ↔ RealSupremumAttainment E A)

/-- The norm is attained on the norm-closed unit ball, including zero functionals. -/
def ReflexiveIffNormAttainment : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ↔
      ∀ f : E →L[𝕜] 𝕜, ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖

end
end ExpandedFA.P1.James.Spec
