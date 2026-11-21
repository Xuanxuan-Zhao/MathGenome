import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerDefinitions
import Mathlib.Analysis.RCLike.Basic

/-!
Independent statements for the completeness and scalar-identification clauses
of paper.tex:17036–17040 (`fa2:p4:lp-completeness`). The measure is arbitrary.
In particular no sigma-finiteness, completeness of the measure, or separability
of the Banach codomain is assumed. `p : ℝ≥0∞` includes the endpoint `∞`.

Completeness is stated for complete normed additive groups, which includes
all real and complex Banach spaces with their inherited `Lp` scalar structure.
The scalar statements use a Borel measurable structure on an `RCLike` field;
they apply to both `ℝ` and `ℂ` with their usual measurable structures.
-/

noncomputable section
open Filter MeasureTheory
open scoped ENNReal
universe u v

namespace ExpandedFA.FunctionSpaces.BochnerLpCompletenessSpec

/-- Completeness of the canonical strongly measurable a.e. quotient with
its usual norm, including the essential-supremum norm for `p = ∞`. -/
def LpComplete : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [CompleteSpace E] (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X),
    CompleteSpace (BochnerDefinitionsSpec.BochnerLpValue E p μ)

/-- The paper's a.e. simple approximation definition is exactly the existence
of an ordinary measurable scalar representative, on any positive measure space. -/
def ScalarStrongMeasurableRepresentative : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    BochnerDefinitionsSpec.StrongMeasurableValue μ f ↔
      ∃ g : X → 𝕜, Measurable g ∧ f =ᵐ[μ] g

/-- The admissible scalar functions are precisely those a.e. equal to an
ordinary measurable function of finite extended p-norm. -/
def ScalarLpMembership : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : Measure X) (f : X → 𝕜),
    MemLp f p μ ↔ ∃ g : X → 𝕜,
      Measurable g ∧ eLpNorm g p μ < ∞ ∧ f =ᵐ[μ] g

/-- Every quotient element has an ordinary measurable representative of
finite p-norm with exactly the same norm. Together with the upstream
`LpEquality`, this identifies the quotient with the usual scalar a.e. quotient. -/
def ScalarLpRepresentative : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : Measure X) (f : BochnerDefinitionsSpec.BochnerLpValue 𝕜 p μ),
    ∃ g : X → 𝕜, Measurable g ∧ eLpNorm g p μ < ∞ ∧
      f =ᵐ[μ] g ∧ ‖f‖ = (eLpNorm g p μ).toReal

end ExpandedFA.FunctionSpaces.BochnerLpCompletenessSpec
