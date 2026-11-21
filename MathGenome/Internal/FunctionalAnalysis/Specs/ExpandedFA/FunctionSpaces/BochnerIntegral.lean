import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Independent specification of the construction part of paper.tex:17026–17066.
Dominated convergence and Lᵖ completeness are assigned separately. The measure
is arbitrary and neither codomain is assumed separable. Real scalar structures
for the real/complex statements are the canonical restrictions of scalars.
-/

noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology
universe u v w z

namespace ExpandedFA.FunctionSpaces.BochnerIntegralSpec
open BochnerDefinitionsSpec

def BochnerIntegrableIdentification : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f : X → E), BochnerIntegrableValue μ f ↔ Integrable f μ

/-- Finiteness is expressed before taking `toReal`, which would discard ∞. -/
def IntegrabilityCriterion : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f : X → E), StrongMeasurableValue μ f →
      (BochnerIntegrableValue μ f ↔ (∫⁻ x, ‖f x‖ₑ ∂μ) < ∞)

def IntegralType :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E], Measure X → (X → E) → E

/-- The canonical total integral; the theorems describe its integrable domain. -/
def IntegralValue : IntegralType.{u,v} := fun μ f => ∫ x, f x ∂μ

def IntegralL1Type :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X), Lp E 1 μ →L[ℝ] E

def IntegralL1Value : IntegralL1Type.{u,v} := fun _ => L1.integralCLM

/-- Function-level integration is the continuous map on the a.e. L¹ quotient. -/
def IntegralOnL1 : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (f : X → E)
    (hf : Integrable f μ), IntegralValue μ f = IntegralL1Value μ (hf.toL1 f)

def IntegralSimple : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (s : SimpleFunc X E),
    IntegrableSimpleValue μ s → IntegralValue μ s = SimpleIntegralValue μ s

/-- Uniqueness holds even among all continuous maps, without assuming linearity.
`Lp.simpleFunc` is the subspace of integrable simple functions modulo a.e. equality. -/
def IntegralExtension : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X),
    Continuous (IntegralL1Value (E := E) μ) ∧
    (∀ s : Lp.simpleFunc E 1 μ,
      IntegralL1Value μ (s : Lp E 1 μ) =
        SimpleIntegralValue μ (Lp.simpleFunc.toSimpleFunc s)) ∧
    (∀ J : Lp E 1 μ → E, Continuous J →
      (∀ s : Lp.simpleFunc E 1 μ,
        J (s : Lp E 1 μ) = SimpleIntegralValue μ (Lp.simpleFunc.toSimpleFunc s)) →
      J = IntegralL1Value μ)

/-- Every choice of integrable simple L¹ approximants gives the same integral. -/
def IntegralApproximation : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (f : X → E)
    (s : ℕ → SimpleFunc X E), (∀ n, IntegrableSimpleValue μ (s n)) →
    Tendsto (fun n => eLpNorm (f - ⇑(s n)) 1 μ) atTop (𝓝 0) →
      Tendsto (fun n => SimpleIntegralValue μ (s n)) atTop (𝓝 (IntegralValue μ f))

def IntegralNormBound : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (f : X → E),
    BochnerIntegrableValue μ f → ‖IntegralValue μ f‖ ≤ ∫ x, ‖f x‖ ∂μ

def IntegralL1NormBound : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X),
    ‖IntegralL1Value (E := E) μ‖ ≤ 1

def IntegralAdd : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (f g : X → E),
    BochnerIntegrableValue μ f → BochnerIntegrableValue μ g →
      BochnerIntegrableValue μ (f + g) ∧
        IntegralValue μ (f + g) = IntegralValue μ f + IntegralValue μ g

def IntegralSmul : Prop :=
  ∀ {𝕜 : Type w} [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (μ : Measure X) (c : 𝕜) (f : X → E),
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    BochnerIntegrableValue μ f → BochnerIntegrableValue μ (c • f) ∧
      IntegralValue μ (c • f) = c • IntegralValue μ f

def IntegralContinuousLinearMap : Prop :=
  ∀ {𝕜 : Type w} [RCLike 𝕜] {X : Type u} {E : Type v} {F : Type z}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (μ : Measure X) (T : E →L[𝕜] F) (f : X → E),
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    letI : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F
    BochnerIntegrableValue μ f → BochnerIntegrableValue μ (fun x => T (f x)) ∧
      T (IntegralValue μ f) = IntegralValue μ (fun x => T (f x))

end ExpandedFA.FunctionSpaces.BochnerIntegralSpec
