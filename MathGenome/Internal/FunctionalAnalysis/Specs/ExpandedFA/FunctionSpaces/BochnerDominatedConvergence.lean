import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerIntegral

/-!
Independent specification of dominated convergence in paper.tex:17026–17068.
The measure is arbitrary. Strong measurability has the paper's a.e. simple
approximation meaning, and integrability has its L¹ simple approximation meaning.
There is no separability, sigma-finiteness, or completeness-of-measure hypothesis.
Every complex Banach space also has the real normed-space structure used here.
-/

noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology
universe u v

namespace ExpandedFA.FunctionSpaces.BochnerDominatedConvergenceSpec
open BochnerDefinitionsSpec BochnerIntegralSpec

/-- A.e. norm convergence under one integrable bound implies strong
measurability and integrability of the limit, L¹ convergence, and norm-topology
convergence of the integrals. Integrability of the approximants and of their
norm errors is included explicitly, so all integrals are on their natural domains.
The domination may hold a.e. separately for each index. -/
def DominatedConvergence : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) (F : ℕ → X → E) (f : X → E) (g : X → ℝ),
    (∀ n, StrongMeasurableValue μ (F n)) →
    BochnerIntegrableValue μ g →
    (∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ g x) →
    (∀ᵐ x ∂μ, Tendsto (fun n => ‖F n x - f x‖) atTop (𝓝 0)) →
      StrongMeasurableValue μ f ∧
      (∀ n, BochnerIntegrableValue μ (F n)) ∧
      BochnerIntegrableValue μ f ∧
      (∀ n, BochnerIntegrableValue μ (fun x => ‖F n x - f x‖)) ∧
      Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => IntegralValue μ (F n)) atTop (𝓝 (IntegralValue μ f))

end ExpandedFA.FunctionSpaces.BochnerDominatedConvergenceSpec
