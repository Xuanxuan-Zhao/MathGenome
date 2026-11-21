import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction

/-! Independent statements for paper.tex:3447–3458.

Exponents are extended nonnegative reals: `q = ∞` is included, and
`1 / ∞ = 0` is expressed by `1 / q.toReal = 0`. The carrier and the
representative norm are the shared ordinary measurable a.e. quotient.
The norm structures in the quotient conclusion are supplied as conclusions,
with their representative formulas, as in the upstream quotient construction.
No completeness or sigma-finiteness assumption is imposed on the measure.
The positive-mass norm estimate and the zero-mass quotient are separate.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch10.FiniteMeasureInclusion

open Specs.D11.Ch10.QuotientConstruction

def raw_inclusion : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p q : ℝ≥0∞),
    1 ≤ p → p < q → μ univ < ∞ →
    ∀ f : X → 𝕜, f ∈ rawSpace μ q → f ∈ rawSpace μ p

def raw_norm_estimate : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p q : ℝ≥0∞),
    1 ≤ p → p < q → μ univ < ∞ → μ univ ≠ 0 →
    ∀ f : Raw (𝕜 := 𝕜) μ q,
      sourceNorm μ p f.val ≤
        μ univ ^ (1 / p.toReal - 1 / q.toReal) * sourceNorm μ q f.val

/-- The inclusion on the actual ordinary quotient, together with its quantitative
norm bound. The representative identity specifies which inclusion is intended. -/
def finite_measure_inclusion : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p q : ℝ≥0∞),
    1 ≤ p → p < q → μ univ < ∞ → μ univ ≠ 0 →
    ∃ Gp : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ p),
    letI := Gp
    ∃ Gq : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ q),
    letI := Gq
    (∀ f : Raw (𝕜 := 𝕜) μ p, ‖classOf f‖ = (sourceNorm μ p f.val).toReal) ∧
    (∀ f : Raw (𝕜 := 𝕜) μ q, ‖classOf f‖ = (sourceNorm μ q f.val).toReal) ∧
    ∃ i : QuotientLp (𝕜 := 𝕜) μ q ↪ QuotientLp (𝕜 := 𝕜) μ p,
      (∀ f : Raw (𝕜 := 𝕜) μ q, ∃ h : f.val ∈ rawSpace μ p,
        i (classOf f) = classOf ⟨f.val, h⟩) ∧
      ∀ a, ‖i a‖ ≤ (μ univ).toReal ^ (1 / p.toReal - 1 / q.toReal) * ‖a‖

/-- Every exponent has the zero quotient when the total mass is zero.
This assertion does not evaluate a power of the total mass. -/
def zero_measure_quotient : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X), μ univ = 0 →
    ∀ (p : ℝ≥0∞), 1 ≤ p →
      (∀ a : QuotientLp (𝕜 := 𝕜) μ p, a = classOf (0 : Raw (𝕜 := 𝕜) μ p)) ∧
      (∀ f : Raw (𝕜 := 𝕜) μ p, sourceNorm μ p f.val = 0)

end Specs.D11.Ch10.FiniteMeasureInclusion
