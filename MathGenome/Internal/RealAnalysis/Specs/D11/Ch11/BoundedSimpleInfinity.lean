import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.SimpleApproximation

/-! Independent statements for paper.tex:3624–3635. The measure is arbitrary.
`SimpleFunc` has finite range and measurable fibers; no finiteness of the measure
of its support is imposed. The quotient statement measures the error of every
ordinary measurable representative, using the already specified source norm.
The native Lp statement uses the upstream identification with the ordinary
quotient, not a local-null quotient. `RCLike` includes both real and complex
scalars. Empty spaces and zero measures are included. -/
open Set MeasureTheory
open scoped ENNReal
universe u
namespace Specs.D11.Ch11.BoundedSimpleInfinity

open Specs.D11.Ch10.QuotientConstruction
open Specs.D11.Ch10.LpDefinition
open Specs.D11.Ch04.EssentialBounds

def raw_approximation : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    f ∈ rawLInfinity_value μ → ∀ ε : ℝ, 0 < ε →
    ∃ s : SimpleFunc X 𝕜,
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖s x‖ ≤ B) ∧
      (s : X → 𝕜) ∈ rawLInfinity_value μ ∧
      essentialSupNorm_value μ (fun x => f x - s x) < ENNReal.ofReal ε

/-- An approximating simple class is close to the given ordinary quotient
class independently of the choice of representative. `sourceNorm μ ∞` is
literally the earlier essential supremum, and is the quotient norm by the
upstream norm formula. -/
def quotient_approximation : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (q : QuotientLp (𝕜 := 𝕜) μ ∞) (ε : ℝ), 0 < ε →
    ∃ s : SimpleFunc X 𝕜,
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖s x‖ ≤ B) ∧
      (s : X → 𝕜) ∈ rawSpace μ ∞ ∧
      ∀ f : Raw (𝕜 := 𝕜) μ ∞, classOf f = q →
        sourceNorm μ ∞ (fun x => f.val x - s x) < ENNReal.ofReal ε

/-- The equivalent norm formulation for the native ordinary a.e. quotient. -/
def native_approximation : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (f : Lp 𝕜 ∞ μ) (ε : ℝ), 0 < ε →
    ∃ (s : SimpleFunc X 𝕜) (hs : MemLp (s : X → 𝕜) ∞ μ),
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖s x‖ ≤ B) ∧
      ‖f - hs.toLp s‖ < ε

end Specs.D11.Ch11.BoundedSimpleInfinity
