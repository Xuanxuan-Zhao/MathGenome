import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-!
Independent statements for paper.tex:2639–2673 (`D11.08.fubini`).
The factors are arbitrary measurable spaces and the product is the ordinary
product, with no completion. `RCLike` includes both real and complex scalars.
The shared scalar integrability predicate includes actual measurability and
finiteness of the shared nonnegative integral of the modulus. The section
integrals below use the shared scalar integral only with an integrability
proof, and are explicitly zero at every other parameter.
-/

open MeasureTheory
open Specs.D11.Ch08.ProductMeasure (productMeasure_value)
open Specs.D11.Ch06.ScalarIntegral (scalarIntegrable_value scalarIntegral_value)
open Specs.D11.Ch04.AeCommonException (almostEverywhere_value)

universe u v
noncomputable section

namespace Specs.D11.Ch08.Fubini

def sectionIntegralLeft_type :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜],
    Measure Y → (X × Y → 𝕜) → X → 𝕜

def sectionIntegralLeft_value : sectionIntegralLeft_type.{u, v} := by
  classical
  exact fun ν f x => if h : scalarIntegrable_value ν (fun y => f (x, y)) then
    scalarIntegral_value ν (fun y => f (x, y)) h else 0

def sectionIntegralRight_type :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜],
    Measure X → (X × Y → 𝕜) → Y → 𝕜

def sectionIntegralRight_value : sectionIntegralRight_type.{u, v} := by
  classical
  exact fun μ f y => if h : scalarIntegrable_value μ (fun x => f (x, y)) then
    scalarIntegral_value μ (fun x => f (x, y)) h else 0

/-- Fubini with actual section integrability almost everywhere, measurable
zero-extended section integrals, their absolute integrability, and the full
chain of scalar integral equalities. No nonemptiness or positive mass is assumed. -/
def fubini : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ (f : X × Y → 𝕜) (hf : scalarIntegrable_value (productMeasure_value μ ν) f),
      almostEverywhere_value μ (fun x => scalarIntegrable_value ν (fun y => f (x, y))) ∧
      almostEverywhere_value ν (fun y => scalarIntegrable_value μ (fun x => f (x, y))) ∧
      Measurable (sectionIntegralLeft_value ν f) ∧
      Measurable (sectionIntegralRight_value μ f) ∧
      ∃ (hl : scalarIntegrable_value μ (sectionIntegralLeft_value ν f))
        (hr : scalarIntegrable_value ν (sectionIntegralRight_value μ f)),
        scalarIntegral_value (productMeasure_value μ ν) f hf =
          scalarIntegral_value μ (sectionIntegralLeft_value ν f) hl ∧
        scalarIntegral_value μ (sectionIntegralLeft_value ν f) hl =
          scalarIntegral_value ν (sectionIntegralRight_value μ f) hr

end Specs.D11.Ch08.Fubini
