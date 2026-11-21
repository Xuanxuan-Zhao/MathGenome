import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.LpDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.Fubini

/-!
Independent statements for paper.tex:3532–3560, Minkowski's integral inequality.
Both measures are sigma-finite, with the ordinary product sigma-algebra.
The scalar right side uses the shared extended power norm and nonnegative
integral; its finiteness is an explicit hypothesis. The section integral is
exactly the upstream integral with an integrability proof, extended by zero
at all other parameters. Its exceptional set is measurable and null in the
original space. No completeness or finiteness of total mass is assumed.

For nonnegative extended-valued functions the power norm formula is used
directly: in particular, the inner integral can be infinite. The nonnegative
conclusion has no finiteness hypothesis on either displayed side.
-/
open Set MeasureTheory
open scoped ENNReal
universe u v
noncomputable section
namespace Specs.D11.Ch10.MinkowskiIntegral
open Specs.D11.Ch05.NonnegativeIntegral (nonnegativeIntegral_value)
open Specs.D11.Ch10.LpDefinition (powerNorm_value rawLp_value)
open Specs.D11.Ch06.ScalarIntegral (scalarIntegrable_value)
open Specs.D11.Ch08.Fubini (sectionIntegralLeft_value)
open Specs.D11.Ch04.AeCommonException (almostEverywhere_value)

def nonnegative_minkowski : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ (p : ℝ), 1 ≤ p → ∀ (F : X × Y → ℝ≥0∞), Measurable F →
      Measurable (fun y => (nonnegativeIntegral_value μ (fun x => F (x,y) ^ p)) ^ (1/p)) ∧
      Measurable (fun x => nonnegativeIntegral_value ν (fun y => F (x,y))) ∧
      (nonnegativeIntegral_value μ
        (fun x => (nonnegativeIntegral_value ν (fun y => F (x,y))) ^ p)) ^ (1/p) ≤
        nonnegativeIntegral_value ν
          (fun y => (nonnegativeIntegral_value μ (fun x => F (x,y) ^ p)) ^ (1/p))

def scalar_minkowski : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ (p : ℝ), 1 ≤ p → ∀ (F : X × Y → 𝕜), Measurable F →
      nonnegativeIntegral_value ν (fun y => powerNorm_value μ p (fun x => F (x,y))) < ∞ →
      Measurable (fun y => powerNorm_value μ p (fun x => F (x,y))) ∧
      almostEverywhere_value μ (fun x => scalarIntegrable_value ν (fun y => F (x,y))) ∧
      MeasurableSet {x | ¬ scalarIntegrable_value ν (fun y => F (x,y))} ∧
      μ {x | ¬ scalarIntegrable_value ν (fun y => F (x,y))} = 0 ∧
      sectionIntegralLeft_value ν F ∈ rawLp_value μ p ∧
      powerNorm_value μ p (sectionIntegralLeft_value ν F) ≤
        nonnegativeIntegral_value ν (fun y => powerNorm_value μ p (fun x => F (x,y)))

end Specs.D11.Ch10.MinkowskiIntegral
