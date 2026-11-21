import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.LpDefinition
import Mathlib.Analysis.RCLike.Basic

/-!
Independent statements for paper.tex:3344–3363, Minkowski and the norm
identities. Finite real exponents and the infinity endpoint together cover
the entire source range. The shared raw spaces retain actual measurability;
the shared a.e. predicate uses a measurable null envelope in the original
sigma-algebra. No completeness or finiteness hypothesis is imposed on μ.
`RCLike` includes both scalar fields, and their norm is absolute value.
The norms take values in ENNReal as in the upstream definitions; on these
raw spaces they are finite. Scalar multiplication is written pointwise.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch10.Minkowski

open LpDefinition
open Specs.D11.Ch04.EssentialBounds Specs.D11.Ch04.AeCommonException

def minkowski_finite : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p : ℝ) (f g : X → 𝕜), 1 ≤ p →
    f ∈ rawLp_value μ p → g ∈ rawLp_value μ p →
    (fun x => f x + g x) ∈ rawLp_value μ p ∧
      powerNorm_value μ p (fun x => f x + g x) ≤
        powerNorm_value μ p f + powerNorm_value μ p g

def minkowski_top : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f g : X → 𝕜),
    f ∈ rawLInfinity_value μ → g ∈ rawLInfinity_value μ →
    (fun x => f x + g x) ∈ rawLInfinity_value μ ∧
      essentialSupNorm_value μ (fun x => f x + g x) ≤
        essentialSupNorm_value μ f + essentialSupNorm_value μ g

def homogeneity_finite : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p : ℝ) (f : X → 𝕜) (c : 𝕜), 1 ≤ p →
    f ∈ rawLp_value μ p →
    (fun x => c * f x) ∈ rawLp_value μ p ∧
      powerNorm_value μ p (fun x => c * f x) =
        ENNReal.ofReal ‖c‖ * powerNorm_value μ p f

def homogeneity_top : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : X → 𝕜) (c : 𝕜),
    f ∈ rawLInfinity_value μ →
    (fun x => c * f x) ∈ rawLInfinity_value μ ∧
      essentialSupNorm_value μ (fun x => c * f x) =
        ENNReal.ofReal ‖c‖ * essentialSupNorm_value μ f

def zero_iff_finite : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p : ℝ) (f : X → 𝕜), 1 ≤ p →
    f ∈ rawLp_value μ p →
    (powerNorm_value μ p f = 0 ↔ aeEq_value μ f (fun _ => 0))

def zero_iff_top : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : X → 𝕜), f ∈ rawLInfinity_value μ →
    (essentialSupNorm_value μ f = 0 ↔ aeEq_value μ f (fun _ => 0))

end Specs.D11.Ch10.Minkowski
