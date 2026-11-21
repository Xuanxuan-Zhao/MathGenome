import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.LpDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.Basic.Real.ConjExponents

/-!
Hölder, paper.tex:3316–3336. Finite conjugate real exponents cover the
interior case; the two endpoint statements cover (1,∞) and (∞,1).
`Real.holderConjugate_iff` identifies the finite hypothesis with
`1 < p` and `p⁻¹ + q⁻¹ = 1`; `HolderConjugate.conjugate_eq` gives
`q = p / (p - 1)` for the equality statement.
All functions are actual measurable representatives in the upstream raw
spaces. The absolute integral and both norms are the shared canonical
objects, with values in ENNReal. No hypothesis on the measure is added.
The equality criterion concerns the absolute product integral, and its
constant is a strictly positive real number. A.e. has the shared ordinary
measurable-null-envelope meaning, including on incomplete spaces.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch10.Holder
open LpDefinition
open Specs.D11.Ch04.EssentialBounds Specs.D11.Ch04.AeCommonException
open Specs.D11.Ch05.NonnegativeIntegral Specs.D11.Ch06.ScalarIntegral

def holder_finite : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p q : ℝ) (f g : X → 𝕜),
    p.HolderConjugate q → f ∈ rawLp_value μ p → g ∈ rawLp_value μ q →
    scalarIntegrable_value μ (fun x => f x * g x) ∧
    nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x * g x‖) ≤
      powerNorm_value μ p f * powerNorm_value μ q g

def holder_one_top : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f g : X → 𝕜),
    f ∈ rawLp_value μ 1 → g ∈ rawLInfinity_value μ →
    scalarIntegrable_value μ (fun x => f x * g x) ∧
    nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x * g x‖) ≤
      powerNorm_value μ 1 f * essentialSupNorm_value μ g

def holder_top_one : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f g : X → 𝕜),
    f ∈ rawLInfinity_value μ → g ∈ rawLp_value μ 1 →
    scalarIntegrable_value μ (fun x => f x * g x) ∧
    nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x * g x‖) ≤
      essentialSupNorm_value μ f * powerNorm_value μ 1 g

def equality_iff : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p q : ℝ) (f g : X → 𝕜),
    p.HolderConjugate q → f ∈ rawLp_value μ p → g ∈ rawLp_value μ q →
    powerNorm_value μ p f ≠ 0 → powerNorm_value μ q g ≠ 0 →
    (nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x * g x‖) =
        powerNorm_value μ p f * powerNorm_value μ q g ↔
      ∃ c : ℝ, 0 < c ∧ almostEverywhere_value μ
        (fun x => ‖f x‖ ^ p = c * ‖g x‖ ^ q))

def zero_finite : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p q : ℝ) (f g : X → 𝕜),
    p.HolderConjugate q → f ∈ rawLp_value μ p → g ∈ rawLp_value μ q →
    (powerNorm_value μ p f = 0 ∨ powerNorm_value μ q g = 0) →
    nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x * g x‖) =
      powerNorm_value μ p f * powerNorm_value μ q g

def zero_one_top : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f g : X → 𝕜),
    f ∈ rawLp_value μ 1 → g ∈ rawLInfinity_value μ →
    (powerNorm_value μ 1 f = 0 ∨ essentialSupNorm_value μ g = 0) →
    nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x * g x‖) =
      powerNorm_value μ 1 f * essentialSupNorm_value μ g

def zero_top_one : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f g : X → 𝕜),
    f ∈ rawLInfinity_value μ → g ∈ rawLp_value μ 1 →
    (essentialSupNorm_value μ f = 0 ∨ powerNorm_value μ 1 g = 0) →
    nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x * g x‖) =
      essentialSupNorm_value μ f * powerNorm_value μ 1 g

end Specs.D11.Ch10.Holder
