import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.EssentialBounds
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Independent interface for paper.tex:2100–2125 and 2395–2403.

The convergence predicates use specified representatives. Their analytic clauses
are defined for normed additive groups; specialization to measurable `ℝ`- or
`ℂ`-valued functions is the source setting. Measurability is a separate premise
when using the raw pointwise, uniform, a.e., and measure predicates. The Lp
membership conditions explicitly retain measurability on the original space.
The norm is absolute value on `ℝ` and modulus on `ℂ`.

There is no mass or completeness hypothesis. Measures and nonnegative integrals
remain `ℝ≥0∞`-valued throughout, with no `toReal` totalization. The a.e. and
essential-bound objects are the canonical upstream ordinary-null objects.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
universe u v
noncomputable section
namespace Specs.D11.Ch07.ConvergenceDefinitions

open Specs.D11.Ch04.AeCommonException
open Specs.D11.Ch04.EssentialBounds
open Specs.D11.Ch05.NonnegativeIntegral

def pointwiseConverges_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E],
    (ℕ → X → E) → (X → E) → Prop

def pointwiseConverges_value : pointwiseConverges_type.{u, v} := fun f g =>
  ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))

def aeConverges_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X],
    Measure X → (ℕ → X → E) → (X → E) → Prop

def aeConverges_value : aeConverges_type.{u, v} := fun μ f g =>
  almostEverywhere_value μ (fun x => Tendsto (fun n => f n x) atTop (𝓝 (g x)))

def uniformConvergesOn_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E],
    (ℕ → X → E) → (X → E) → Set X → Prop

def uniformConvergesOn_value : uniformConvergesOn_type.{u, v} := fun f g A =>
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ A, ‖f n x - g x‖ < ε

def uniformConverges_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E],
    (ℕ → X → E) → (X → E) → Prop

def uniformConverges_value : uniformConverges_type.{u, v} := fun f g =>
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, ‖f n x - g x‖ < ε

def almostUniformConverges_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X],
    Measure X → (ℕ → X → E) → (X → E) → Prop

def almostUniformConverges_value : almostUniformConverges_type.{u, v} := fun μ f g =>
  ∀ δ : ℝ, 0 < δ → ∃ A : Set _, MeasurableSet A ∧ μ A < ENNReal.ofReal δ ∧
    uniformConvergesOn_value f g Aᶜ

def deviationSet_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E],
    (X → E) → (X → E) → ℝ → Set X

def deviationSet_value : deviationSet_type.{u, v} := fun f g ε =>
  {x | ε < ‖f x - g x‖}

def inMeasureConverges_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X],
    Measure X → (ℕ → X → E) → (X → E) → Prop

def inMeasureConverges_value : inMeasureConverges_type.{u, v} := fun μ f g =>
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ (deviationSet_value (f n) g ε)) atTop (𝓝 0)

def cauchyInMeasure_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X],
    Measure X → (ℕ → X → E) → Prop

def cauchyInMeasure_value : cauchyInMeasure_type.{u, v} := fun μ f =>
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
    ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      μ (deviationSet_value (f n) (f m) ε) < ENNReal.ofReal δ

def locallyInMeasureConverges_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X],
    Measure X → (ℕ → X → E) → (X → E) → Prop

def locallyInMeasureConverges_value : locallyInMeasureConverges_type.{u, v} :=
  fun μ f g => ∀ A : Set _, MeasurableSet A → μ A < ∞ → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ (A ∩ deviationSet_value (f n) g ε)) atTop (𝓝 0)

/-- The p-power absolute integral, before taking any pth root. -/
def powerIntegral_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X],
    Measure X → ℝ → (X → E) → ℝ≥0∞

def powerIntegral_value : powerIntegral_type.{u, v} := fun μ p f =>
  nonnegativeIntegral_value μ (fun x => ENNReal.ofReal (‖f x‖ ^ p))

def finitePowerIntegral_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X]
    [MeasurableSpace E], Measure X → ℝ → (X → E) → Prop

def finitePowerIntegral_value : finitePowerIntegral_type.{u, v} := fun μ p f =>
  Measurable f ∧ powerIntegral_value μ p f < ∞

def lpConverges_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X]
    [MeasurableSpace E], Measure X → ℝ → (ℕ → X → E) → (X → E) → Prop

/-- A real exponent is finite; the first clause fixes the source range. -/
def lpConverges_value : lpConverges_type.{u, v} := fun μ p f g =>
  1 ≤ p ∧ finitePowerIntegral_value μ p g ∧
    (∀ n, finitePowerIntegral_value μ p (f n)) ∧
    Tendsto (fun n => powerIntegral_value μ p (fun x => f n x - g x)) atTop (𝓝 0)

def linftyConverges_type :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X]
    [MeasurableSpace E], Measure X → (ℕ → X → E) → (X → E) → Prop

def linftyConverges_value : linftyConverges_type.{u, v} := fun μ f g =>
  (Measurable g ∧ essentiallyBounded_value μ g) ∧
    (∀ n, Measurable (f n) ∧ essentiallyBounded_value μ (f n)) ∧
    Tendsto (fun n => essentialSupNorm_value μ (fun x => f n x - g x)) atTop (𝓝 0)

def global_implies_local : Prop :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → E) (g : X → E),
    inMeasureConverges_value μ f g → locallyInMeasureConverges_value μ f g

/-- In the source scalar setting the evaluated deviation sets are measurable
in the original sigma-algebra, including when the measure is incomplete. -/
def measurable_deviationSet : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f g : X → 𝕜) (ε : ℝ),
    Measurable f → Measurable g → MeasurableSet (deviationSet_value f g ε)

def powerIntegral_eq_lintegral : Prop :=
  ∀ {X : Type u} {E : Type v} [NormedAddCommGroup E] [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (f : X → E),
    powerIntegral_value μ p f = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p) ∂μ

end Specs.D11.Ch07.ConvergenceDefinitions
