import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.EssentialBounds
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Independent statements for paper.tex:3297–3314. The norm on real or complex
scalars is their absolute value. The definitions work for normed additive
groups too. Finite exponents in the source are real numbers `1 ≤ p`; the
formula is extended to other real exponents only to avoid proof parameters
in the definitions. Every finite-exponent assertion below retains `1 ≤ p`.

Raw spaces require ordinary Borel measurability of the given function.
The infinity norm is exactly the upstream ordinary essential supremum,
not a new definition. No completeness or size assumption on the measure
is made. Native `MemLp` is compared only with measurable representatives;
it is not substituted for their measurability requirement.
-/
open Set MeasureTheory
open scoped ENNReal NNReal
universe u v
noncomputable section
namespace Specs.D11.Ch10.LpDefinition

open Specs.D11.Ch04.EssentialBounds Specs.D11.Ch04.AeCommonException
open Specs.D11.Ch05.NonnegativeIntegral

def powerNorm_type := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E], Measure X → ℝ → (X → E) → ℝ≥0∞
def powerNorm_value : powerNorm_type.{u,v} := fun μ p f =>
  (nonnegativeIntegral_value μ (fun x => ENNReal.ofReal (‖f x‖ ^ p))) ^ (1 / p)

def rawLp_type := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E],
  Measure X → ℝ → Set (X → E)
def rawLp_value : rawLp_type.{u,v} := fun μ p =>
  {f | Measurable f ∧ powerNorm_value μ p f < ∞}

def rawLInfinity_type := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E],
  Measure X → Set (X → E)
def rawLInfinity_value : rawLInfinity_type.{u,v} := fun μ =>
  {f | Measurable f ∧ essentialSupNorm_value μ f < ∞}

def powerNorm_formula : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] (μ : Measure X) (p : ℝ)
  (f : X → E), 1 ≤ p →
  powerNorm_value μ p f = (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p) ∂μ) ^ (1 / p)

def rawLp_iff_finite_integral : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E]
  (μ : Measure X) (p : ℝ) (f : X → E), 1 ≤ p →
  (f ∈ rawLp_value μ p ↔ Measurable f ∧
    nonnegativeIntegral_value μ (fun x => ENNReal.ofReal (‖f x‖ ^ p)) < ∞)

def measurable_strict_level : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  (f : X → E), Measurable f → ∀ M : ℝ, MeasurableSet {x | M < ‖f x‖}

def essentialSupNorm_level_formula : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure X) (f : X → E), Measurable f →
  essentialSupNorm_value μ f = sInf ((fun M : ℝ≥0 => (M : ℝ≥0∞)) ''
    {M : ℝ≥0 | μ {x | (M : ℝ) < ‖f x‖} = 0})

def infinity_norm_attained : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E]
  (μ : Measure X) (f : X → E), f ∈ rawLInfinity_value μ →
  almostEverywhere_value μ (fun x => ‖f x‖ ≤ (essentialSupNorm_value μ f).toReal)

def bounded_measurable_representative : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure X) (f : X → E), f ∈ rawLInfinity_value μ →
  ∃ g : X → E, Measurable g ∧ aeEq_value μ f g ∧
    (∀ x, ‖g x‖ ≤ (essentialSupNorm_value μ f).toReal) ∧
    g ∈ rawLInfinity_value μ ∧ essentialSupNorm_value μ g = essentialSupNorm_value μ f

def powerNorm_zero_measure : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] (p : ℝ) (f : X → E), 1 ≤ p →
  powerNorm_value (0 : Measure X) p f = 0

def rawLp_zero_measure : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E]
  (p : ℝ) (f : X → E), 1 ≤ p →
  (f ∈ rawLp_value (0 : Measure X) p ↔ Measurable f)

def rawLInfinity_zero_measure : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E] (f : X → E),
  f ∈ rawLInfinity_value (0 : Measure X) ↔ Measurable f

/-- For real/complex scalars the Borel and countability instances are automatic. -/
def powerNorm_eq_eLpNorm : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] (μ : Measure X) (p : ℝ) (f : X → E),
  1 ≤ p → Measurable f → powerNorm_value μ p f = eLpNorm f (ENNReal.ofReal p) μ

def essentialSupNorm_eq_eLpNorm : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] (μ : Measure X) (f : X → E),
  Measurable f → essentialSupNorm_value μ f = eLpNorm f ∞ μ

def rawLp_iff_memLp : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] (μ : Measure X) (p : ℝ) (f : X → E), 1 ≤ p →
  (f ∈ rawLp_value μ p ↔ Measurable f ∧ MemLp f (ENNReal.ofReal p) μ)

def rawLInfinity_iff_memLp : Prop := ∀ {X : Type u} {E : Type v}
  [MeasurableSpace X] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] (μ : Measure X) (f : X → E),
  f ∈ rawLInfinity_value μ ↔ Measurable f ∧ MemLp f ∞ μ

end Specs.D11.Ch10.LpDefinition
