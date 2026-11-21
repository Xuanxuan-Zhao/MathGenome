import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.AeCommonException
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Data.EReal.Inv

/-! Independent interface for paper.tex:1766–1803. Actual scalar measurability
is part of integrability, on the original (possibly incomplete) sigma-algebra.
Scalar integral evaluation requires an integrability proof. No mass assumption
is imposed. The RCLike formulation includes both real and complex scalars. -/
open Set MeasureTheory
open scoped ENNReal NNReal
universe u
noncomputable section
namespace Specs.D11.Ch06.ScalarIntegral

open Specs.D11.Ch05.NonnegativeIntegral
open Specs.D11.Ch04.AeCommonException

def scalarIntegrable_type :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (X → 𝕜) → Prop

def scalarIntegrable_value : scalarIntegrable_type.{u} := fun μ f =>
  Measurable f ∧ nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x‖) < ∞

def scalarIntegral_type :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    scalarIntegrable_value μ f → 𝕜

def scalarIntegral_value : scalarIntegral_type.{u} := fun μ f _ => ∫ x, f x ∂μ

def positivePart_type := ∀ {X : Type u}, (X → ℝ) → X → ℝ

def positivePart_value : positivePart_type.{u} := fun f x => max (f x) 0

def negativePart_type := ∀ {X : Type u}, (X → ℝ) → X → ℝ

def negativePart_value : negativePart_type.{u} := fun f x => max (-f x) 0

def extendedIntegrable_type :=
  ∀ {X : Type u} [MeasurableSpace X], Measure X → (X → EReal) → Prop

def extendedIntegrable_value : extendedIntegrable_type.{u} := fun μ f =>
  Measurable f ∧ nonnegativeIntegral_value μ (fun x => (f x).abs) < ∞

/-- `EReal.toReal` sends each infinity to zero, and fixes every finite value. -/
def finiteVersion_type := ∀ {X : Type u}, (X → EReal) → X → ℝ

def finiteVersion_value : finiteVersion_type.{u} := fun f x => (f x).toReal

def extendedIntegral_type :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → EReal),
    extendedIntegrable_value μ f → ℝ

def extendedIntegral_value : extendedIntegral_type.{u} := fun μ f _ =>
  ∫ x, finiteVersion_value f x ∂μ

def scalarIntegrable_iff : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    scalarIntegrable_value μ f ↔ Measurable f ∧ Integrable f μ

def native_integrable_iff : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    Measurable f → (scalarIntegrable_value μ f ↔ Integrable f μ)

def parts_identities : Prop :=
  ∀ {X : Type u} (f : X → ℝ) (x : X),
    0 ≤ positivePart_value f x ∧ 0 ≤ negativePart_value f x ∧
    |f x| = positivePart_value f x + negativePart_value f x ∧
    f x = positivePart_value f x - negativePart_value f x

def measurable_parts : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (f : X → ℝ), Measurable f →
    Measurable (positivePart_value f) ∧ Measurable (negativePart_value f)

def real_integrable_iff_parts : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ),
    Measurable f → (scalarIntegrable_value μ f ↔
      nonnegativeIntegral_value μ (fun x => ENNReal.ofReal (positivePart_value f x)) < ∞ ∧
      nonnegativeIntegral_value μ (fun x => ENNReal.ofReal (negativePart_value f x)) < ∞)

def real_integral_formula : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : scalarIntegrable_value μ f),
    scalarIntegral_value μ f hf =
      (nonnegativeIntegral_value μ (fun x => ENNReal.ofReal (positivePart_value f x))).toReal -
      (nonnegativeIntegral_value μ (fun x => ENNReal.ofReal (negativePart_value f x))).toReal

def complex_integrable_iff_coordinates : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℂ),
    scalarIntegrable_value μ f ↔
      scalarIntegrable_value μ (fun x => (f x).re) ∧
      scalarIntegrable_value μ (fun x => (f x).im)

def complex_integral_formula : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℂ)
    (hf : scalarIntegrable_value μ f),
    ∃ (hr : scalarIntegrable_value μ (fun x => (f x).re))
      (hi : scalarIntegrable_value μ (fun x => (f x).im)),
    scalarIntegral_value μ f hf =
      ((scalarIntegral_value μ (fun x => (f x).re) hr : ℝ) : ℂ) +
      Complex.I * ((scalarIntegral_value μ (fun x => (f x).im) hi : ℝ) : ℂ)

/-- All nonzero simple levels have finite mass: no infinite scalar product
is hidden by the library's `Measure.real` coercion in the finite sum. -/
def simple_nonzero_levels_finite : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (s : SimpleFunc X 𝕜),
    scalarIntegrable_value μ s → ∀ c : 𝕜, c ≠ 0 → μ (s ⁻¹' {c}) < ∞

def simple_integral_sum : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (s : SimpleFunc X 𝕜)
    (hs : scalarIntegrable_value μ s),
    scalarIntegral_value μ s hs = ∑ c ∈ s.range, μ.real (s ⁻¹' {c}) • c

/-- The exceptional set is measurable and null in the original space. -/
def extended_exceptional_null : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → EReal),
    extendedIntegrable_value μ f →
    MeasurableSet {x | (f x).abs = ∞} ∧ μ {x | (f x).abs = ∞} = 0

def finiteVersion_values : Prop :=
  ∀ {X : Type u} (f : X → EReal) (x : X),
    ((f x).abs = ∞ → finiteVersion_value f x = 0) ∧
    ((f x).abs ≠ ∞ → (finiteVersion_value f x : EReal) = f x)

def finiteVersion_integrable : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → EReal),
    extendedIntegrable_value μ f → scalarIntegrable_value μ (finiteVersion_value f)

def finiteVersion_ae : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → EReal),
    extendedIntegrable_value μ f →
    aeEq_value μ (fun x => (finiteVersion_value f x : EReal)) f

/-- Uniqueness of a finite representative itself needs no measurability
assumption on the second representative. -/
def finiteVersion_unique_ae : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → EReal),
    extendedIntegrable_value μ f → ∀ g : X → ℝ,
    aeEq_value μ (fun x => (g x : EReal)) f →
    aeEq_value μ g (finiteVersion_value f)

def finiteVersion_absolute_integral : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → EReal),
    extendedIntegrable_value μ f →
    nonnegativeIntegral_value μ (fun x => ENNReal.ofReal |finiteVersion_value f x|) =
      nonnegativeIntegral_value μ (fun x => (f x).abs)

/-- Any other real representative of the same extended function agrees a.e.,
is integrable when measurable, and has the same scalar integral. -/
def finiteVersion_unique : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → EReal)
    (hf : extendedIntegrable_value μ f) (g : X → ℝ),
    Measurable g → aeEq_value μ (fun x => (g x : EReal)) f →
    aeEq_value μ g (finiteVersion_value f) ∧
    ∃ hg : scalarIntegrable_value μ g,
      scalarIntegral_value μ g hg = extendedIntegral_value μ f hf

def extended_integral_formula : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → EReal)
    (hf : extendedIntegrable_value μ f),
    ∃ hfin : scalarIntegrable_value μ (finiteVersion_value f),
      extendedIntegral_value μ f hf = scalarIntegral_value μ (finiteVersion_value f) hfin

end Specs.D11.Ch06.ScalarIntegral
