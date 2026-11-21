import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.PontryaginDual

/-!
Independent specification for paper.tex:10282–10313, the group-algebra part
of `fa2:p2:wiener`. Multiplicative notation is used for the source's additive
group. Haar measure means a regular Borel Haar measure; Mathlib's bare
`IsHaarMeasure` does not include regularity on arbitrary groups. There is no
σ-compactness, separability, σ-finiteness or s-finiteness hypothesis.

The multiplication is specified by its Bochner formula in the native L¹ space.
The pointwise integral formula is a separate required identification, so this
choice does not replace convolution by an unspecified product. Characters
are algebraic nonzero complex-linear multiplicative functionals: continuity
is a conclusion, never a hypothesis of `CharacterClassification`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

abbrev L1 (μ : Measure G) := MeasureTheory.Lp ℂ 1 μ

section LeftInvariant
variable (μ : Measure G) [μ.IsMulLeftInvariant]

/-- Left translation: τₓf(t) = f(x⁻¹t), on a.e. classes. -/
def translateValue (x : G) : L1 μ →ₗᵢ[ℂ] L1 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun t => x⁻¹ * t) (measurePreserving_mul_left μ x⁻¹)

abbrev TranslateType := G → (L1 μ →ₗᵢ[ℂ] L1 μ)

/-- Totalized Bochner integral; its integrability is explicitly required below. -/
def convolutionValue (f g : L1 μ) : L1 μ :=
  ∫ x, (f x) • translateValue μ x g ∂μ

abbrev ConvolutionType := L1 μ → L1 μ → L1 μ

end LeftInvariant

/-- The source's Fourier evaluation, using the conjugate of the group character. -/
def fourierValue (μ : Measure G) (γ : G →ₜ* Circle) (f : L1 μ) : ℂ :=
  ∫ x, f x * star (Circle.coeHom (γ x)) ∂μ

abbrev FourierType (μ : Measure G) := (G →ₜ* Circle) → L1 μ → ℂ

abbrev FourierLinearType (μ : Measure G) := (G →ₜ* Circle) → (L1 μ →L[ℂ] ℂ)

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Translation continuity and its precise a.e. representative. -/
def TranslationProperties : Prop :=
  (∀ x : G, ∀ f : L1 μ,
    translateValue μ x f =ᵐ[μ] fun t => f (x⁻¹ * t)) ∧
  (∀ f : L1 μ, translateValue μ 1 f = f) ∧
  (∀ x y : G, ∀ f : L1 μ,
    translateValue μ (x * y) f = translateValue μ x (translateValue μ y f)) ∧
  Continuous (fun xf : G × L1 μ => translateValue μ xf.1 xf.2)

/-- Full commutative complex Banach-algebra laws on the original L¹ space. -/
def ConvolutionAlgebra : Prop :=
  CompleteSpace (L1 μ) ∧
  (∀ f g : L1 μ, Integrable (fun x => f x • translateValue μ x g) μ) ∧
  (∀ f g : L1 μ, ∀ᵐ t ∂μ, Integrable (fun x => f x * g (x⁻¹ * t)) μ) ∧
  (∀ f g : L1 μ,
    convolutionValue μ f g =ᵐ[μ] fun t => ∫ x, f x * g (x⁻¹ * t) ∂μ) ∧
  (∀ f g : L1 μ, ‖convolutionValue μ f g‖ ≤ ‖f‖ * ‖g‖) ∧
  (∀ f g h : L1 μ,
    convolutionValue μ (convolutionValue μ f g) h =
      convolutionValue μ f (convolutionValue μ g h)) ∧
  (∀ f g : L1 μ, convolutionValue μ f g = convolutionValue μ g f) ∧
  (∀ f g h : L1 μ,
    convolutionValue μ (f + g) h = convolutionValue μ f h + convolutionValue μ g h) ∧
  (∀ f g h : L1 μ,
    convolutionValue μ f (g + h) = convolutionValue μ f g + convolutionValue μ f h) ∧
  (∀ f : L1 μ, convolutionValue μ 0 f = 0 ∧ convolutionValue μ f 0 = 0) ∧
  (∀ c : ℂ, ∀ f g : L1 μ,
    convolutionValue μ (c • f) g = c • convolutionValue μ f g ∧
      convolutionValue μ f (c • g) = c • convolutionValue μ f g)

/-- The Bochner-algebra portion, also available separately from the
pointwise formula and commutativity. -/
def ConvolutionBasicProperties : Prop :=
  CompleteSpace (L1 μ) ∧
  (∀ f g : L1 μ, Integrable (fun x => f x • translateValue μ x g) μ) ∧
  (∀ f g : L1 μ, ‖convolutionValue μ f g‖ ≤ ‖f‖ * ‖g‖) ∧
  (∀ f g h : L1 μ,
    convolutionValue μ (convolutionValue μ f g) h =
      convolutionValue μ f (convolutionValue μ g h)) ∧
  (∀ f g h : L1 μ,
    convolutionValue μ (f + g) h = convolutionValue μ f h + convolutionValue μ g h) ∧
  (∀ f g h : L1 μ,
    convolutionValue μ f (g + h) = convolutionValue μ f g + convolutionValue μ f h) ∧
  (∀ f : L1 μ, convolutionValue μ 0 f = 0 ∧ convolutionValue μ f 0 = 0) ∧
  (∀ c : ℂ, ∀ f g : L1 μ,
    convolutionValue μ (c • f) g = c • convolutionValue μ f g ∧
      convolutionValue μ f (c • g) = c • convolutionValue μ f g)

/-- This is algebraic multiplicativity, with no boundedness assumption. -/
def IsCharacter (χ : L1 μ →ₗ[ℂ] ℂ) : Prop :=
  χ ≠ 0 ∧ ∀ f g : L1 μ, χ (convolutionValue μ f g) = χ f * χ g

/-- Both directions, uniqueness of the representing group character, and norm one.
The separate forward clause rules out a vacuous representation theorem. -/
def CharacterClassification : Prop :=
  (∀ γ : G →ₜ* Circle, ∃ χ : L1 μ →L[ℂ] ℂ,
    (∀ f, χ f = fourierValue μ γ f) ∧ IsCharacter μ χ.toLinearMap ∧ ‖χ‖ = 1) ∧
  (∀ χ : L1 μ →ₗ[ℂ] ℂ, IsCharacter μ χ →
    (∃! γ : G →ₜ* Circle, ∀ f, χ f = fourierValue μ γ f) ∧ Continuous χ)

def FourierLinearProperties (F : FourierLinearType μ) : Prop :=
  (∀ γ f, F γ f = fourierValue μ γ f) ∧
  (∀ γ, ‖F γ‖ ≤ 1)

def TranslationTheorem : Prop :=
  ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular], TranslationProperties μ

def ConvolutionBasicTheorem : Prop :=
  ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular], ConvolutionBasicProperties μ

def ConvolutionTheorem : Prop :=
  ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular], ConvolutionAlgebra μ

def CharacterTheorem : Prop :=
  ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular], CharacterClassification μ

def GroupAlgebraTheorem : Prop :=
  ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular], ConvolutionAlgebra μ ∧ CharacterClassification μ

end Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters
