import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open MeasureTheory
open scoped Topology FourierTransform

namespace ExpandedFA.PartIV.WienerLocalIdeal
open ExpandedFA.Fourier

abbrev L1 (d : ℕ) := Lp ℂ 1 (volume : Measure (Euclidean d))

/-- Ordinary translation on a.e. classes, with Lebesgue measure. -/
def translate {d : ℕ} (y : Euclidean d) (f : L1 d) : L1 d :=
  Lp.compMeasurePreserving (fun x => x - y) (measurePreserving_sub_right volume y) f

/-- Convolution as the Bochner integral of translations. Its identification with
`x ↦ ∫ y, f y * g (x-y)` is a separate proof obligation. -/
def convolution {d : ℕ} (f g : L1 d) : L1 d := ∫ y, f y • translate y g

def TranslationInvariant {d : ℕ} (Y : Submodule ℂ (L1 d)) : Prop :=
  ∀ y f, f ∈ Y → translate y f ∈ Y

/-- The algebraic unitization product: `(a,f)` represents `a δ + f`. -/
def unitizedMul {d : ℕ} (u v : ℂ × L1 d) : ℂ × L1 d :=
  (u.1 * v.1, u.1 • v.2 + v.1 • u.2 + convolution u.2 v.2)

end ExpandedFA.PartIV.WienerLocalIdeal

namespace Specs.ExpandedFA.PartIV.WienerLocalIdeal
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.PartIV.WienerLocalIdeal

def ConvolutionFormula : Prop := ∀ (d : ℕ) (f g : L1 d),
  (convolution f g : Euclidean d → ℂ) =ᵐ[volume] (fun x => ∫ y, f y * g (x-y))

def ConvolutionBound : Prop := ∀ (d : ℕ) (f g : L1 d),
  ‖convolution f g‖ ≤ ‖f‖ * ‖g‖

def ConvolutionIdeal : Prop := ∀ (d : ℕ) (Y : Submodule ℂ (L1 d)),
  IsClosed (Y : Set (L1 d)) → TranslationInvariant Y →
  ∀ (f g : L1 d), f ∈ Y → convolution f g ∈ Y

/-- A genuine two-sided inverse in the algebraic unitization, with an L¹ kernel. -/
def UnitizedInverse : Prop := ∀ (d : ℕ) (h : L1 d), ‖h‖ < 1 →
  ∃ k : L1 d,
    unitizedMul (1, -h) (1, k) = (1, 0) ∧
    unitizedMul (1, k) (1, -h) = (1, 0)

/-- The local membership conclusion at every nonzero Fourier evaluation.
The Fourier support is the closure of the set where the transform is nonzero.
There is no restriction on the dimension. -/
def LocalIdeal : Prop := ∀ (d : ℕ) (Y : Submodule ℂ (L1 d)),
  IsClosed (Y : Set (L1 d)) → TranslationInvariant Y →
  ∀ (f : L1 d), f ∈ Y → ∀ (ξ₀ : Euclidean d), integralFourier f ξ₀ ≠ 0 →
    ∃ U : Set (Euclidean d), IsOpen U ∧ ξ₀ ∈ U ∧
      ∀ ψ : Schwartz ℂ d, tsupport (schwartzFourier ψ) ⊆ U → ψ.toLp 1 (volume : Measure (Euclidean d)) ∈ Y

end Specs.ExpandedFA.PartIV.WienerLocalIdeal
