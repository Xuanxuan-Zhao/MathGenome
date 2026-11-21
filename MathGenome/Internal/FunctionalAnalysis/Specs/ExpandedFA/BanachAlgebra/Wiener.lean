import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Instances.Int

/-!
The ℤ specialization of paper.tex:10282–10320 (fa2:p2:wiener).
`ZGroup` is ℤ in multiplicative notation. Counting-measure L¹ retains
precisely the absolutely summable coefficient sequences. The spectrum below
uses its own identity δ₀ and two-sided convolution inverses, without adding
an external unit. The Fourier convention is Σ aₙ zⁿ, for every z on the circle.
-/
noncomputable section
open MeasureTheory

namespace Specs.ExpandedFA.BanachAlgebra.Wiener

abbrev ZGroup := Multiplicative ℤ
instance : Countable ZGroup := inferInstanceAs (Countable ℤ)
instance : MeasurableSpace ZGroup := borel ZGroup
instance : BorelSpace ZGroup := ⟨rfl⟩
abbrev counting : Measure ZGroup := Measure.count
instance : counting.IsHaarMeasure where
  lt_top_of_isCompact := fun K hK => by
    rw [counting, Measure.count_apply_finite K hK.finite_of_discrete]
    exact ENNReal.natCast_lt_top _
  open_pos := fun U _ hU => Measure.count_ne_zero hU
abbrev L1 := GroupAlgebraCharacters.L1 counting
abbrev convolution := GroupAlgebraCharacters.convolutionValue counting

def delta : L1 := indicatorConstLp 1 (measurableSet_singleton (1 : ZGroup))
  (by simp [counting]) (1 : ℂ)

def coefficient (a : L1) (n : ℤ) : ℂ := a (Multiplicative.ofAdd n)

def fourier (a : L1) (z : Circle) : ℂ := ∑' n : ℤ, coefficient a n * (z : ℂ) ^ n

def series (a : ℤ → ℂ) (z : Circle) : ℂ := ∑' n : ℤ, a n * (z : ℂ) ^ n

def unitalSpectrum (a : L1) : Set ℂ :=
  {w | ¬ ∃ b : L1, convolution (w • delta - a) b = delta ∧
    convolution b (w • delta - a) = delta}

def IntegerGroupCharacters : Prop :=
  ∀ γ : ZGroup →ₜ* Circle, ∃! z : Circle, ∀ n : ℤ, γ (Multiplicative.ofAdd n) = z ^ n

def SequenceIdentification : Prop :=
  (∀ a : L1, Summable (fun n : ℤ => ‖coefficient a n‖)) ∧
  (∀ a : ℤ → ℂ, Summable (fun n => ‖a n‖) →
    ∃ f : L1, ∀ n, coefficient f n = a n)

def SequenceNorm : Prop :=
  ∀ a : L1, ‖a‖ = ∑' n : ℤ, ‖coefficient a n‖

def ConvolutionCoefficients : Prop :=
  ∀ a b : L1, ∀ n : ℤ, coefficient (convolution a b) n =
    ∑' k : ℤ, coefficient a k * coefficient b (n - k)

def AbsoluteFourierConvergence : Prop :=
  ∀ a : ℤ → ℂ, Summable (fun n => ‖a n‖) →
    ∀ z : Circle, Summable (fun n => ‖a n * (z : ℂ) ^ n‖)

def ConvolutionIdentity : Prop :=
  ‖delta‖ = 1 ∧ ∀ a : L1, convolution delta a = a ∧ convolution a delta = a

def CharacterClassification : Prop :=
  (∀ z : Circle, ∃ χ : L1 →ₗ[ℂ] ℂ,
    GroupAlgebraCharacters.IsCharacter counting χ ∧ ∀ a, χ a = fourier a z) ∧
  (∀ χ : L1 →ₗ[ℂ] ℂ, GroupAlgebraCharacters.IsCharacter counting χ →
    ∃! z : Circle, ∀ a, χ a = fourier a z)

def SpectrumFormula : Prop :=
  ∀ a : L1, unitalSpectrum a = Set.range (fourier a)

def InverseCriterion : Prop :=
  ∀ a : L1, (∀ z : Circle, fourier a z ≠ 0) ↔
    ∃ b : L1, convolution a b = delta ∧ convolution b a = delta

def WienerReciprocal : Prop :=
  ∀ a : ℤ → ℂ, Summable (fun n => ‖a n‖) →
    (∀ z : Circle, series a z ≠ 0) →
    ∃ b : ℤ → ℂ, Summable (fun n => ‖b n‖) ∧
      ∀ z : Circle, series b z = (series a z)⁻¹

end Specs.ExpandedFA.BanachAlgebra.Wiener
