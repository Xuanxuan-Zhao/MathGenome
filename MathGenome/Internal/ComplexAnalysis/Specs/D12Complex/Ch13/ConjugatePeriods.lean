import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.LocalConjugateRegularity
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.DiskCauchyFormula
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! The global assertions of paper.tex:2539–2548. The real one-form is a
continuous real linear functional at each point. Its period is represented
by the imaginary coordinate of the canonical contour integral; the coordinate
integral bridge below is part of the obligation. -/
noncomputable section
open Complex Set

namespace D12Complex

def conjugateField (u : ℂ → ℝ) (z : ℂ) : ℂ :=
  (partialX u z : ℂ) - I * (partialY u z : ℂ)

def conjugateForm (u : ℂ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (-partialY u z) • reCLM + (partialX u z) • imCLM

def conjugatePeriod (u : ℂ → ℝ) (γ : PiecewiseC1Path) : ℝ :=
  (γ.integral (conjugateField u)).im

end D12Complex

namespace Specs.D12Complex.Ch13.ConjugatePeriods
open _root_.D12Complex

def conjugateField_type := (ℂ → ℝ) → ℂ → ℂ
def conjugateField_value : conjugateField_type :=
  fun u z => (partialX u z : ℂ) - I * (partialY u z : ℂ)
def conjugateForm_type := (ℂ → ℝ) → ℂ → (ℂ →L[ℝ] ℝ)
def conjugateForm_value : conjugateForm_type :=
  fun u z => (-partialY u z) • reCLM + (partialX u z) • imCLM
def conjugatePeriod_type := (ℂ → ℝ) → PiecewiseC1Path → ℝ
def conjugatePeriod_value : conjugatePeriod_type :=
  fun u γ => (γ.integral (conjugateField u)).im

def conjugateForm_apply_type : Prop :=
  ∀ (u : ℂ → ℝ) (z w : ℂ),
    conjugateForm u z w = -partialY u z * w.re + partialX u z * w.im

/-- The period is the sum of the actual real coordinate integrals over the
chosen C¹ pieces of the canonical path. -/
def conjugatePeriod_coordinates_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), HarmonicOn U u →
    ∀ γ : PiecewiseC1Path, γ.trace ⊆ U →
      conjugatePeriod u γ = ∑ i : Fin γ.partition.count,
        ∫ t in γ.partition.node i.castSucc..γ.partition.node i.succ,
          -partialY u (γ t) * (derivWithin γ (γ.partition.pieceSet i) t).re +
            partialX u (γ t) * (derivWithin γ (γ.partition.pieceSet i) t).im

def conjugate_period_endpoint_type : Prop :=
  ∀ (U : Set ℂ) (u v : ℂ → ℝ), HarmonicConjugateOn U u v →
    ∀ γ : PiecewiseC1Path, γ.trace ⊆ U →
      conjugatePeriod u γ = v γ.path.target - v γ.path.source

def global_conjugate_iff_zero_periods_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), IsDomain U → HarmonicOn U u →
    ((∃ v : ℂ → ℝ, HarmonicConjugateOn U u v) ↔
      ∀ γ : PiecewiseC1Path, γ.trace ⊆ U → γ.IsClosed → conjugatePeriod u γ = 0)

def conjugate_unique_type : Prop :=
  ∀ (U : Set ℂ) (u v w : ℂ → ℝ), IsDomain U →
    HarmonicConjugateOn U u v → HarmonicConjugateOn U u w →
    ∃ c : ℝ, ∀ z ∈ U, v z = w z + c

def simply_connected_conjugate_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), IsDomain U → HarmonicOn U u →
    IsSimplyConnected U → ∃ v : ℂ → ℝ, HarmonicConjugateOn U u v

def log_norm_harmonic_type : Prop :=
  HarmonicOn ({0}ᶜ : Set ℂ) (fun z => Real.log ‖z‖)

def log_norm_circle_period_type : Prop :=
  ∀ (c : ℂ) (r : ℝ), 0 < r → ‖c‖ < r →
    conjugatePeriod (fun z => Real.log ‖z‖)
      (Ch04.DiskCauchyFormula.circlePath_value c r) = 2 * Real.pi

def log_norm_no_conjugate_type : Prop :=
  ¬ ∃ v : ℂ → ℝ, HarmonicConjugateOn ({0}ᶜ : Set ℂ) (fun z => Real.log ‖z‖) v

end Specs.D12Complex.Ch13.ConjugatePeriods
