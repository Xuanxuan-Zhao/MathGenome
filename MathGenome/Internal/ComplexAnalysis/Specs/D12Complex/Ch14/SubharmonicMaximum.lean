import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.SubharmonicDefinition
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.BoundaryMaximum

/-! Maximum and comparison principles for the continuous subharmonic class
of paper.tex:2611–2616. The boundary condition is the shared epsilon-delta
form of the upper limit through the open set; boundary values or a
continuous extension to the boundary are not assumed. -/
noncomputable section
open Set Metric

namespace Specs.D12Complex.Ch14.SubharmonicMaximum
open _root_.D12Complex

/-- Bounded open sets may be empty or disconnected. -/
def subharmonic_boundary_maximum_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ) (M : ℝ), Bornology.IsBounded U →
    SubharmonicOn U u → BoundaryLimsupLE U u M → ∀ z ∈ U, u z ≤ M

/-- Only an attained global maximum is assumed; the domain need not be bounded. -/
def subharmonic_strong_maximum_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), IsDomain U → SubharmonicOn U u →
    ∀ a ∈ U, (∀ z ∈ U, u z ≤ u a) → ∀ z ∈ U, u z = u a

/-- Subtraction uses the actual differential notion of harmonicity. -/
def subharmonic_sub_harmonic_type : Prop :=
  ∀ (U : Set ℂ) (u h : ℂ → ℝ), SubharmonicOn U u → HarmonicOn U h →
    SubharmonicOn U (fun z => u z - h z)

/-- Harmonic comparison with a boundary upper limit for the difference. -/
def subharmonic_harmonic_boundary_comparison_type : Prop :=
  ∀ (U : Set ℂ) (u h : ℂ → ℝ) (M : ℝ), Bornology.IsBounded U →
    SubharmonicOn U u → HarmonicOn U h →
    BoundaryLimsupLE U (fun z => u z - h z) M →
    ∀ z ∈ U, u z ≤ h z + M

/-- In particular a zero boundary upper limit for the difference gives comparison. -/
def subharmonic_harmonic_comparison_type : Prop :=
  ∀ (U : Set ℂ) (u h : ℂ → ℝ), Bornology.IsBounded U →
    SubharmonicOn U u → HarmonicOn U h →
    BoundaryLimsupLE U (fun z => u z - h z) 0 →
    ∀ z ∈ U, u z ≤ h z

end Specs.D12Complex.Ch14.SubharmonicMaximum
