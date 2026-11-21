import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.RegularDirichlet
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The bounded regular-domain part of paper.tex:2681–2691.
The total representatives have no prescribed value at the pole or outside
 the closure. A normalized pole is a local harmonic extension of g + log. -/
noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex

def HasNormalizedLogPole (Ω : Set ℂ) (a : ℂ) (g : ℂ → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ball a r ⊆ Ω ∧ ∃ h : ℂ → ℝ,
    HarmonicOn (ball a r) h ∧
      EqOn h (fun z => g z + Real.log ‖z - a‖) (ball a r \ {a})

/-- Positivity is deliberately absent from the uniqueness hypotheses. -/
def IsZeroBoundaryGreen (Ω : Set ℂ) (a : ℂ) (g : ℂ → ℝ) : Prop :=
  HarmonicOn (Ω \ {a}) g ∧ HasNormalizedLogPole Ω a g ∧
    ContinuousOn g (closure Ω \ {a}) ∧ EqOn g (fun _ => 0) (frontier Ω)

end D12Complex

namespace Specs.D12Complex.Ch14.RegularGreen
open _root_.D12Complex

def regularGreen_type := Set ℂ → ℂ → ℂ → ℝ
def regularGreen_value : regularGreen_type := fun Ω a z =>
  RegularDirichlet.perronSolution_value Ω (fun ξ => Real.log ‖ξ - a‖) z - Real.log ‖z - a‖

def HasNormalizedLogPole_type := Set ℂ → ℂ → (ℂ → ℝ) → Prop
def HasNormalizedLogPole_value : HasNormalizedLogPole_type := fun Ω a g =>
  ∃ r : ℝ, 0 < r ∧ ball a r ⊆ Ω ∧ ∃ h : ℂ → ℝ,
    HarmonicOn (ball a r) h ∧
      EqOn h (fun z => g z + Real.log ‖z - a‖) (ball a r \ {a})

def IsZeroBoundaryGreen_type := Set ℂ → ℂ → (ℂ → ℝ) → Prop
def IsZeroBoundaryGreen_value : IsZeroBoundaryGreen_type := fun Ω a g =>
  HarmonicOn (Ω \ {a}) g ∧ HasNormalizedLogPole Ω a g ∧
    ContinuousOn g (closure Ω \ {a}) ∧ EqOn g (fun _ => 0) (frontier Ω)

/-- Construction, harmonicity, pole normalization, continuous zero boundary
extension, and strict positivity under precisely the original hypotheses. -/
def regular_green_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ), IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) → a ∈ Ω →
    IsZeroBoundaryGreen Ω a (regularGreen_value Ω a) ∧
      (∀ z ∈ Ω \ {a}, 0 < regularGreen_value Ω a z) ∧
      (∀ ξ ∈ frontier Ω,
        Tendsto (regularGreen_value Ω a) (𝓝[Ω] ξ) (𝓝 0))

/-- The pole condition is local, and no sign assumption is made on a competitor.
Equality includes the boundary and excludes the immaterial pole value. -/
def regular_green_unique_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ), IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) → a ∈ Ω →
    ∀ g : ℂ → ℝ, IsZeroBoundaryGreen Ω a g →
      EqOn g (regularGreen_value Ω a) (closure Ω \ {a})

end Specs.D12Complex.Ch14.RegularGreen
