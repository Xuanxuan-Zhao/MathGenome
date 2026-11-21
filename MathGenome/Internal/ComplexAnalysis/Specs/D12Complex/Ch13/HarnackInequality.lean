import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarmonicFoundation

/-! Harnack's inequalities and their uniform compact propagation
(paper.tex:2584–2594). Harmonicity is required only on the open disk/domain. -/
noncomputable section
open Metric Set

namespace Specs.D12Complex.Ch13.HarnackInequality
open _root_.D12Complex

/-- The sharp disk estimate, including the center and nonnegative functions
which vanish there. No value on the radius-R circle is constrained. -/
def harnack_disk_type : Prop :=
  ∀ (u : ℂ → ℝ) (a : ℂ) (R : ℝ), 0 < R →
    HarmonicOn (ball a R) u → (∀ w ∈ ball a R, 0 ≤ u w) →
    ∀ z ∈ ball a R,
      (R - ‖z - a‖) / (R + ‖z - a‖) * u a ≤ u z ∧
      u z ≤ (R + ‖z - a‖) / (R - ‖z - a‖) * u a

/-- The constant is chosen before u, hence depends only on the domain,
basepoint and compact set. Empty compact sets are included. -/
def harnack_compact_type : Prop :=
  ∀ (Ω : Set ℂ), IsDomain Ω → ∀ a ∈ Ω,
    ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : ℂ → ℝ),
        HarmonicOn Ω u → (∀ w ∈ Ω, 0 ≤ u w) →
        ∀ z ∈ K, C⁻¹ * u a ≤ u z ∧ u z ≤ C * u a

end Specs.D12Complex.Ch13.HarnackInequality
