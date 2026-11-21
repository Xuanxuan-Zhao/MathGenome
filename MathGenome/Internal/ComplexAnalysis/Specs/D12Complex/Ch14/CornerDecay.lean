import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularExhaustion
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent statements for the corner estimates in paper.tex:2660–2669.
The local geometry is the upstream, actual biholomorphic sector chart. The
hypotheses impose harmonicity only on the interior cap and continuity on the
closure cap; in particular they impose no derivative bound at the corner.
The norm of the gradient uses the real inner product on the complex plane. -/
noncomputable section
open Set Metric
open scoped ContDiff

namespace Specs.D12Complex.Ch14.CornerDecay
open _root_.D12Complex _root_.D12Complex.CircularExhaustion

/-- The full corner conclusion for any open set with the specified local
geometry, hence in particular for each circular exhaustion stage. -/
def corner_decay_type : Prop :=
  ∀ (D : Set ℂ) (c : ℂ) (θ R : ℝ) (u : ℂ → ℝ),
    IsOpen D → 0 < θ → θ < 2 * Real.pi → SectorChart D c θ → 0 < R →
    HarmonicOn (D ∩ ball c R) u →
    ContinuousOn u (closure D ∩ ball c R) →
    (∀ z ∈ frontier D ∩ ball c R, u z = 0) →
    ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ R ∧
      ∀ z ∈ D, ‖z - c‖ < r₀ →
        |u z| ≤ C * ‖z - c‖ ^ (Real.pi / θ) ∧
        ‖gradient u z‖ ≤ C * ‖z - c‖ ^ (Real.pi / θ - 1)

/-- Smooth extension across a noncorner arc. Equality includes the boundary,
while all derivatives of the extension are taken on a full open neighborhood. -/
def smooth_boundary_extension_type : Prop :=
  ∀ (D : Set ℂ) (c : ℂ) (R : ℝ) (u : ℂ → ℝ),
    IsOpen D → SectorChart D c Real.pi → 0 < R →
    HarmonicOn (D ∩ ball c R) u →
    ContinuousOn u (closure D ∩ ball c R) →
    (∀ z ∈ frontier D ∩ ball c R, u z = 0) →
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∃ v : ℂ → ℝ,
      HarmonicOn (ball c r) v ∧ ContDiffOn ℝ ∞ v (ball c r) ∧
      EqOn v u (closure D ∩ ball c r)

/-- The quantitative real-calculus step used after harmonic reflection.
It bounds both the function vanishing at its center and its actual gradient. -/
def harmonic_linear_bounds_type : Prop :=
  ∀ (U : Set ℂ) (v : ℂ → ℝ) (c : ℂ), HarmonicOn U v → c ∈ U → v c = 0 →
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ball c r ⊆ U ∧
      ∀ z ∈ ball c r, |v z| ≤ C * ‖z - c‖ ∧ ‖gradient v z‖ ≤ C

/-- The straight-sector estimate, with the same zero data and no
extension or derivative estimate included in the hypotheses. -/
def sector_decay_type : Prop :=
  ∀ (θ R : ℝ) (u : ℂ → ℝ), 0 < θ → θ < 2 * Real.pi → 0 < R →
    HarmonicOn (sector θ ∩ ball 0 R) u →
    ContinuousOn u (closure (sector θ) ∩ ball 0 R) →
    (∀ z ∈ frontier (sector θ) ∩ ball 0 R, u z = 0) →
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      ∀ z ∈ sector θ, ‖z‖ < r →
        |u z| ≤ C * ‖z‖ ^ (Real.pi / θ) ∧
        ‖gradient u z‖ ≤ C * ‖z‖ ^ (Real.pi / θ - 1)

/-- A proved reduction, to be discharged by a straight-sector theorem. This
conditional statement is not itself the unconditional corner theorem. -/
def corner_decay_of_sector_decay_type : Prop := sector_decay_type → corner_decay_type

/-- Odd reflection supplies the full estimates on a half-disk, with no
regularity assumed on the outer semicircle or its endpoints. -/
def halfDisk_decay_type : Prop :=
  ∀ (R : ℝ) (u : ℂ → ℝ), 0 < R →
    HarmonicOn {z : ℂ | ‖z‖ < R ∧ 0 < z.im} u →
    ContinuousOn u {z : ℂ | ‖z‖ < R ∧ 0 ≤ z.im} →
    (∀ z : ℂ, ‖z‖ < R → z.im = 0 → u z = 0) →
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      ∀ z : ℂ, ‖z‖ < r → 0 < z.im →
        |u z| ≤ C * ‖z‖ ∧ ‖gradient u z‖ ≤ C

/-- Application to the actual exhaustion stages. The same finite corner set
supplies smooth extension at its complement and the two estimates at each
corner, with its actual conformal angle. -/
def exhaustion_boundary_estimates_type : Prop :=
  ∀ (Ω : Set ℂ) (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ),
    IsCircularExhaustion Ω s r → ∀ j : ℕ,
    let D := diskUnion (s j) (r j)
    ∃ corners : Finset ℂ, (↑corners : Set ℂ) ⊆ frontier D ∧
      (∀ c ∈ frontier D, c ∉ corners → ∀ (R : ℝ) (u : ℂ → ℝ), 0 < R →
        HarmonicOn (D ∩ ball c R) u →
        ContinuousOn u (closure D ∩ ball c R) →
        (∀ z ∈ frontier D ∩ ball c R, u z = 0) →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ ∃ v : ℂ → ℝ,
          HarmonicOn (ball c δ) v ∧ ContDiffOn ℝ ∞ v (ball c δ) ∧
          EqOn v u (closure D ∩ ball c δ)) ∧
      ∀ c ∈ corners, ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧ SectorChart D c θ ∧
        ∀ (R : ℝ) (u : ℂ → ℝ), 0 < R →
          HarmonicOn (D ∩ ball c R) u →
          ContinuousOn u (closure D ∩ ball c R) →
          (∀ z ∈ frontier D ∩ ball c R, u z = 0) →
          ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧
            ∀ z ∈ D, ‖z - c‖ < δ →
              |u z| ≤ C * ‖z - c‖ ^ (Real.pi / θ) ∧
              ‖gradient u z‖ ≤ C * ‖z - c‖ ^ (Real.pi / θ - 1)

end Specs.D12Complex.Ch14.CornerDecay
