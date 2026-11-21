import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CanonicalGreen
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.TruncatedGreenIdentity

/-! Symmetry from paper.tex:2681–2691.  The total Green representatives have
arbitrary values at their poles; all symmetry assertions use distinct points. -/
noncomputable section
open Set Metric Filter
open scoped Topology

namespace Specs.D12Complex.Ch14.GreenSymmetry
open _root_.D12Complex _root_.D12Complex.CircularExhaustion
open _root_.D12Complex.TruncatedGreenIdentity

/-- The normalized negative logarithmic pole contributes minus 2π times the
other function's value. The normal points into the deleted disk. -/
def normalized_pole_circle_flux_type : Prop :=
  ∀ (D : Set ℂ) (a : ℂ) (u v : ℂ → ℝ), IsOpen D → a ∈ D →
    NormalizedPole D a u →
    (∃ R : ℝ, 0 < R ∧ HarmonicOn (ball a R) v) →
    Tendsto (circleFlux D u v a) (𝓝[>] 0) (𝓝 (-2 * Real.pi * v a))

/-- First establish symmetry on the actual regular circular stages. -/
def circular_stage_green_symmetry_type : Prop :=
  ∀ (Ω : Set ℂ) (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ),
    IsCircularExhaustion Ω s r → ∀ (j : ℕ) (a b : ℂ),
    a ∈ diskUnion (s j) (r j) → b ∈ diskUnion (s j) (r j) → a ≠ b →
    RegularGreen.regularGreen_value (diskUnion (s j) (r j)) a b =
      RegularGreen.regularGreen_value (diskUnion (s j) (r j)) b a

/-- Canonical symmetry on every bounded domain, including irregular domains. -/
def canonical_green_symmetry_type : Prop :=
  ∀ (Ω : Set ℂ) (a b : ℂ), IsDomain Ω → Bornology.IsBounded Ω →
    a ∈ Ω → b ∈ Ω → a ≠ b →
    CanonicalGreen.canonicalGreen_value Ω a b =
      CanonicalGreen.canonicalGreen_value Ω b a

end Specs.D12Complex.Ch14.GreenSymmetry
