import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Space
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Algebra.Support

/-!
Independent statements for the density assertion in paper.tex:2270–2304.
The ambient space is the upstream graph realization with its sum norm.
No extension property or regularity of a boundary is involved.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace P102.Fractional

/-- Whole-space Gagliardo classes admitting a compactly supported representative.
The representative need not be continuous. -/
def compactElements {d : ℕ} (𝕜 : Type*) [RCLike 𝕜] (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : Set (Space 𝕜 (Set.univ : Set (Domain d)) s p) :=
  {u | ∃ f : Domain d → 𝕜, HasCompactSupport f ∧
    f =ᵐ[domainMeasure Set.univ] (firstProjection u : Domain d → 𝕜)}

/-- The actual smooth compactly supported classes in the original space.
Smoothness is over the real Euclidean domain, for both real and complex values. -/
def smoothCompactElements {d : ℕ} (𝕜 : Type*) [RCLike 𝕜] (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : Set (Space 𝕜 (Set.univ : Set (Domain d)) s p) :=
  {u | ∃ f : Domain d → 𝕜, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
    f =ᵐ[domainMeasure Set.univ] (firstProjection u : Domain d → 𝕜)}

end P102.Fractional

namespace Specs.P102.Fractional.Density
open _root_.P102.Fractional

/-- All smooth compactly supported functions belong to the actual Gagliardo
space, including the endpoint p = 1. This also specifies the inclusion implicit
in the statement that C_c^∞ is dense. -/
def SmoothCompactMembership : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜] (s : ℝ),
    0 < s → s < 1 → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ f : Domain d → 𝕜, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f →
      MemLp f p (domainMeasure Set.univ) ∧
      MemLp (increment f) p (pairMeasure Set.univ s p)

/-- Density in the full norm ||u||_p + [u]_{s,p}, with every finite exponent
1 ≤ p and every 0 < s < 1. The topology here is the canonical inherited sum
norm topology, not just the topology of the first Lp projection. -/
def SmoothCompactDensity : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜] (s : ℝ),
    0 < s → s < 1 → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
      Dense (smoothCompactElements (d := d) 𝕜 s p)

end Specs.P102.Fractional.Density
