import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
The compact, real, smooth divergence identity used in the proof of
`paper.tex`, `fa2:p4:second-trace` (the smooth integration-by-parts step).
The chart and geometric-normal hypotheses are written out in full. The
coordinate space, coordinate directions, and surface measure are the existing
Sobolev objects. This statement assumes no area or normalization certificate.
-/

noncomputable section
open Set TopologicalSpace MeasureTheory

namespace Specs.ExpandedFA.PartIV.SmoothBoundaryDivergence
open _root_.ExpandedFA.Distributions
open _root_.ExpandedFA.Sobolev.Trace

/-- Divergence in one coordinate for an ambient smooth compactly supported
real function, on every bounded open set having the displayed C² charts,
with every supplied outward geometric normal. This includes dimension zero. -/
def CompactRealSmoothDivergence : Prop :=
  ∀ (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
    (∀ x ∈ frontier (Ω : Set (Domain d)),
      ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
        x ∈ Φ.source ∧ Φ x i = 0 ∧
        ContDiffOn ℝ 2 Φ Φ.source ∧ ContDiffOn ℝ 2 Φ.symm Φ.target ∧
        ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i) →
    ∀ ν : Fin d → Domain d → ℝ,
      (∀ j, AEStronglyMeasurable (ν j) (surfaceMeasure Ω)) →
      (∀ j, ∀ᵐ x ∂surfaceMeasure Ω, |ν j x| ≤ 1) →
      (∀ x ∈ frontier (Ω : Set (Domain d)),
        ∃ (U : Opens (Domain d)) (r : Domain d → ℝ),
          x ∈ U ∧ ContDiffOn ℝ 2 r U ∧ r x = 0 ∧
          (∀ y ∈ U, y ∈ Ω ↔ r y < 0) ∧
          0 < ∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2 ∧
          ∀ j, ν j x = fderiv ℝ r x (coordinateVector j) /
            Real.sqrt (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2)) →
      ∀ f : Domain d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        ∀ j : Fin d,
          (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) =
            ∫ x, f x * ν j x ∂surfaceMeasure Ω

end Specs.ExpandedFA.PartIV.SmoothBoundaryDivergence
