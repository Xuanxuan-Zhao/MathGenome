import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Interpolation.ThreeLines
import Mathlib.Analysis.Complex.Hadamard

namespace ExpandedFA.Interpolation

open Complex Complex.HadamardThreeLines

/-- The three-lines lemma with the paper's boundary parametrizations.
Zero boundary bounds are included in Mathlib's limiting form of Hadamard's
theorem; no positivity assumption on either bound is imposed here. -/
theorem three_lines : Specs.ExpandedFA.Interpolation.ThreeLines := by
  intro F M₀ M₁ θ hbounded hcontinuous hholomorphic hleft hright hθ₀ hθ₁
  have hd : DiffContOnCl ℂ F (verticalStrip 0 1) := by
    refine ⟨hholomorphic, ?_⟩
    rw [verticalStrip, Complex.closure_preimage_re,
      closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
    exact hcontinuous
  have hB : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 1) := by
    obtain ⟨C, hC⟩ := hbounded
    refine ⟨C, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact hC z hz.1 hz.2
  have ha : ∀ z ∈ Complex.re ⁻¹' {0}, ‖F z‖ ≤ M₀ := by
    intro z hz
    have hre : z.re = 0 := hz
    have heq : (z.im : ℂ) * I = z := by
      apply Complex.ext <;> simp [hre]
    simpa only [heq] using hleft z.im
  have hb : ∀ z ∈ Complex.re ⁻¹' {1}, ‖F z‖ ≤ M₁ := by
    intro z hz
    have hre : z.re = 1 := hz
    have heq : 1 + (z.im : ℂ) * I = z := by
      apply Complex.ext <;> simp [hre]
    simpa only [heq] using hright z.im
  have hz : (θ : ℂ) ∈ verticalClosedStrip 0 1 := ⟨hθ₀.le, hθ₁.le⟩
  simpa only [Complex.ofReal_re] using
    norm_le_interp_of_mem_verticalClosedStrip₀₁' F hz hd hB ha hb

end ExpandedFA.Interpolation
