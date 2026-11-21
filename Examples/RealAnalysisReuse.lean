import MathGenome.RealAnalysis
import Examples.RealAnalysisReuseSpecs

/-! Integration probes for composition of the delivered public interfaces.
Root compiles these independently against the assembled MathGenome library. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Examples.GenomeAnalysisProbe

theorem complexPrimitiveStieltjes :
    Examples.GenomeAnalysisProbeSpecs.complexPrimitiveStieltjes := by
  intro f c a b hab hf
  let F : ℝ → ℂ := fun x => c + ∫ t in a..x, f t
  have hAC : D11.Ch12.AbsolutelyContinuousOnInterval F a b :=
    D11.Ch12.AcPrimitive.primitive_ac f c hab hf
  have hG := (D11.Ch12.AcStieltjesEquivalence.compact_complex F hab).1.mp hAC
  rcases hG with ⟨⟨hBV, hright, hbot⟩, hcontinuous, hac⟩
  exact ⟨hBV, hright, hbot, hcontinuous, hac⟩

theorem complexPrimitiveVariationAndRepresentative :
    Examples.GenomeAnalysisProbeSpecs.complexPrimitiveVariationAndRepresentative := by
  intro f c a b hab hf
  refine ⟨D11.Ch12.AcPrimitive.primitive_variation f c hab hf,
    D11.Ch12.AcPrimitive.primitive_derivative f c hab hf, ?_⟩
  intro g hg hfg x hx
  exact D11.Ch12.AcPrimitive.primitive_representative_independent
    f g c hab hf hg hfg x hx

theorem squareRootProductFtc :
    Examples.GenomeAnalysisProbeSpecs.squareRootProductFtc := by
  let F : ℝ → ℝ := fun x => Real.sqrt x * Real.sqrt x
  have hAC : D11.Ch12.AbsolutelyContinuousOnInterval F 0 1 :=
    D11.Ch12.AcBasic.mul (by norm_num)
      D11.Ch12.AcBasic.sqrt_ac D11.Ch12.AcBasic.sqrt_ac
  have hftc := (D11.Ch12.AcFtc.ftc_real F (by norm_num : (0 : ℝ) < 1)).2.1.mp hAC
  exact ⟨hftc.2.1, hftc.1, hftc.2.2⟩

end Examples.GenomeAnalysisProbe
