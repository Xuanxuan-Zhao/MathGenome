import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ContinuousAeSequence
import MathGenome.Internal.RealAnalysis.D11.Ch07.LusinRealLine
import MathGenome.Internal.RealAnalysis.D11.Ch01.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-! Continuous approximation almost everywhere on any Lebesgue measurable
subset of the real line. Lusin extensions with geometric losses agree
eventually at almost every point, by the first Borel–Cantelli lemma. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace D11.Ch07.ContinuousAeSequence

theorem continuous_ae_sequence :
    Specs.D11.Ch07.ContinuousAeSequence.continuous_ae_sequence := by
  intro E hE f hf
  classical
  choose F hFE g hclosed hcont herror hagree using fun n : ℕ =>
    LusinRealLine.lusin_real E hE f hf ((1 / 2 : ℝ) ^ n)
      (pow_pos (by norm_num) n)
  let μ₀ : Measure ℝ := volume
  let : MeasurableSpace ℝ := Specs.D11.Ch07.LusinRealLine.realLebesgueSpace
  let μ : Measure ℝ := μ₀.completion
  let bad : ℕ → Set ℝ := fun n => E \ F n
  have hsum : (∑' n, μ (bad n)) < ∞ := by
    calc
      (∑' n, μ (bad n)) ≤ ∑' n, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
        ENNReal.tsum_le_tsum (fun n => (herror n).le)
      _ = ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n := by
        congr 1
        funext n
        rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ < ∞ := by rw [ENNReal.tsum_geometric_two]; norm_num
  refine ⟨g, hcont, ?_⟩
  filter_upwards [ae_eventually_notMem hsum.ne] with x hx
  intro hxE
  have heq : (fun n => g n x) =ᶠ[atTop] (fun _ => f ⟨x, hxE⟩) := by
    filter_upwards [hx] with n hn
    have hxF : x ∈ F n := by
      by_contra h
      exact hn ⟨hxE, h⟩
    exact hagree n ⟨x, hxF⟩
  exact tendsto_const_nhds.congr' heq.symm

end D11.Ch07.ContinuousAeSequence
