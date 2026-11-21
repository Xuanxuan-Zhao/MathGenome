import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.ConvergenceComparisons
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.VitaliFiniteMeasure
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.ProbabilityBounds

/-! Convergence comparisons in paper.tex:675–710. Mathlib's convergence-in-measure
results are transported through the proved chapter-1 strict-threshold bridge.
The moment implication uses Markov and integrability of the pth power, requiring
only p > 0, and the final assertion is the finite-measure Vitali theorem. -/

open MeasureTheory Filter
open scoped ENNReal Topology

universe u

namespace ProbabilityFoundations.Ch02
open ProbabilityFoundations.Ch01
open Specs.ProbabilityFoundations.Ch02.ConvergenceComparisons

theorem almostSure_implies_probability : almostSureImpliesProbabilityType := by
  intro Ω mΩ P hP Xn X hXn _hX hconv
  apply (convergesInProbability_iff_tendstoInMeasure P Xn X).mpr
  exact tendstoInMeasure_of_tendsto_ae
    (fun n => (hXn n).stronglyMeasurable.aestronglyMeasurable) hconv

theorem lp_implies_probability : lpImpliesProbabilityType := by
  intro Ω mΩ P hP Xn X p hXn hX hp hXnp hXp hconv
  change ConvergesInMeasure P Xn X
  intro ε hε
  have hint (n : ℕ) : Integrable (fun ω => |Xn n ω - X ω| ^ p) P := by
    simpa only [ENNReal.toReal_ofReal hp.le, Pi.sub_apply, Real.norm_eq_abs] using
      ((hXnp n).sub hXp).integrable_norm_rpow
        (by simpa using hp) ENNReal.ofReal_ne_top
  have hext : Tendsto
      (fun n => ∫⁻ ω, ENNReal.ofReal (|Xn n ω - X ω| ^ p) ∂P) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hconv
    simpa only [ENNReal.ofReal_zero,
      ofReal_integral_eq_lintegral_ofReal (hint _) (ae_of_all P (fun ω =>
        Real.rpow_nonneg (abs_nonneg _) _))] using h
  have hbound := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (ε ^ (-p)))
    hext (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hbound
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le) ?_
  intro n
  exact moment_gt P (fun ω => Xn n ω - X ω) ((hXn n).sub hX) ε p hε hp

theorem probability_iff_subsequences : probabilityIffSubsequencesType := by
  intro Ω mΩ P hP Xn X hXn _hX
  change ConvergesInProbability P Xn X ↔ _
  rw [convergesInProbability_iff_tendstoInMeasure]
  exact exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (hXn n).stronglyMeasurable.aestronglyMeasurable)

theorem probability_limit_unique : probabilityLimitUniqueType := by
  intro Ω mΩ P hP Xn X Y _hXn _hX _hY hconvX hconvY
  exact tendstoInMeasure_ae_unique
    ((convergesInProbability_iff_tendstoInMeasure P Xn X).mp hconvX)
    ((convergesInProbability_iff_tendstoInMeasure P Xn Y).mp hconvY)

theorem probability_ui_implies_l1 : probabilityUiImpliesL1Type := by
  intro Ω mΩ P hP Xn X _hXn hX hconv hui
  have hF : ∀ n, Integrable (Xn n) P := fun n => hui.1 _ (Set.mem_range_self n)
  simpa only [Real.norm_eq_abs] using
    (vitali_finite_measure P Xn X hF hX).mpr ⟨hconv, hui⟩

end ProbabilityFoundations.Ch02
