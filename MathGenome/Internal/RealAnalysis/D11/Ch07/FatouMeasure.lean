import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.FatouMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch07.SubsequenceUniqueness
import MathGenome.Internal.RealAnalysis.D11.Ch05.Fatou

/-!
Fatou for global convergence in measure (paper.tex:2382–2393).

Choose indices tending to infinity along which the nonnegative integrals
converge to their lower limit. Global convergence in measure persists along
these indices. The upstream subsequence theorem supplies a further sequence
converging almost everywhere to the prescribed limit. Continuity of
`ENNReal.ofReal` and ordinary Fatou give the bound. The selection theorem is
valid in the complete ordered space `ℝ≥0∞`, so this argument also covers an
infinite lower limit directly.
-/

open Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace D11.Ch07.FatouMeasure

open D11.Ch07.ConvergenceDefinitions
open D11.Ch07.SubsequenceUniqueness
open D11.Ch04.AeCommonException
open D11.Ch05.NonnegativeIntegral

theorem fatou_measure : Specs.D11.Ch07.FatouMeasure.fatou_measure.{u} := by
  intro X _ μ f g hf hg _hf0 _hg0 h
  change nonnegativeIntegral μ (fun x => ENNReal.ofReal (g x)) ≤
    liminf (fun n => nonnegativeIntegral μ (fun x => ENNReal.ofReal (f n x))) atTop
  obtain ⟨ns, hI, hns⟩ := exists_seq_tendsto_liminf
    (u := fun n => nonnegativeIntegral μ (fun x => ENNReal.ofReal (f n x)))
    (f := atTop)
  have hm : inMeasureConverges μ (fun n => f (ns n)) g :=
    fun ε hε => (h ε hε).comp hns
  obtain ⟨ms, hms, hae⟩ := exists_ae_subsequence μ (fun n => f (ns n)) g hm
  have hle : almostEverywhere μ (fun x => ENNReal.ofReal (g x) ≤
      liminf (fun n => ENNReal.ofReal (f (ns (ms n)) x)) atTop) := by
    apply almostEverywhere_mono μ _ _ hae
    intro x hx
    exact le_of_eq (ENNReal.tendsto_ofReal hx).liminf_eq.symm
  have hfatou := D11.Ch05.Fatou.fatou_of_ae_le_liminf μ
    (fun n x => ENNReal.ofReal (f (ns (ms n)) x))
    (fun x => ENNReal.ofReal (g x))
    (fun n => (hf (ns (ms n))).ennreal_ofReal) hg.ennreal_ofReal hle
  change nonnegativeIntegral μ (fun x => ENNReal.ofReal (g x)) ≤
    liminf (fun n => nonnegativeIntegral μ
      (fun x => ENNReal.ofReal (f (ns (ms n)) x))) atTop at hfatou
  exact hfatou.trans_eq (hI.comp hms.tendsto_atTop).liminf_eq

end D11.Ch07.FatouMeasure
