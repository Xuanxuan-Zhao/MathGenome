import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.Fatou
import MathGenome.Internal.RealAnalysis.D11.Ch05.AlgebraNull
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Fatou's inequality and its almost-everywhere lower-bound version
(paper.tex:1637–1657). The library inequality is transported through the
proved equality of the canonical simple-minorant integral with `lintegral`.
The second conclusion uses measurability of the pointwise liminf and the
shared a.e. order property. No restriction on total mass or completeness
is used, and no nonmeasurable modification is made.
-/

open Filter MeasureTheory
open scoped ENNReal
universe u

namespace D11.Ch05.Fatou

open NonnegativeIntegral

theorem fatou : Specs.D11.Ch05.Fatou.fatou.{u} := by
  intro X _ μ f hf
  change nonnegativeIntegral μ (fun x => liminf (fun n => f n x) atTop) ≤
    liminf (fun n => nonnegativeIntegral μ (f n)) atTop
  simp only [integral_eq_lintegral]
  exact lintegral_liminf_le hf

theorem fatou_of_ae_le_liminf : Specs.D11.Ch05.Fatou.fatou_of_ae_le_liminf.{u} := by
  intro X _ μ f g hf hg hle
  exact (AlgebraNull.ae_monotonicity μ g
    (fun x => liminf (fun n => f n x) atTop) hg (Measurable.liminf hf) hle).trans
      (fatou μ f hf)

end D11.Ch05.Fatou
