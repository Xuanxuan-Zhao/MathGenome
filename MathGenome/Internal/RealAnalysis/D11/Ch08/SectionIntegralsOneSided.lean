import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.SectionIntegralsOneSided
import MathGenome.Internal.RealAnalysis.D11.Ch08.Sections
import MathGenome.Internal.RealAnalysis.D11.Ch05.NonnegativeIntegral
import Mathlib.MeasureTheory.Measure.Prod

/-!
One-sided measurability of section integrals (paper.tex:2550–2578).

Mathlib proves section-mass measurability for an s-finite measure by first
using a Dynkin-class argument for finite measures, then a countable sum of
finite measures. Its section-integral theorem uses measurable nonnegative
simple functions and monotone convergence. Sigma-finiteness of ν supplies
the s-finite instance; neither theorem assumes a measure on X.

For the function assertion, every section is measurable for the original
factor sigma-algebra by the upstream sections theorem. The proved upstream
bridge identifies its source integral with Mathlib's nonnegative integral.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v

noncomputable section

namespace D11.Ch08.SectionIntegralsOneSided

theorem section_measure_measurable :
    Specs.D11.Ch08.SectionIntegralsOneSided.section_measure_measurable.{u, v} := by
  intro X Y _ _ ν hν E hE
  let : SigmaFinite ν := hν
  exact measurable_measure_prodMk_left hE

theorem section_integral_measurable :
    Specs.D11.Ch08.SectionIntegralsOneSided.section_integral_measurable.{u, v} := by
  intro X Y m n ν hν f hf
  let : SigmaFinite ν := hν
  have hsection (x : X) : Measurable (fun y : Y => f (x, y)) :=
    Sections.function_section_left m n inferInstance f hf x
  have hbridge (x : X) :
      Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value ν
        (fun y : Y => f (x, y)) = ∫⁻ y, f (x, y) ∂ν :=
    D11.Ch05.NonnegativeIntegral.eq_lintegral ν _ (hsection x)
  simpa only [hbridge] using (hf.lintegral_prod_right' (ν := ν))

end D11.Ch08.SectionIntegralsOneSided
