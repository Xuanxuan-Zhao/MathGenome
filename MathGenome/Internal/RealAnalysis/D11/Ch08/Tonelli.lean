import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.Tonelli
import MathGenome.Internal.RealAnalysis.D11.Ch08.ProductMeasure

/-!
Tonelli's theorem on the ordinary product, paper.tex:2617–2637.

The upstream one-sided theorem supplies measurability of both source
section-integral maps. Every section is measurable on the original factor
sigma-algebra. The upstream `NonnegativeIntegral.eq_lintegral` therefore
identifies its source integral with the native nonnegative integral; it also
identifies the outer and product integrals. Mathlib's `lintegral_prod` and
`lintegral_prod_symm` then give the two identities. These library theorems
apply to s-finite measures, supplied here by the source's sigma-finiteness.
The native product is the same canonical product established upstream.
No integrability, completion, or nonemptiness assumption is used.
-/

open MeasureTheory
open scoped ENNReal
open Specs.D11.Ch05.NonnegativeIntegral (nonnegativeIntegral_value)
open Specs.D11.Ch08.ProductMeasure (productMeasure_value)

universe u v
noncomputable section

namespace D11.Ch08.Tonelli

theorem section_integrals_measurable :
    Specs.D11.Ch08.Tonelli.section_integrals_measurable.{u, v} := by
  intro X Y _ _ μ ν hμ hν f hf
  refine ⟨SectionIntegralsOneSided.section_integral_measurable ν hν f hf, ?_⟩
  exact SectionIntegralsOneSided.section_integral_measurable μ hμ
    (fun p : Y × X => f p.swap) (hf.comp measurable_swap)

theorem integral_product_left : Specs.D11.Ch08.Tonelli.integral_product_left.{u, v} := by
  intro X Y m n μ ν hμ hν f hf
  let : SigmaFinite ν := hν
  have hm := (section_integrals_measurable μ ν hμ hν f hf).1
  have hinner (x : X) :
      nonnegativeIntegral_value ν (fun y : Y => f (x, y)) = ∫⁻ y, f (x, y) ∂ν :=
    D11.Ch05.NonnegativeIntegral.eq_lintegral ν _
      (Sections.function_section_left m n inferInstance f hf x)
  calc
    nonnegativeIntegral_value (productMeasure_value μ ν) f =
        ∫⁻ z, f z ∂μ.prod ν := D11.Ch05.NonnegativeIntegral.eq_lintegral _ _ hf
    _ = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := lintegral_prod f hf.aemeasurable
    _ = nonnegativeIntegral_value μ (fun x : X =>
          nonnegativeIntegral_value ν (fun y : Y => f (x, y))) := by
      rw [D11.Ch05.NonnegativeIntegral.eq_lintegral μ _ hm]
      simp_rw [hinner]

theorem integral_product_right : Specs.D11.Ch08.Tonelli.integral_product_right.{u, v} := by
  intro X Y m n μ ν hμ hν f hf
  let : SigmaFinite μ := hμ
  let : SigmaFinite ν := hν
  have hm := (section_integrals_measurable μ ν hμ hν f hf).2
  have hinner (y : Y) :
      nonnegativeIntegral_value μ (fun x : X => f (x, y)) = ∫⁻ x, f (x, y) ∂μ :=
    D11.Ch05.NonnegativeIntegral.eq_lintegral μ _
      (Sections.function_section_right m n inferInstance f hf y)
  calc
    nonnegativeIntegral_value (productMeasure_value μ ν) f =
        ∫⁻ z, f z ∂μ.prod ν := D11.Ch05.NonnegativeIntegral.eq_lintegral _ _ hf
    _ = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := lintegral_prod_symm f hf.aemeasurable
    _ = nonnegativeIntegral_value ν (fun y : Y =>
          nonnegativeIntegral_value μ (fun x : X => f (x, y))) := by
      rw [D11.Ch05.NonnegativeIntegral.eq_lintegral ν _ hm]
      simp_rw [hinner]

theorem tonelli : Specs.D11.Ch08.Tonelli.tonelli.{u, v} := by
  intro X Y _ _ μ ν hμ hν f hf
  obtain ⟨hmleft, hmright⟩ := section_integrals_measurable μ ν hμ hν f hf
  have hleft := integral_product_left μ ν hμ hν f hf
  have hright := integral_product_right μ ν hμ hν f hf
  exact ⟨hmleft, hmright, hleft, hleft.symm.trans hright⟩

end D11.Ch08.Tonelli
