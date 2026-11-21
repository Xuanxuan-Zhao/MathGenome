import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.Sections
import MathGenome.Internal.RealAnalysis.D11.Ch08.ProductSigma
import MathGenome.Internal.RealAnalysis.D11.Ch04.MeasurableMapTests

/-!
Sections of ordinary-product-measurable sets and functions
(`D11.08.sections`, paper.tex:2516–2536).

The shared `productSigma` is definitionally `m.prod n`; its rectangle
generation is established in `D11.Ch08.ProductSigma`. The fixed-coordinate
maps are measurable since a constant map and the identity are measurable,
and a pair of measurable maps is measurable for this ordinary product.
Set sections are inverse images under those maps, and function sections
are compositions with them. This works at every parameter, for arbitrary
factor measurable spaces and arbitrary measurable codomains.
-/

open Set MeasurableSpace
open scoped MeasureTheory

universe u v w

namespace D11.Ch08.Sections

theorem set_section_left : Specs.D11.Ch08.Sections.set_section_left := by
  intro X Y m n E hE x
  let : MeasurableSpace X := m
  let : MeasurableSpace Y := n
  exact measurable_prodMk_left hE

theorem set_section_right : Specs.D11.Ch08.Sections.set_section_right := by
  intro X Y m n E hE y
  let : MeasurableSpace X := m
  let : MeasurableSpace Y := n
  exact measurable_prodMk_right hE

theorem function_section_left : Specs.D11.Ch08.Sections.function_section_left := by
  intro X Y Z m n p f hf x
  let : MeasurableSpace X := m
  let : MeasurableSpace Y := n
  let : MeasurableSpace Z := p
  exact hf.comp measurable_prodMk_left

theorem function_section_right : Specs.D11.Ch08.Sections.function_section_right := by
  intro X Y Z m n p f hf y
  let : MeasurableSpace X := m
  let : MeasurableSpace Y := n
  let : MeasurableSpace Z := p
  exact hf.comp measurable_prodMk_right

theorem real_sections : Specs.D11.Ch08.Sections.real_sections := by
  intro X Y m n f hf
  exact ⟨function_section_left m n (borel ℝ) f hf,
    function_section_right m n (borel ℝ) f hf⟩

theorem complex_sections : Specs.D11.Ch08.Sections.complex_sections := by
  intro X Y m n f hf
  exact ⟨function_section_left m n (borel ℂ) f hf,
    function_section_right m n (borel ℂ) f hf⟩

theorem extendedReal_sections : Specs.D11.Ch08.Sections.extendedReal_sections := by
  intro X Y m n f hf
  exact ⟨function_section_left m n (borel EReal) f hf,
    function_section_right m n (borel EReal) f hf⟩

end D11.Ch08.Sections
