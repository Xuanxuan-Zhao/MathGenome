import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.NullSections
import MathGenome.Internal.RealAnalysis.D11.Ch08.ProductMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch05.MarkovZeroFinite

/-!
Null sections, paper.tex:2672–2683. The product construction expresses the
mass of a measurable set as the nonnegative integral of each section-mass
map, and proves those maps measurable. The zero-integral criterion then
gives each equivalence using the shared ordinary almost-everywhere predicate.
The argument covers empty spaces and zero measures without separate cases.
-/

open Set MeasureTheory

universe u v

namespace D11.Ch08.NullSections

theorem null_sections_left : Specs.D11.Ch08.NullSections.null_sections_left.{u, v} := by
  intro X Y _ _ μ ν hμ hν E hE
  rw [ProductMeasure.section_formula_left μ ν hμ hν E hE]
  exact D11.Ch05.MarkovZeroFinite.zero_integral_iff μ _
    (ProductMeasure.section_integrands_measurable μ ν hμ hν E hE).1

theorem null_sections_right : Specs.D11.Ch08.NullSections.null_sections_right.{u, v} := by
  intro X Y _ _ μ ν hμ hν E hE
  rw [ProductMeasure.section_formula_right μ ν hμ hν E hE]
  exact D11.Ch05.MarkovZeroFinite.zero_integral_iff ν _
    (ProductMeasure.section_integrands_measurable μ ν hμ hν E hE).2

theorem null_sections : Specs.D11.Ch08.NullSections.null_sections.{u, v} := by
  intro X Y _ _ μ ν hμ hν E hE
  exact ⟨null_sections_left μ ν hμ hν E hE, null_sections_right μ ν hμ hν E hE⟩

end D11.Ch08.NullSections
