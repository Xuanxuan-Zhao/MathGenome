import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch08.SectionIntegralsOneSided

/-!
The sigma-finite product measure of paper.tex:2580–2616.

The shared native product measurable space is the ordinary rectangle-generated
sigma-algebra. Mathlib constructs `Measure.prod` by integrating the measures
obtained from the fixed-coordinate inclusions. `prod_apply` gives the left
section formula, `prod_prod` the rectangle values, and `prod.instSigmaFinite`
the finite-rectangle exhaustion. `prod_eq` proves uniqueness from rectangle
values for sigma-finite factors, without assuming that the competing measure
is sigma-finite. `prod_apply_symm` gives the reversed section formula.

Both section-mass maps are measurable by the upstream one-sided theorem,
applied in each order. The upstream proved integral bridge then converts
the library formulas to the source's nonnegative integral. No completion,
finite-total-mass, or nonemptiness hypothesis is added.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v
noncomputable section

namespace D11.Ch08.ProductMeasure

abbrev productMeasure {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) : Measure (X × Y) := μ.prod ν

theorem rectangle_value : Specs.D11.Ch08.ProductMeasure.rectangle_value.{u, v} := by
  intro X Y _ _ μ ν _hμ hν A B _hA _hB
  let : SigmaFinite ν := hν
  exact Measure.prod_prod A B

theorem uniqueness : Specs.D11.Ch08.ProductMeasure.uniqueness.{u, v} := by
  intro X Y _ _ μ ν hμ hν η hη
  let : SigmaFinite μ := hμ
  let : SigmaFinite ν := hν
  exact (Measure.prod_eq hη).symm

theorem sigma_finite : Specs.D11.Ch08.ProductMeasure.sigma_finite.{u, v} := by
  intro X Y _ _ μ ν hμ hν
  let : SigmaFinite μ := hμ
  let : SigmaFinite ν := hν
  change SigmaFinite (μ.prod ν)
  infer_instance

theorem section_integrands_measurable :
    Specs.D11.Ch08.ProductMeasure.section_integrands_measurable.{u, v} := by
  intro X Y _ _ μ ν hμ hν E hE
  refine ⟨SectionIntegralsOneSided.section_measure_measurable ν hν E hE, ?_⟩
  exact SectionIntegralsOneSided.section_measure_measurable μ hμ
    (Prod.swap ⁻¹' E) (measurable_swap hE)

theorem section_formula_left : Specs.D11.Ch08.ProductMeasure.section_formula_left.{u, v} := by
  intro X Y _ _ μ ν hμ hν E hE
  let : SigmaFinite ν := hν
  have hm := (section_integrands_measurable μ ν hμ hν E hE).1
  rw [D11.Ch05.NonnegativeIntegral.eq_lintegral μ _ hm]
  exact Measure.prod_apply hE

theorem section_formula_right : Specs.D11.Ch08.ProductMeasure.section_formula_right.{u, v} := by
  intro X Y _ _ μ ν hμ hν E hE
  let : SigmaFinite μ := hμ
  let : SigmaFinite ν := hν
  have hm := (section_integrands_measurable μ ν hμ hν E hE).2
  rw [D11.Ch05.NonnegativeIntegral.eq_lintegral ν _ hm]
  exact Measure.prod_apply_symm hE

theorem exists_unique : Specs.D11.Ch08.ProductMeasure.exists_unique.{u, v} := by
  intro X Y _ _ μ ν hμ hν
  exact ⟨productMeasure μ ν, rectangle_value μ ν hμ hν,
    fun η hη => uniqueness μ ν hμ hν η hη⟩

theorem product_measure : Specs.D11.Ch08.ProductMeasure.product_measure.{u, v} := by
  intro X Y _ _ μ ν hμ hν
  refine ⟨productMeasure μ ν, rectangle_value μ ν hμ hν,
    sigma_finite μ ν hμ hν, ?_, fun θ hθ => uniqueness μ ν hμ hν θ hθ⟩
  intro E hE
  obtain ⟨hmleft, hmright⟩ := section_integrands_measurable μ ν hμ hν E hE
  exact ⟨hmleft, hmright, section_formula_left μ ν hμ hν E hE,
    section_formula_right μ ν hμ hν E hE⟩

end D11.Ch08.ProductMeasure
