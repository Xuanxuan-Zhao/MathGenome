import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonProductOpenRectangles
import MathGenome.Internal.RealAnalysis.D11.Ch01.GeneratorUniqueness
import MathGenome.Internal.RealAnalysis.D11.Ch08.ProductMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.SigmaFiniteRadonOrdinaryProduct

/-! Outer regularity enlarges a sigma-finite cover to finite-mass opens.
Open rectangles generate the ordinary product sigma-algebra and have equal
masses for the two measures. The finite open covers supply the spanning sets
needed for sigma-finite uniqueness. Trimming then transfers Cc integrals. -/

noncomputable section
namespace D11.Ch18.SigmaFiniteRadonOrdinaryProduct

open Set MeasureTheory
open scoped ENNReal
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z
local instance {Z : Type*} [TopologicalSpace Z] : BorelSpace Z := ⟨rfl⟩

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]

theorem finite_open_cover :
    Specs.D11.Ch18.SigmaFiniteRadonOrdinaryProduct.finite_open_cover.{u} := by
  intro X _ _ _ μ hμ hsf
  let : SigmaFinite μ := hsf
  let : Measure.OuterRegular μ := (outerRegularBorel_iff μ).mp hμ.2.1
  have h (n : ℕ) := (spanningSets μ n).exists_isOpen_lt_add
    (measure_spanningSets_lt_top μ n).ne (ε := 1) one_ne_zero
  choose U hsub hopen hfinite using h
  refine ⟨U, fun n => ⟨hopen n, (hfinite n).trans ?_⟩, ?_⟩
  · exact ENNReal.add_lt_top.mpr ⟨measure_spanningSets_lt_top μ n, ENNReal.one_lt_top⟩
  · exact eq_univ_of_subset (iUnion_mono hsub) (iUnion_spanningSets μ)

/-- The countable finite-mass open cover, packaged for measure uniqueness. -/
def finiteSpanningOpen (μ : Measure X) (hμ : isRadon μ) (hsf : SigmaFinite μ) :
    μ.FiniteSpanningSetsIn {U | IsOpen U} := by
  let h := finite_open_cover X μ hμ hsf
  exact ⟨h.choose, fun n => (h.choose_spec.1 n).1,
    fun n => (h.choose_spec.1 n).2, h.choose_spec.2⟩

theorem ordinary_product_restriction :
    Specs.D11.Ch18.SigmaFiniteRadonOrdinaryProduct.ordinary_product_restriction.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν hsfμ hsfν
  apply Eq.symm
  apply Measure.prod_eq_generateFrom (C := {U : Set X | IsOpen U})
    (D := {V : Set Y | IsOpen V}) rfl rfl isPiSystem_isOpen isPiSystem_isOpen
    (finiteSpanningOpen μ hμ hsfμ) (finiteSpanningOpen ν hν hsfν)
  intro U hU V hV
  rw [trim_measurableSet_eq prod_le_borel_prod (hU.measurableSet.prod hV.measurableSet)]
  exact RadonProductOpenRectangles.open_rectangle X Y μ ν hμ hν U V hU hV

theorem ordinary_product_apply :
    Specs.D11.Ch18.SigmaFiniteRadonOrdinaryProduct.ordinary_product_apply.{u,v} := by
  intro X _ _ _ Y _ _ _ μ ν hμ hν hsfμ hsfν E hE
  rw [← ordinary_product_restriction X Y μ ν hμ hν hsfμ hsfν,
    trim_measurableSet_eq prod_le_borel_prod hE]

theorem cc_fubini : Specs.D11.Ch18.SigmaFiniteRadonOrdinaryProduct.cc_fubini.{u,v} := by
  intro X _ _ _ Y _ _ _ 𝕜 _ μ ν hμ hν hsfμ hsfν f
  let : SigmaFinite μ := hsfμ
  let : SigmaFinite ν := hsfν
  have hm := (RadonProduct.measurable_finite_rectangle X Y 𝕜 μ ν hμ hν f).1
  have hdata := RadonProduct.integral_identity X Y 𝕜 μ ν hμ hν f
  have hi := hdata.2.1
  have ht := ordinary_product_restriction X Y μ ν hμ hν hsfμ hsfν
  have hsm : StronglyMeasurable[(borel X).prod (borel Y)] f := hm.stronglyMeasurable
  have hip : Integrable f (μ.prod ν) := by
    rw [← ht]
    exact hi.trim prod_le_borel_prod hsm
  have he : (∫ p, f p ∂(RadonProduct.radonProduct μ ν)) = ∫ p, f p ∂(μ.prod ν) := by
    rw [← ht]
    exact integral_trim prod_le_borel_prod hsm
  refine ⟨hm, hi, hip, hdata.2.2.2.1, hdata.2.2.2.2.2.1, he, ?_, ?_⟩
  · exact integral_prod f hip
  · exact integral_prod_symm f hip

end D11.Ch18.SigmaFiniteRadonOrdinaryProduct
