import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.Fubini
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
Fubini for absolutely integrable real or complex functions on an ordinary
product (paper.tex:2639–2673). The shared scalar bridge retains measurability
on the original sigma-algebra. Every section of a measurable function is
measurable, so its source integrability is equivalent to native integrability.
Consequently the explicitly zero-extended section integral agrees pointwise
with the native integral: on integrable sections this is the shared definition;
on other sections `integral_undef` gives exactly the prescribed zero.

Mathlib's strongly measurable parameter-integral theorem therefore proves
actual measurability of these particular maps, including on incomplete factors.
Its integrable-section and Fubini theorems give the remaining conclusions after
transport through the shared scalar integrability and a.e. bridges.
-/

open MeasureTheory
open Specs.D11.Ch08.ProductMeasure (productMeasure_value)
open Specs.D11.Ch06.ScalarIntegral (scalarIntegrable_value scalarIntegral_value)

universe u v
noncomputable section

namespace D11.Ch08.Fubini

def sectionIntegralLeft : Specs.D11.Ch08.Fubini.sectionIntegralLeft_type.{u, v} :=
  Specs.D11.Ch08.Fubini.sectionIntegralLeft_value

def sectionIntegralRight : Specs.D11.Ch08.Fubini.sectionIntegralRight_type.{u, v} :=
  Specs.D11.Ch08.Fubini.sectionIntegralRight_value

variable {X : Type u} {Y : Type v} {𝕜 : Type}
  [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- The source's explicit zero convention coincides pointwise with the native
integral, because the sections are actually measurable. -/
theorem sectionIntegralLeft_eq_integral (ν : Measure Y) (f : X × Y → 𝕜)
    (hf : Measurable f) :
    sectionIntegralLeft ν f = fun x => ∫ y, f (x, y) ∂ν := by
  classical
  funext x
  have hm : Measurable (fun y => f (x, y)) := hf.comp measurable_prodMk_left
  have hi := D11.Ch06.ScalarIntegral.native_integrable_iff ν (fun y => f (x, y)) hm
  change (if h : scalarIntegrable_value ν (fun y => f (x, y)) then
    scalarIntegral_value ν (fun y => f (x, y)) h else 0) = ∫ y, f (x, y) ∂ν
  split_ifs with h
  · rfl
  · exact (integral_undef (fun hnat => h (hi.mpr hnat))).symm

theorem sectionIntegralRight_eq_integral (μ : Measure X) (f : X × Y → 𝕜)
    (hf : Measurable f) :
    sectionIntegralRight μ f = fun y => ∫ x, f (x, y) ∂μ := by
  classical
  funext y
  have hm : Measurable (fun x => f (x, y)) := hf.comp measurable_prodMk_right
  have hi := D11.Ch06.ScalarIntegral.native_integrable_iff μ (fun x => f (x, y)) hm
  change (if h : scalarIntegrable_value μ (fun x => f (x, y)) then
    scalarIntegral_value μ (fun x => f (x, y)) h else 0) = ∫ x, f (x, y) ∂μ
  split_ifs with h
  · rfl
  · exact (integral_undef (fun hnat => h (hi.mpr hnat))).symm

theorem fubini : Specs.D11.Ch08.Fubini.fubini.{u, v} := by
  intro X Y 𝕜 _ _ _ _ _ μ ν hμ hν f hf
  let : SigmaFinite μ := hμ
  let : SigmaFinite ν := hν
  have hfi := (D11.Ch06.ScalarIntegral.scalarIntegrable_iff (productMeasure_value μ ν) f).mp hf
  have hleft := sectionIntegralLeft_eq_integral ν f hfi.1
  have hright := sectionIntegralRight_eq_integral μ f hfi.1
  have hml : Measurable (sectionIntegralLeft ν f) := by
    rw [hleft]
    exact hfi.1.stronglyMeasurable.integral_prod_right'.measurable
  have hmr : Measurable (sectionIntegralRight μ f) := by
    rw [hright]
    exact hfi.1.stronglyMeasurable.integral_prod_left'.measurable
  have hil : scalarIntegrable_value μ (sectionIntegralLeft ν f) := by
    apply (D11.Ch06.ScalarIntegral.scalarIntegrable_iff μ _).mpr
    refine ⟨hml, ?_⟩
    rw [hleft]
    exact hfi.2.integral_prod_left
  have hir : scalarIntegrable_value ν (sectionIntegralRight μ f) := by
    apply (D11.Ch06.ScalarIntegral.scalarIntegrable_iff ν _).mpr
    refine ⟨hmr, ?_⟩
    rw [hright]
    exact hfi.2.integral_prod_right
  refine ⟨?_, ?_, hml, hmr, hil, hir, ?_, ?_⟩
  · apply (D11.Ch04.AeCommonException.almostEverywhere_iff_native μ _).mpr
    filter_upwards [hfi.2.prod_right_ae] with x hx
    exact (D11.Ch06.ScalarIntegral.scalarIntegrable_iff ν _).mpr
      ⟨hfi.1.comp measurable_prodMk_left, hx⟩
  · apply (D11.Ch04.AeCommonException.almostEverywhere_iff_native ν _).mpr
    filter_upwards [hfi.2.prod_left_ae] with y hy
    exact (D11.Ch06.ScalarIntegral.scalarIntegrable_iff μ _).mpr
      ⟨hfi.1.comp measurable_prodMk_right, hy⟩
  · change (∫ z, f z ∂μ.prod ν) = ∫ x, sectionIntegralLeft ν f x ∂μ
    rw [hleft]
    exact integral_prod f hfi.2
  · change (∫ x, sectionIntegralLeft ν f x ∂μ) =
      ∫ y, sectionIntegralRight μ f y ∂ν
    rw [hleft, hright]
    exact (integral_prod f hfi.2).symm.trans (integral_prod_symm f hfi.2)

end D11.Ch08.Fubini
