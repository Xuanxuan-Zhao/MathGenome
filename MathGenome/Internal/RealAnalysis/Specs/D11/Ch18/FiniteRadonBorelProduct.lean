import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonProduct
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Finite-factor stage of paper.tex:5453–5471. All measure domains are
exactly Borel sigma-algebras. In particular the domain on the product is
`borel (X × Y)`, without a second-countability assumption or an identification
with the product measurable space. -/

namespace Specs.D11.Ch18.FiniteRadonBorelProduct
open Set MeasureTheory
open scoped ENNReal
universe u v

local instance {Z : Type*} [TopologicalSpace Z] : MeasurableSpace Z := borel Z

/-- The open-section assertion actually holds without finite total mass. -/
def open_sections_lowerSemicontinuous : Prop :=
  ∀ (X : Type u) [TopologicalSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (ν : Measure Y), RadonPredicates.isRadonValue ν →
    ∀ W : Set (X × Y), IsOpen W →
      LowerSemicontinuous (fun x => ν {y | (x,y) ∈ W})

def borel_sections : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (Y : Type v) [TopologicalSpace Y]
    (E : Set (X × Y)), MeasurableSet[borel (X × Y)] E →
      (∀ x, MeasurableSet[borel Y] {y | (x,y) ∈ E}) ∧
      (∀ y, MeasurableSet[borel X] {x | (x,y) ∈ E})

def finite_product_mass : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    μ univ < ∞ → ν univ < ∞ →
      RadonProduct.radonProduct_value μ ν univ = μ univ * ν univ ∧
      RadonProduct.radonProduct_value μ ν univ < ∞

def open_section_regularity : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    ∀ W : Set (X × Y), IsOpen W →
      LowerSemicontinuous (fun x => ν {y | (x,y) ∈ W}) ∧
      LowerSemicontinuous (fun y => μ {x | (x,y) ∈ W}) ∧
      Measurable (fun x => ν {y | (x,y) ∈ W}) ∧
      Measurable (fun y => μ {x | (x,y) ∈ W})

def borel_section_masses_measurable : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    μ univ < ∞ → ν univ < ∞ →
    ∀ E : Set (X × Y), MeasurableSet[borel (X × Y)] E →
      Measurable (fun x => ν {y | (x,y) ∈ E}) ∧
      Measurable (fun y => μ {x | (x,y) ∈ E})

/-- Open-set identity, including both orders and everywhere Borel section masses. -/
def open_integral_identity : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    μ univ < ∞ → ν univ < ∞ →
    ∀ W : Set (X × Y), IsOpen W →
      LowerSemicontinuous (fun x => ν {y | (x,y) ∈ W}) ∧
      LowerSemicontinuous (fun y => μ {x | (x,y) ∈ W}) ∧
      Measurable (fun x => ν {y | (x,y) ∈ W}) ∧
      Measurable (fun y => μ {x | (x,y) ∈ W}) ∧
      RadonProduct.radonProduct_value μ ν W = ∫⁻ x, ν {y | (x,y) ∈ W} ∂μ ∧
      RadonProduct.radonProduct_value μ ν W = ∫⁻ y, μ {x | (x,y) ∈ W} ∂ν

/-- The full finite-factor conclusion on the product topology's Borel sets. -/
def borel_integral_identity : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (μ : Measure X) (ν : Measure Y),
    RadonPredicates.isRadonValue μ → RadonPredicates.isRadonValue ν →
    μ univ < ∞ → ν univ < ∞ →
    ∀ E : Set (X × Y), MeasurableSet[borel (X × Y)] E →
      Measurable (fun x => ν {y | (x,y) ∈ E}) ∧
      Measurable (fun y => μ {x | (x,y) ∈ E}) ∧
      RadonProduct.radonProduct_value μ ν E = ∫⁻ x, ν {y | (x,y) ∈ E} ∂μ ∧
      RadonProduct.radonProduct_value μ ν E = ∫⁻ y, μ {x | (x,y) ∈ E} ∂ν

end Specs.D11.Ch18.FiniteRadonBorelProduct
