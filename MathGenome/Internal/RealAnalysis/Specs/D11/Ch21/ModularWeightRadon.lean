import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.ModularProperties
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.DensityMeasureDomains

/-! The weighted-regularity stage of paper.tex:5972–5987. The weight is the
real, hence finite, function Δ(x⁻¹), in the manuscript's right-set convention.
The density construction is on exactly the Borel sigma-algebra. The right Haar
conclusion includes nonzero mass, compact finiteness, outer regularity on all
Borel sets (also those of infinite mass), and compact-inner regularity on opens.
There are no countability or sigma-finiteness hypotheses. -/
namespace Specs.D11.Ch21.ModularWeightRadon
open MeasureTheory
universe u
noncomputable section
local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G

def weight_type :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G],
    @Measure G (borel G) → G → ℝ

def weight_value : weight_type.{u} := fun μ x =>
  ModularFunction.modularFunction_value μ x⁻¹

def weightedMeasure_type :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G],
    @Measure G (borel G) → @Measure G (borel G)

def weightedMeasure_value : weightedMeasure_type.{u} := fun μ =>
  Specs.D11.Ch05.DensityMeasureDomains.densityMeasure_value μ
    (fun x => ENNReal.ofReal (weight_value μ x))

def weight_properties : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ →
      Continuous (weight_value μ) ∧ ∀ x, 0 < weight_value μ x

def weightedMeasure_apply : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (μ : @Measure G (borel G)) (E : Set G), MeasurableSet[borel G] E →
    weightedMeasure_value μ E =
      Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value
        (Specs.D11.Ch01.ExhaustionRestriction.restrictOnSpace_value μ E)
        (fun x => ENNReal.ofReal (weight_value μ x))

def weightedMeasure_rightHaar : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → HaarDefinition.rightHaarValue (weightedMeasure_value μ)

end
end Specs.D11.Ch21.ModularWeightRadon
