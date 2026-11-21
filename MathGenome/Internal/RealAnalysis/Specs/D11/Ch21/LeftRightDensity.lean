import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.ModularWeightRadon
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarInversion

/-!
The conclusion of paper.tex:5972–5990, with Δ defined by μ(Ea) = Δ(a) μ(E).
The group is arbitrary Hausdorff locally compact; all measures have exactly
its Borel domain. The density is real-valued, everywhere positive and finite.
The equality specifies the inversion pushforward itself, with scalar one.
-/
namespace Specs.D11.Ch21.LeftRightDensity
open MeasureTheory
universe u
noncomputable section
local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G

def inversion_eq_weightedMeasure : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ →
      HaarInversion.inversionMeasureValue μ = ModularWeightRadon.weightedMeasure_value μ

/-- Exact equality on every Borel set, in the shared nonnegative integral. -/
def density_formula : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → ∀ E : Set G, MeasurableSet[borel G] E →
      HaarInversion.inversionMeasureValue μ E =
        Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value
          (Specs.D11.Ch01.ExhaustionRestriction.restrictOnSpace_value μ E)
          (fun x => ENNReal.ofReal (ModularFunction.modularFunction_value μ x⁻¹))

def inversion_null_iff : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → ∀ E : Set G, MeasurableSet[borel G] E →
      (HaarInversion.inversionMeasureValue μ E = 0 ↔ μ E = 0)

/-- Includes every positive normalization of the inversion pushforward. -/
def rightHaar_null_iff : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ ν : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → HaarDefinition.rightHaarValue ν →
      ∀ E : Set G, MeasurableSet[borel G] E → (ν E = 0 ↔ μ E = 0)

/-- Explicitly records all finite positive normalizations, without choosing one. -/
def normalized_inversion_null_iff : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    HaarDefinition.leftHaarValue μ → ∀ c : ℝ, 0 < c →
      ∀ E : Set G, MeasurableSet[borel G] E →
        ((ENNReal.ofReal c • HaarInversion.inversionMeasureValue μ) E = 0 ↔ μ E = 0)
end
end Specs.D11.Ch21.LeftRightDensity
