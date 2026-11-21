import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.HaarAveraging
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.ContinuousMap.Compact

/-! Independent statements for `fa2:p5:haar`, paper.tex:23284–23339.
The measurable structure on each factor is its Borel structure; no assumption
identifies the product measurable structure with the Borel structure of a product.
All measures here are native nonnegative countably additive measures. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
universe u v
namespace ExpandedFA.PartV.Haar

open ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec

/-- Normalization, the source's explicit Radon conditions, and left invariance.
On a compact space this also entails compact inner regularity on every Borel set. -/
def IsNormalizedLeftHaar {G : Type u} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] (μ : Measure G) : Prop :=
  PositiveRadon μ ∧ μ univ = 1 ∧ IsMulLeftInvariant μ

namespace Spec

/-- Interchange for continuous tests on arbitrary compact Hausdorff products.
In particular this applies to (y,x) ↦ f(y*x) in the uniqueness argument. -/
def CompactProductInterchange : Prop :=
  ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : C(X × Y, ℝ)),
    (∫ x, ∫ y, f (x,y) ∂ν ∂μ) = ∫ y, ∫ x, f (x,y) ∂μ ∂ν

/-- The measure is constructed from the already proved positive invariant mean,
with its representation identity on all real continuous functions. -/
def RepresentationOfMean : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (M : C(G, ℝ) →L[ℝ] ℝ), HaarAveraging.Spec.MeanProperties M →
    ∃ μ : Measure G, IsNormalizedLeftHaar μ ∧ IsMulRightInvariant μ ∧
      ∀ f : C(G, ℝ), Integrable f μ ∧ M f = ∫ x, f x ∂μ

/-- Uniqueness among all normalized left-invariant regular Borel measures. -/
def NormalizedHaar : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G],
    ∃! μ : Measure G, IsNormalizedLeftHaar μ

/-- Every such measure is right invariant, inversion invariant, and positive
on every nonempty open set. No commutativity or metrizability is imposed. -/
def AdditionalInvariances : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G), IsNormalizedLeftHaar μ →
      IsMulRightInvariant μ ∧ IsInvInvariant μ ∧
        ∀ U : Set G, IsOpen U → U.Nonempty → 0 < μ U

end Spec
end ExpandedFA.PartV.Haar
