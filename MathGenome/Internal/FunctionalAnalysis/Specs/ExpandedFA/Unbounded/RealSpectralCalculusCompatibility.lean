import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealSpectralProductAndSumDomains
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SpectralProductAndSumDomains

/-! Compatibility on the same real Hilbert space. No spectral existence
certificate is assumed; the old calculus is an arbitrary already given calculus.
The final conjunctions retain the complex statements verbatim. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace ENNReal NNReal
namespace ExpandedFA.Unbounded.RealSpectralCalculusCompatibility
open ExpandedFA.SpectralMeasure
universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Canonical conversion, including the values on nonmeasurable sets. -/
def toGeneralPVMValue (E : RealNonnegativeSpectralCalculus.ProjectionValuedMeasure H) :
    RealProjectionValuedMeasure ℝ≥0 H where
  toFun := E.toFun
  univ := E.univ
  selfAdjoint := fun B hB => (E.selfAdjoint B hB).isSymmetric
  inter := E.inter
  countablyAdditive := E.iUnion

def toHalfLinePVMValue (E : RealProjectionValuedMeasure ℝ≥0 H) :
    RealNonnegativeSpectralCalculus.ProjectionValuedMeasure H where
  toFun := E.toFun
  univ := E.univ
  selfAdjoint := fun B hB => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (E.selfAdjoint B hB)
  inter := E.inter
  iUnion := E.countablyAdditive

namespace Spec

def ToGeneralType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H],
  RealNonnegativeSpectralCalculus.ProjectionValuedMeasure H → RealProjectionValuedMeasure ℝ≥0 H

def ToHalfLineType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H],
  RealProjectionValuedMeasure ℝ≥0 H → RealNonnegativeSpectralCalculus.ProjectionValuedMeasure H

def ToGeneralValue : ToGeneralType.{v} := @toGeneralPVMValue

def ToHalfLineValue : ToHalfLineType.{v} := @toHalfLinePVMValue

def PVMEquivalence : Prop := ∀ (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H],
  ∃ e : RealNonnegativeSpectralCalculus.ProjectionValuedMeasure H ≃ RealProjectionValuedMeasure ℝ≥0 H,
    (∀ E, e E = toGeneralPVMValue E) ∧
    (∀ E, e.symm E = toHalfLinePVMValue E) ∧
    (∀ E B, (e E) B = E B) ∧ (∀ E B, (e.symm E) B = E B)

/-- Exact equality of measures, bounded operators, truncations and maximal
operators. The operator equality includes its domain and every value. -/
def CompatibilityFor (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (D : RealBoundedRealization (toGeneralPVMValue C.E)) : Prop :=
  (∀ x, D.scalar x = C.measure x) ∧
  (∀ x y, D.coefficient x y = C.coefficient x y) ∧
  (∀ f : RealBoundedFunction ℝ≥0, D.integral f = C.bounded f) ∧
  (∀ a : SimpleFunc ℝ≥0 ℝ,
    C.bounded a = realSimpleSpectralIntegral (toGeneralPVMValue C.E) a) ∧
  (∀ (f : RealBoundedFunction ℝ≥0) (a : ℕ → SimpleFunc ℝ≥0 ℝ),
    TendstoUniformly (fun n => (a n : ℝ≥0 → ℝ)) f atTop →
    Tendsto (fun n => C.bounded (a n)) atTop (𝓝 (C.bounded f))) ∧
  (∀ (f : ℝ≥0 → ℝ) (hf : Measurable f) (n : ℕ),
    (RealMeasurableSpectralCalculus.truncation f hf n : ℝ≥0 → ℝ) = RealNonnegativeSpectralCalculus.truncation f n ∧
    RealMeasurableSpectralCalculus.truncatedOperator D f hf n = C.bounded (RealNonnegativeSpectralCalculus.truncation f n)) ∧
  (∀ (f : ℝ≥0 → ℝ) (x : H),
    RealMeasurableSpectralCalculus.squareMoment D f x < ∞ ↔ RealNonnegativeSpectralCalculus.SquareIntegrable (C.measure x) f) ∧
  (∀ (f : ℝ≥0 → ℝ) (hf : Measurable f),
    RealMeasurableSpectralCalculus.measurableIntegralValue D f hf = C.integral f)

def CalculusCompatibility : Prop := ∀ (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (C : RealNonnegativeSpectralCalculus.Calculus (H := H)),
  ∃ D : RealBoundedRealization (toGeneralPVMValue C.E), CompatibilityFor C D

/-- The general closure laws specialized to the old actual integral. -/
def HalfLineDomainLaws : Prop := ∀ (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (C : RealNonnegativeSpectralCalculus.Calculus (H := H))
    (f g : ℝ≥0 → ℝ), Measurable f → Measurable g →
  let A := C.integral f
  let B := C.integral g
  let P := OperatorDomainsSpec.productValue A B
  P.domain = B.domain ⊓ (C.integral (f * g)).domain ∧
  P ≤ C.integral (f * g) ∧ P.IsClosable ∧ P.closure = C.integral (f * g) ∧
  (A + B).IsClosable ∧ (A + B).closure = C.integral (f + g)

/-- Complete complex PVM/bounded-calculus conclusions, with original types. -/
def ComplexBoundedTheorem : Prop := ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  SpectralMeasure.Spec.SourceRealization (S := S) (H := H) ∧
  SpectralMeasure.Spec.Empty (S := S) (H := H) ∧
  SpectralMeasure.Spec.ProjectionLaws (S := S) (H := H) ∧
  SpectralMeasure.Spec.CoefficientProjection (S := S) (H := H) ∧
  SpectralMeasure.Spec.Orthogonality (S := S) (H := H) ∧
  SpectralMeasure.Spec.ScalarMeasures (S := S) (H := H) ∧
  SpectralMeasure.Spec.FunctionalCalculus (S := S) (H := H)

def FullScalarBoundedTheorem : Prop :=
  ComplexBoundedTheorem.{u,v} ∧
  RealDefinitions.Spec.ProjectionProperties.{u,v} ∧
  RealDefinitions.Spec.OrderedAdditivityEquivalence.{u,v} ∧
  RealDefinitions.Spec.BoundedRealizationExists.{u,v}

def FullScalarUnboundedTheorem : Prop :=
  (MeasurableSpectralCalculus.Spec.MeasurableCalculusInterface.{u,v} ∧
   MeasurableSpectralCalculus.Spec.MeasurableCalculusExistsInterface.{u,v} ∧
   SpectralProductAndSumDomains.Spec.ProductRule.{u,v} ∧
   SpectralProductAndSumDomains.Spec.ProductClosure.{u,v} ∧
   SpectralProductAndSumDomains.Spec.SumClosure.{u,v} ∧
   SpectralProductAndSumDomains.Spec.StrictDomainExample) ∧
  (RealMeasurableSpectralCalculus.Spec.EveryRealization.{u,v} ∧ RealMeasurableSpectralCalculus.Spec.RealizationExists.{u,v} ∧
   RealSpectralProductAndSumDomains.Spec.CompleteTheorem.{u,v})
end Spec
end ExpandedFA.Unbounded.RealSpectralCalculusCompatibility
