import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.MercerExpansion
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.ContinuousTraceDiagonal

/-! Full statement of `fa2:p2:mercer` (paper.tex:11643–11657).
The positive clause uses the shared complete spectral data, including normalized
continuous eigenfunctions and absolute uniform convergence. The independent
diagonal identity is stated for both scalar fields, with trace class as a premise.
All operators and traces are the canonical upstream objects. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace ExpandedFA.IntegralOperators.Mercer.Spec

def PositiveMercer : Prop := MercerExpansion.Spec.Mercer.{u}

def ComplexDiagonalTrace : Prop := ContinuousTraceDiagonal.Spec.FullSupportDiagonalTrace.{u}

def RealDiagonalTrace : Prop :=
  ∀ (Q : Type u) [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q)
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] (k : C(Q × Q, ℝ)),
    TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue
      (MercerExpansion.Spec.operator μ k) →
    TraceIdeals.TraceClassDefinitions.Spec.TraceValue (MercerExpansion.Spec.operator μ k) =
      ∫ x, k (x,x) ∂μ

end ExpandedFA.IntegralOperators.Mercer.Spec
