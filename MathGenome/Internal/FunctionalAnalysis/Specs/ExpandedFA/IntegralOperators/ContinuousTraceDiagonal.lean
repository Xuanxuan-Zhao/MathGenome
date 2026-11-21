import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2Kernel
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.Support

/-! Independent specifications for the general (nonpositive) diagonal trace
identity in `fa2:p2:mercer` and its application to finite Radon measures in
`fa2:p2:classical-fredholm-product`. The kernel operator and trace are the
upstream canonical objects. No Hermitian or positivity assumption is made. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
universe u v
namespace ExpandedFA.IntegralOperators.ContinuousTraceDiagonal.Spec

variable {Q : Type u} [MetricSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]

/-- Apply the existing ordinary product-L² kernel assignment to the continuous
kernel. This is an abbreviation of that assignment, not a new choice of map. -/
abbrev continuousKernelOperator (μ : Measure Q) [IsFiniteMeasure μ]
    (k : C(Q × Q, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  PartV.L2KernelSpec.OperatorValue μ μ (ContinuousMap.toLp 2 (μ.prod μ) ℂ k)

/-- Full-support version stated in the general clause of Mercer. -/
def FullSupportDiagonalTrace : Prop :=
  ∀ (Q : Type u) [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q)
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] (k : C(Q × Q, ℂ)),
    TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (continuousKernelOperator μ k) →
    TraceIdeals.TraceClassDefinitions.Spec.TraceValue (continuousKernelOperator μ k) =
      ∫ x, k (x, x) ∂μ

/-- The finite-Radon application, with no full-support assumption. Compact
metric finite Borel measures are Radon; the stronger formulation below also
makes the zero-measure and empty-space cases explicit through its quantifiers. -/
def DiagonalTrace : Prop :=
  ∀ (Q : Type u) [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q)
    [IsFiniteMeasure μ] (k : C(Q × Q, ℂ)),
    TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (continuousKernelOperator μ k) →
    TraceIdeals.TraceClassDefinitions.Spec.TraceValue (continuousKernelOperator μ k) =
      ∫ x, k (x, x) ∂μ

/-- The concrete support reduction, including the natural restriction unitary.
The trace and diagonal integral agree before and after restriction. -/
def SupportReduction : Prop :=
  ∀ (Q : Type u) [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ],
    let S := μ.support
    let ν : Measure S := μ.comap (Subtype.val : S → Q)
    letI : CompactSpace S := isCompact_iff_compactSpace.mp μ.isClosed_support.isCompact
    μ Sᶜ = 0 ∧ ν.IsOpenPosMeasure ∧
      ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν,
        (∀ f, (U f : S → ℂ) =ᵐ[ν] fun s => f s.val) ∧
        ∀ k : C(Q × Q, ℂ),
          let kS : C(S × S, ℂ) :=
            k.comp ⟨fun p => (p.1.val, p.2.val),
              continuous_subtype_val.prodMap continuous_subtype_val⟩
          U.toContinuousLinearEquiv.toContinuousLinearMap.comp (continuousKernelOperator μ k) =
            (continuousKernelOperator ν kS).comp U.toContinuousLinearEquiv.toContinuousLinearMap ∧
          (TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue
              (continuousKernelOperator μ k) →
            TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue
                (continuousKernelOperator ν kS) ∧
              TraceIdeals.TraceClassDefinitions.Spec.TraceValue (continuousKernelOperator μ k) =
                TraceIdeals.TraceClassDefinitions.Spec.TraceValue (continuousKernelOperator ν kS)) ∧
          (∫ s, kS (s, s) ∂ν) = ∫ x, k (x, x) ∂μ

/-- Abstract trace limit needed by finite averaging projections. A uniformly
bounded strongly convergent family suffices; no positivity or self-adjointness
of the trace-class operator is required. -/
def StrongTraceLimit : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (T : H →L[𝕜] H),
    TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
    ∀ (P : ℕ → H →L[𝕜] H) (M : ℝ),
      (∀ n, ‖P n‖ ≤ M) → (∀ x, Filter.Tendsto (fun n => P n x) Filter.atTop (𝓝 x)) →
      Filter.Tendsto (fun n => TraceIdeals.TraceClassDefinitions.Spec.TraceValue ((P n).comp T))
        Filter.atTop (𝓝 (TraceIdeals.TraceClassDefinitions.Spec.TraceValue T))

/-- Reduction of the arbitrary finite measure conclusion to the full-support
case. This is an implication, not a proof of its antecedent. -/
def SupportTransfer : Prop := FullSupportDiagonalTrace.{u} → DiagonalTrace.{u}

end ExpandedFA.IntegralOperators.ContinuousTraceDiagonal.Spec
