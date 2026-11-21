import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ContinuousKernel

/-!
Independent statements for the continuous-kernel clause of
`paper.tex:10556–10577`, `fa2:p2:kernel-compactness`.

We specialize the shared continuous-kernel construction to X = Y = Q.
The slightly stronger finite positive Borel measure hypotheses include every
finite positive regular measure in the source. Q may be empty and the measure
may vanish; no metric on Q is assumed. The continuous-map and operator norms
are the canonical supremum and operator norms.
-/

open MeasureTheory

universe u v
namespace ExpandedFA.IntegralOperators.ContinuousKernelCompactness.Spec

open ExpandedFA.PartV.ContinuousKernel.Spec

/-- Properties of the existing canonical operator, with identical domain and
codomain. In particular, compactness is in the norm topology. -/
def CanonicalProperties : Prop :=
  ∀ (𝕜 : Type u) (Q : Type v) [RCLike 𝕜] [TopologicalSpace Q]
    [CompactSpace Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜)),
    (∀ (f : C(Q, 𝕜)) (x : Q),
      Integrable (fun y => k (x, y) * f y) μ ∧
      KernelOperatorValue μ k f x = ∫ y, k (x, y) * f y ∂μ) ∧
    ‖KernelOperatorValue μ k‖ ≤ μ.real Set.univ * ‖k‖ ∧
    IsCompactOperator (KernelOperatorValue μ k) ∧
    ∀ S : Set C(Q, 𝕜), Bornology.IsBounded S →
      IsCompact (closure (KernelOperatorValue μ k '' S))

/-- The integral defines a unique bounded operator, with the stated sharp
upper bound and compactness. No second operator is defined here. -/
def ContinuousKernelTheorem : Prop :=
  ∀ (𝕜 : Type u) (Q : Type v) [RCLike 𝕜] [TopologicalSpace Q]
    [CompactSpace Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜)),
    ∃! T : C(Q, 𝕜) →L[𝕜] C(Q, 𝕜),
      (∀ f x, T f x = ∫ y, k (x, y) * f y ∂μ) ∧
      ‖T‖ ≤ μ.real Set.univ * ‖k‖ ∧ IsCompactOperator T ∧
      ∀ S : Set C(Q, 𝕜), Bornology.IsBounded S →
        IsCompact (closure (T '' S))

/-- Both degenerate cases yield the zero canonical operator. -/
def ZeroCases : Prop :=
  ∀ (𝕜 : Type u) (Q : Type v) [RCLike 𝕜] [TopologicalSpace Q]
    [CompactSpace Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, 𝕜)),
    (μ = 0 ∨ IsEmpty Q) → KernelOperatorValue μ k = 0

end ExpandedFA.IntegralOperators.ContinuousKernelCompactness.Spec
