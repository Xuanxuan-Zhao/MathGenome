import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ContinuousKernel

/-!
The operator clause of `paper.tex:4295–4303`, with its integrability and
continuity justification in `4319–4340`. We state the stronger result for all
finite positive Borel measures; full support is not needed. The spaces retain
their given compact Hausdorff topology and the canonical supremum norms.
There is no regularity, metrizability, or nonemptiness hypothesis.
-/

open MeasureTheory

universe u
namespace P201.Integral.ContinuousKernel.Spec

/-- The complex bounded operator on the source's continuous-function space. -/
def OperatorType :=
  ∀ {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ],
    C(K × K, ℂ) → (C(K, ℂ) →L[ℂ] C(K, ℂ))

/-- Reuse the pinned integral construction, rather than choosing another
operator from an existence assertion. -/
noncomputable def OperatorValue : OperatorType.{u} :=
  fun μ _ k => ExpandedFA.PartV.ContinuousKernel.Spec.KernelOperatorValue μ k

/-- All conclusions concern the same canonical operator. In a finite measure,
`μ.real Set.univ` is the real number μ(K). Compactness is in the supremum norm.
The last clause also states relative compactness of every bounded image. -/
def KernelTheorem : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (k : C(K × K, ℂ)),
    (∀ (f : C(K, ℂ)) (x : K),
      Integrable (fun y => k (x, y) * f y) μ ∧
      OperatorValue μ k f x = ∫ y, k (x, y) * f y ∂μ) ∧
    (∀ f : C(K, ℂ), Continuous (fun x => ∫ y, k (x, y) * f y ∂μ)) ∧
    ‖OperatorValue μ k‖ ≤ μ.real Set.univ * ‖k‖ ∧
    IsCompactOperator (OperatorValue μ k) ∧
    ∀ S : Set C(K, ℂ), Bornology.IsBounded S →
      IsCompact (closure (OperatorValue μ k '' S))

/-- The allowed empty-space boundary, and also the zero measure, give zero. -/
def ZeroCases : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (k : C(K × K, ℂ)),
    (μ = 0 ∨ IsEmpty K) → OperatorValue μ k = 0

end P201.Integral.ContinuousKernel.Spec
