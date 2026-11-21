import MathGenome.Internal.LinearPDE.P201Specs.Integral.ContinuousKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.ContinuousKernel

/-!
The source's compact integral operator is the square-domain, complex-scalar
specialization of the pinned compact-Hausdorff continuous-kernel theorem.
Its hypotheses require only a finite Borel measure, so the source's full-support
case follows directly, including the empty compact space.
-/

universe u
namespace P201.Integral.ContinuousKernel

/-- The actual bounded complex-linear integral operator. -/
noncomputable def kernelOperator : Spec.OperatorType.{u} :=
  Spec.OperatorValue

/-- Integrability, output continuity, integral formula, operator norm bound,
and compactness of the same canonical operator. -/
theorem continuous_kernel_theorem : Spec.KernelTheorem.{u} := by
  intro K _ _ _ _ _ μ _ k
  obtain ⟨hformula, hnorm, hcompact, himages⟩ :=
    ExpandedFA.PartV.ContinuousKernel.canonical_operator_properties ℂ K K μ k
  refine ⟨hformula, ?_, hnorm, hcompact, himages⟩
  intro f
  exact ExpandedFA.PartV.ContinuousKernel.continuous_kernel_output_continuous ℂ K K μ k f

/-- The theorem includes the empty compact-space boundary. -/
theorem zero_cases : Spec.ZeroCases.{u} := by
  intro K _ _ _ _ _ μ _ k hz
  apply ExpandedFA.PartV.ContinuousKernel.continuous_kernel_zero_cases ℂ K K μ k
    (Spec.OperatorValue μ k)
    (ExpandedFA.PartV.ContinuousKernel.Spec.KernelOperatorValue_apply μ k)
  rcases hz with hμ | hK
  · exact Or.inl hμ
  · exact Or.inr (Or.inl hK)

end P201.Integral.ContinuousKernel
