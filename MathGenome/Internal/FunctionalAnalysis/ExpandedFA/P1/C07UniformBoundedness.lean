import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C07UniformBoundedness
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Uniform boundedness

Theorem `fa2:p1:c07:uniform-boundedness`. Mathlib's Banach–Steinhaus theorem
applies to arbitrary families of continuous linear maps, with completeness
only in the domain. Replacing its real bound by its maximum with zero gives
the nonnegative bound even when the family is empty. The remaining statements
verify the extended nonnegative supremum formulation and the boundary cases.
-/

namespace ExpandedFA.P1.C07UniformBoundedness

open scoped ENNReal

theorem uniform_boundedness : Spec.UniformBoundedness := by
  intro 𝕜 E F I _ _ _ _ _ _ T h
  obtain ⟨C, hC⟩ := banach_steinhaus h
  exact ⟨max C 0, le_max_right _ _, fun i => (hC i).trans (le_max_left _ _)⟩

theorem operator_norm_supremum_finite_iff :
    Spec.FiniteSupremumCriterion := by
  intro 𝕜 E F I _ _ _ _ _ T
  rw [ENNReal.iSup_coe_lt_top]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨(C : ℝ), C.coe_nonneg, fun i => hC (Set.mem_range_self i)⟩
  · rintro ⟨C, hC, hbound⟩
    refine ⟨⟨C, hC⟩, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hbound i

theorem uniform_boundedness_supremum :
    Spec.UniformBoundednessSupremum := by
  intro 𝕜 E F I _ _ _ _ _ _ T h
  exact banach_steinhaus_iSup_nnnorm h

theorem empty_family_suprema : Spec.EmptyFamilySuprema := by
  intro 𝕜 E F I _ _ _ _ _ _ T
  simp

theorem zero_domain_operator_norm_supremum :
    Spec.ZeroDomainSupremum := by
  intro 𝕜 E F I _ _ _ _ _ _ T
  simp [ContinuousLinearMap.opNNNorm_subsingleton]

end ExpandedFA.P1.C07UniformBoundedness
