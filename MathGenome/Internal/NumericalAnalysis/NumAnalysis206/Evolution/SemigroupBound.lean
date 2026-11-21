import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Evolution.SemigroupBound
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

namespace NumAnalysis206.Evolution

universe u v

/-- Strong continuity bounds every orbit on a compact time interval; uniform
boundedness then bounds the operator norms. No operator-norm continuity is used. -/
theorem semigroupCompactBound :
    Specs.NumAnalysis206.Evolution.semigroupCompactBound := by
  intro 𝕜 _ X _ _ _ T T₀ _hT₀
  have horbit (x : X) : ∃ B : ℝ, ∀ t ∈ Set.Icc 0 T₀, ‖T t x‖ ≤ B := by
    exact isCompact_Icc.exists_bound_of_continuousOn
      ((T.strong_continuous x).mono (fun _ ht => ht.1))
  have hpoint : ∀ x : X, ∃ B : ℝ, ∀ t : Set.Icc 0 T₀, ‖T t x‖ ≤ B := by
    intro x
    obtain ⟨B, hB⟩ := horbit x
    exact ⟨B, fun t => hB t t.property⟩
  obtain ⟨B, hB⟩ := banach_steinhaus (g := fun t : Set.Icc 0 T₀ => T t) hpoint
  refine ⟨max B 0, le_max_right _ _, fun t ht => ?_⟩
  exact (hB ⟨t, ht⟩).trans (le_max_left _ _)

end NumAnalysis206.Evolution
