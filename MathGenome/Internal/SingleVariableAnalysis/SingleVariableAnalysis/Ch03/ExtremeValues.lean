import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.ExtremeValues
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.CompactInterval
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.ClosedPreimage
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SupInf
import Mathlib.Topology.Order.Compact

/-!
# Continuous images, extreme values, and scalar bounds

K03.03.extreme_values (paper.tex:539–548). The upstream epsilon–delta
continuity predicate gives ContinuousOn without any extension hypothesis.
Mathlib's compact-image and real extreme-value theorems then apply with
exactly the stated hypotheses. Scalar image bounds use the upstream
real and complex compactness characterizations. The elementary examples
show why neither attainment nor boundedness follows from continuity alone.
-/
namespace SingleVariableAnalysis

universe u v

/-- Unpunctured relative continuity is continuity on the given set. -/
theorem relativeContinuous_continuousOn
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (hf : RelativeContinuous f E) :
    ContinuousOn f E :=
  fun a ha => (relativeContinuousAt_within_iff f E a).mp (hf a ha)

/-- Compact images require continuity only on the compact set itself. -/
theorem compact_relativeContinuous_image
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (hE : IsCompact E)
    (hf : RelativeContinuous f E) : IsCompact (f '' E) :=
  hE.image_of_continuousOn (relativeContinuous_continuousOn f E hf)

theorem real_compact_maximum
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X)
    (hE : IsCompact E) (hne : E.Nonempty) (hf : RelativeContinuous f E) :
    ∃ a ∈ E, ∀ x ∈ E, f x ≤ f a :=
  hE.exists_isMaxOn hne (relativeContinuous_continuousOn f E hf)

theorem real_compact_minimum
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X)
    (hE : IsCompact E) (hne : E.Nonempty) (hf : RelativeContinuous f E) :
    ∃ a ∈ E, ∀ x ∈ E, f a ≤ f x :=
  hE.exists_isMinOn hne (relativeContinuous_continuousOn f E hf)

/-- Empty E is allowed: enlarging the image bound also makes it nonnegative. -/
theorem real_compact_bounded
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X)
    (hE : IsCompact E) (hf : RelativeContinuous f E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ E, |f x| ≤ M := by
  obtain ⟨_, M, hM⟩ := (real_compact_iff_closed_bounded (f '' E)).mp
    (compact_relativeContinuous_image f E hE hf)
  exact ⟨max M 0, le_max_right _ _, fun x hx =>
    (hM (f x) (Set.mem_image_of_mem f hx)).trans (le_max_left _ _)⟩

theorem complex_compact_bounded
    {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X)
    (hE : IsCompact E) (hf : RelativeContinuous f E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ E, ‖f x‖ ≤ M := by
  obtain ⟨_, M, hM⟩ := (complex_compact_iff_closed_bounded (f '' E)).mp
    (compact_relativeContinuous_image f E hE hf)
  exact ⟨max M 0, le_max_right _ _, fun x hx =>
    (hM (f x) (Set.mem_image_of_mem f hx)).trans (le_max_left _ _)⟩

/-- The identity is continuous on (0,1), with infimum 0 and supremum 1. -/
theorem open_unit_identity_bounds :
    RelativeContinuous (fun x : ℝ => x) (Set.Ioo 0 1) ∧
      IsGLB ((fun x : ℝ => x) '' Set.Ioo 0 1) 0 ∧
      IsLUB ((fun x : ℝ => x) '' Set.Ioo 0 1) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro a _ ε hε
    exact ⟨ε, hε, fun x _ hx => hx⟩
  · simpa only [Set.image_id'] using (isGLB_Ioo (by norm_num : (0 : ℝ) < 1))
  · simpa only [Set.image_id'] using (isLUB_Ioo (by norm_num : (0 : ℝ) < 1))

/-- Midpoints toward 1 and 0 respectively defeat any proposed extrema. -/
theorem open_unit_identity_no_extrema :
    (¬ ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ≤ a) ∧
    (¬ ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∀ x ∈ Set.Ioo (0 : ℝ) 1, a ≤ x) := by
  constructor
  · rintro ⟨a, ha, hmax⟩
    have hmid : (a + 1) / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [ha.1],
      by linarith [ha.2]⟩
    have := hmax _ hmid
    linarith [ha.2]
  · rintro ⟨a, ha, hmin⟩
    have hmid : a / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [ha.1],
      by linarith [ha.1, ha.2]⟩
    have := hmin _ hmid
    linarith [ha.1]

theorem real_identity_unbounded :
    RelativeContinuous (fun x : ℝ => x) Set.univ ∧
      ¬ (∃ M : ℝ, ∀ x : ℝ, |(fun y : ℝ => y) x| ≤ M) := by
  constructor
  · exact (relativeContinuous_univ_iff _).mpr continuous_id
  · rintro ⟨M, hM⟩
    have h := hM (|M| + 1)
    rw [abs_of_pos (by positivity : 0 < |M| + 1)] at h
    linarith [le_abs_self M]

end SingleVariableAnalysis
