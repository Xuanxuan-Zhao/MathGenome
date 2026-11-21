import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.OneSided
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.Jordan
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.MonotoneLimits

/-! Finite one-sided limits and countability of relative discontinuities for
real BV functions, K03.15.one_sided. The proof uses Jordan decomposition on the
original closed interval. The finite endpoint values of its monotone components
bound the one-sided images, including at the available endpoint approaches.
-/
namespace SingleVariableAnalysis.BV

open Set Filter
open scoped Topology

/-- Every point strictly above the left endpoint has a genuine left approach
inside the closed interval, even when it is the right endpoint. -/
theorem closedInterval_left_accumulation {a b c : ℝ} (hc : c ∈ Ioc a b) :
    LeftAccumulation (Icc a b) c := by
  change ∀ δ : ℝ, 0 < δ → ∃ x ∈ Icc a b, c - δ < x ∧ x < c
  intro δ hδ
  obtain ⟨x, hx₁, hx₂⟩ := exists_between (max_lt hc.1 (sub_lt_self c hδ))
  exact ⟨x, ⟨(le_max_left _ _).trans hx₁.le, hx₂.le.trans hc.2⟩,
    (le_max_right _ _).trans_lt hx₁, hx₂⟩

/-- The right approach includes the left endpoint and excludes the right one. -/
theorem closedInterval_right_accumulation {a b c : ℝ} (hc : c ∈ Ico a b) :
    RightAccumulation (Icc a b) c := by
  change ∀ δ : ℝ, 0 < δ → ∃ x ∈ Icc a b, c < x ∧ x < c + δ
  intro δ hδ
  obtain ⟨x, hx₁, hx₂⟩ := exists_between (lt_min hc.2 (lt_add_of_pos_right c hδ))
  exact ⟨x, ⟨hc.1.trans hx₁.le, hx₂.le.trans (min_le_left _ _)⟩,
    hx₁, hx₂.trans_le (min_le_right _ _)⟩

/-- Nonemptiness and the finite value at c justify the real supremum. -/
theorem monotoneOn_closedInterval_left_limit {g : ℝ → ℝ} {a b c : ℝ}
    (hg : MonotoneOn g (Icc a b)) (hc : c ∈ Ioc a b) :
    ∃ L : ℝ, LeftRelativeLimit g (Icc a b) c L := by
  have hcI : c ∈ Icc a b := ⟨hc.1.le, hc.2⟩
  have hne : (g '' (Icc a b ∩ Iio c)).Nonempty :=
    ⟨g a, mem_image_of_mem g ⟨⟨le_rfl, hc.1.le.trans hc.2⟩, hc.1⟩⟩
  have hbd : BddAbove (g '' (Icc a b ∩ Iio c)) := by
    refine ⟨g c, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hg hx.1 hcI hx.2.le
  refine ⟨sSup (g '' (Icc a b ∩ Iio c)), ?_⟩
  exact (leftRelativeLimit_filter_iff _ _ _ _).mpr
    ⟨closedInterval_left_accumulation hc,
      monotoneOn_tendsto_left_of_isLUB hg (isLUB_csSup hne hbd)⟩

/-- The right-hand image is nonempty and bounded below by the finite value at c. -/
theorem monotoneOn_closedInterval_right_limit {g : ℝ → ℝ} {a b c : ℝ}
    (hg : MonotoneOn g (Icc a b)) (hc : c ∈ Ico a b) :
    ∃ L : ℝ, RightRelativeLimit g (Icc a b) c L := by
  have hcI : c ∈ Icc a b := ⟨hc.1, hc.2.le⟩
  have hne : (g '' (Icc a b ∩ Ioi c)).Nonempty :=
    ⟨g b, mem_image_of_mem g ⟨⟨hc.1.trans hc.2.le, le_rfl⟩, hc.2⟩⟩
  have hbd : BddBelow (g '' (Icc a b ∩ Ioi c)) := by
    refine ⟨g c, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hg hcI hx.1 hx.2.le
  refine ⟨sInf (g '' (Icc a b ∩ Ioi c)), ?_⟩
  exact (rightRelativeLimit_filter_iff _ _ _ _).mpr
    ⟨closedInterval_right_accumulation hc,
      monotoneOn_tendsto_right_of_isGLB hg (isGLB_csInf hne hbd)⟩

theorem finite_left_limits : Specs.SingleVariableAnalysis.Ch15.OneSided.finiteLeftLimits := by
  intro f a b hab hf c hc
  obtain ⟨g, h, hg, hh, heq⟩ := (jordan_iff f hab).mp hf
  obtain ⟨Lg, hLg⟩ := monotoneOn_closedInterval_left_limit hg hc
  obtain ⟨Lh, hLh⟩ := monotoneOn_closedInterval_left_limit hh hc
  have hgT := ((leftRelativeLimit_filter_iff _ _ _ _).mp hLg).2
  have hhT := ((leftRelativeLimit_filter_iff _ _ _ _).mp hLh).2
  refine ⟨Lg - Lh, (leftRelativeLimit_filter_iff _ _ _ _).mpr
    ⟨closedInterval_left_accumulation hc, ?_⟩⟩
  apply (hgT.sub hhT).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (heq x hx.1).symm

theorem finite_right_limits : Specs.SingleVariableAnalysis.Ch15.OneSided.finiteRightLimits := by
  intro f a b hab hf c hc
  obtain ⟨g, h, hg, hh, heq⟩ := (jordan_iff f hab).mp hf
  obtain ⟨Lg, hLg⟩ := monotoneOn_closedInterval_right_limit hg hc
  obtain ⟨Lh, hLh⟩ := monotoneOn_closedInterval_right_limit hh hc
  have hgT := ((rightRelativeLimit_filter_iff _ _ _ _).mp hLg).2
  have hhT := ((rightRelativeLimit_filter_iff _ _ _ _).mp hLh).2
  refine ⟨Lg - Lh, (rightRelativeLimit_filter_iff _ _ _ _).mpr
    ⟨closedInterval_right_accumulation hc, ?_⟩⟩
  apply (hgT.sub hhT).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (heq x hx.1).symm

/-- A difference is continuous wherever both components are continuous.
The exceptional set therefore lies in a union of two countable sets; relative
continuity ensures that this includes possible endpoint discontinuities. -/
theorem countable_discontinuities :
    Specs.SingleVariableAnalysis.Ch15.OneSided.countableDiscontinuities := by
  intro f a b hab hf
  obtain ⟨g, h, hg, hh, heq⟩ := (jordan_iff f hab).mp hf
  have hgC := monotone_countable_discontinuities g (Icc a b) ordConnected_Icc hg
  have hhC := monotone_countable_discontinuities h (Icc a b) ordConnected_Icc hh
  apply (hgC.union hhC).mono
  intro x hx
  by_contra hn
  have hgcont : ContinuousWithinAt g (Icc a b) x := by
    by_contra hn'
    exact hn (Or.inl ⟨hx.1, hn'⟩)
  have hhcont : ContinuousWithinAt h (Icc a b) x := by
    by_contra hn'
    exact hn (Or.inr ⟨hx.1, hn'⟩)
  exact hx.2 ((hgcont.sub hhcont).congr_of_mem heq hx.1)

end SingleVariableAnalysis.BV
