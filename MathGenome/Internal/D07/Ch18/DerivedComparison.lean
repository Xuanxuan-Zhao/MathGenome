import MathGenome.Internal.Specs.D07.Ch18.DerivedComparison
import MathGenome.Internal.D07.Ch15.SolvableGroups
import MathGenome.Internal.D07.Ch18.MixedCommutators
import MathGenome.Internal.D07.Ch18.NilpotenceCriteria

/-!
Derived-series characteristicity and comparison with the lower central series.
Both inductions use the existing recurrences. At a successor the first
commutator argument is bounded by the preceding lower term, and the second
by the whole group. Upper termination then gives lower termination at the
same bound, hence vanishing of the c-th derived term.
-/

namespace D07.Ch18.DerivedComparison

open Specs.D07.Ch18.CentralSeries

universe u

theorem derived_characteristic (G : Type u) [Group G] (r : ℕ) :
    (derivedSeries G r).Characteristic := by
  induction r with
  | zero =>
    rw [D07.Ch15.SolvableGroups.derived_zero G]
    infer_instance
  | succ r ih =>
    rw [D07.Ch15.SolvableGroups.derived_successor G r]
    exact MixedCommutators.commutator_characteristic G _ _ ih ih

theorem derived_le_lower (G : Type u) [Group G] (r : ℕ) :
    derivedSeries G r ≤ lowerValue G (r + 1) := by
  induction r with
  | zero =>
    rw [D07.Ch15.SolvableGroups.derived_zero G]
    exact le_rfl
  | succ r ih =>
    change derivedSeries G (r + 1) ≤ lowerValue G (r + 2)
    rw [D07.Ch15.SolvableGroups.derived_successor G r]
    change ⁅derivedSeries G r, derivedSeries G r⁆ ≤
      ⁅lowerValue G (r + 1), (⊤ : Subgroup G)⁆
    exact MixedCommutators.commutator_monotone G _ _ _ _ ih le_top

theorem classAtMost_derived_terminates (G : Type u) [Group G] (c : ℕ)
    (hc : NilpotenceCriteria.ClassAtMost G c) : derivedSeries G c = ⊥ := by
  have h := derived_le_lower G c
  rw [(NilpotenceCriteria.classAtMost_iff_lower G c).mp hc] at h
  exact le_bot_iff.mp h

theorem classAtMost_solvable (G : Type u) [Group G] (c : ℕ)
    (hc : NilpotenceCriteria.ClassAtMost G c) : Group.IsSolvable G :=
  (D07.Ch15.SolvableGroups.solvable_iff_derived_terminates G).mpr
    ⟨c, classAtMost_derived_terminates G c hc⟩

theorem nilpotent_solvable (G : Type u) [Group G]
    (hG : Group.IsNilpotent G) : Group.IsSolvable G := by
  obtain ⟨c, hc⟩ := (NilpotenceCriteria.nilpotent_iff_exists_bound G).mp hG
  exact classAtMost_solvable G c hc

end D07.Ch18.DerivedComparison
