import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.NestedIntervals
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SupInf
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Squeeze
import Mathlib.Tactic.Linarith

/-!
# Nested closed real intervals

Implements `K03.01.nested_intervals` using the supremum of the left endpoints.
No shrinking hypothesis is used for existence. For uniqueness, the distance
between two common points is bounded by every interval length, and the upstream
absolute-estimate theorem makes this constant error converge to zero.
Indices are shifted exactly as in `SingleVariableAnalysis.Ch01.SequenceLimit`.
-/

namespace SingleVariableAnalysis

/-- Nonempty consecutive nested closed bounded intervals have a common point. -/
theorem nested_intervals_nonempty (a b : ℕ → ℝ)
    (hne : ∀ n, a n ≤ b n)
    (hnest : ∀ n, Set.Icc (a (n + 1)) (b (n + 1)) ⊆ Set.Icc (a n) (b n)) :
    (⋂ n, Set.Icc (a n) (b n)).Nonempty := by
  have hanti : Antitone (fun n => Set.Icc (a n) (b n)) :=
    antitone_nat_of_succ_le hnest
  -- Every right endpoint bounds the entire range of left endpoints.
  have hcross : ∀ n j, a n ≤ b j := by
    intro n j
    rcases le_total n j with hnj | hjn
    · exact (hanti hnj ⟨le_rfl, hne j⟩).1.trans (hne j)
    · exact (hanti hjn ⟨le_rfl, hne n⟩).2
  have hrange : (Set.range a).Nonempty := ⟨a 0, Set.mem_range_self 0⟩
  have hbounded : BddAbove (Set.range a) := by
    refine ⟨b 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hcross n 0
  let s := realSupremum (Set.range a) hrange hbounded
  have hs : IsLUB (Set.range a) s :=
    real_supremum_isLUB (Set.range a) hrange hbounded
  refine ⟨s, Set.mem_iInter.mpr fun j => ⟨hs.1 (Set.mem_range_self j), ?_⟩⟩
  apply hs.2
  rintro _ ⟨n, rfl⟩
  exact hcross n j

/-- If the lengths tend to zero, the common point is unique. -/
theorem nested_intervals_singleton (a b : ℕ → ℝ)
    (hne : ∀ n, a n ≤ b n)
    (hnest : ∀ n, Set.Icc (a (n + 1)) (b (n + 1)) ⊆ Set.Icc (a n) (b n))
    (hlength : RealSequenceConverges (fun n => b n - a n) 0) :
    ∃ x : ℝ, (⋂ n, Set.Icc (a n) (b n)) = {x} := by
  obtain ⟨s, hs⟩ := nested_intervals_nonempty a b hne hnest
  refine ⟨s, Set.ext fun x => ?_⟩
  constructor
  · intro hx
    have hbound : SequenceEventually (fun n => |x - s| ≤ b n - a n) := by
      refine ⟨0, fun n _ => ?_⟩
      obtain ⟨hax, hxb⟩ := Set.mem_iInter.mp hx n
      obtain ⟨has, hsb⟩ := Set.mem_iInter.mp hs n
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hc : RealSequenceConverges (fun _ => x) s :=
      realSequenceConverges_of_abs_le (fun _ => x) s (fun n => b n - a n)
        hbound hlength
    apply Set.mem_singleton_iff.mpr
    by_contra hxs
    have hpos : 0 < |x - s| := abs_pos.mpr (sub_ne_zero.mpr hxs)
    obtain ⟨N, hN⟩ := hc |x - s| hpos
    exact (lt_irrefl |x - s|) (hN N le_rfl)
  · intro hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hs

/-- Constant `[0,1]` intervals are nonempty and nested, and their intersection
is `[0,1]`, containing the distinct points zero and one. -/
theorem constant_unit_intervals :
    let I : ℕ → Set ℝ := fun _ => Set.Icc 0 1
    (∀ n, (I n).Nonempty) ∧
    (∀ n, I (n + 1) ⊆ I n) ∧
    (⋂ n, I n) = Set.Icc (0 : ℝ) 1 ∧
    ¬ ∃ x : ℝ, (⋂ n, I n) = {x} := by
  dsimp only
  have hi : (⋂ _ : ℕ, Set.Icc (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 :=
    Set.iInter_const _
  refine ⟨fun _ => ⟨0, ⟨le_rfl, zero_le_one⟩⟩, fun _ => Set.Subset.rfl, hi, ?_⟩
  rintro ⟨x, hx⟩
  have hzero : (0 : ℝ) ∈ (⋂ _ : ℕ, Set.Icc (0 : ℝ) 1) := by
    rw [hi]
    exact ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ (⋂ _ : ℕ, Set.Icc (0 : ℝ) 1) := by
    rw [hi]
    exact ⟨zero_le_one, le_rfl⟩
  rw [hx, Set.mem_singleton_iff] at hzero hone
  exact zero_ne_one (hzero.trans hone.symm)

end SingleVariableAnalysis
