import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.NoCountablyAdditiveBanachMeasure
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith

open Set MeasureTheory
open scoped ENNReal

namespace ExpandedFA.P1

private abbrev UnitInterval := ↥(Icc (0 : ℝ) 1)

/-- Two points of the unit interval are equivalent when their difference is rational. -/
private def rationalDifference : Setoid UnitInterval where
  r x y := ∃ q : ℚ, (x : ℝ) - (y : ℝ) = (q : ℝ)
  iseqv := {
    refl := fun x => ⟨0, by simp⟩
    symm := by
      rintro x y ⟨q, hq⟩
      exact ⟨-q, by push_cast; linarith⟩
    trans := by
      rintro x y z ⟨q, hq⟩ ⟨r, hr⟩
      exact ⟨q + r, by push_cast; linarith⟩ }

/-- Choice supplies one representative of each rational-difference class in `[0,1]`. -/
private theorem exists_vitali_representatives :
    ∃ V : Set ℝ, V ⊆ Icc 0 1 ∧
      (∀ x ∈ Icc (0 : ℝ) 1, ∃ v ∈ V, ∃ q : ℚ, x = v + (q : ℝ)) ∧
      (∀ a ∈ V, ∀ b ∈ V, ∀ q : ℚ, a - b = (q : ℝ) → a = b) := by
  classical
  let v : Quotient rationalDifference → UnitInterval := Quotient.out
  let V : Set ℝ := Set.range (fun i => (v i : ℝ))
  refine ⟨V, ?_, ?_, ?_⟩
  · rintro x ⟨i, rfl⟩
    exact (v i).property
  · intro x hx
    let i : Quotient rationalDifference := Quotient.mk _ ⟨x, hx⟩
    have hr : rationalDifference.r (v i) ⟨x, hx⟩ :=
      Quotient.exact (Quotient.out_eq i)
    rcases hr with ⟨q, hq⟩
    refine ⟨v i, ⟨i, rfl⟩, -q, ?_⟩
    push_cast
    change (v i : ℝ) - x = (q : ℝ) at hq
    linarith
  · rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ q hq
    have hij : i = j :=
      (Quotient.out_eq i).symm.trans
        ((Quotient.sound (show rationalDifference.r (v i) (v j) from ⟨q, hq⟩)).trans
          (Quotient.out_eq j))
    exact congrArg (fun i => (v i : ℝ)) hij

private abbrev RationalShifts := ↥(Icc (-1 : ℚ) 1)

/-- The rational translates are disjoint, cover `[0,1]`, and stay in `[-1,2]`. -/
private theorem exists_vitali_translates :
    ∃ V : Set ℝ,
      let F : RationalShifts → Set ℝ := fun q => (fun x => x + (q.val : ℝ)) '' V
      Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      Icc (0 : ℝ) 1 ⊆ ⋃ q, F q ∧ (⋃ q, F q) ⊆ Icc (-1 : ℝ) 2 := by
  classical
  obtain ⟨V, hV, hcover, hsep⟩ := exists_vitali_representatives
  refine ⟨V, ?_, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab : a = b := hsep a ha b hb (j.val - i.val) (by push_cast; linarith)
    apply hij
    apply Subtype.ext
    have heq : (i.val : ℝ) = (j.val : ℝ) := by linarith
    exact_mod_cast heq
  · intro x hx
    obtain ⟨a, ha, q, hxq⟩ := hcover x hx
    have ha' := hV ha
    have hq : q ∈ Icc (-1 : ℚ) 1 := by
      constructor
      · exact_mod_cast (show (-1 : ℝ) ≤ (q : ℝ) by linarith [hx.1, ha'.2])
      · exact_mod_cast (show (q : ℝ) ≤ 1 by linarith [hx.2, ha'.1])
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, ⟨a, ha, hxq.symm⟩⟩
  · intro x hx
    obtain ⟨q, a, ha, rfl⟩ := mem_iUnion.mp hx
    have ha' := hV ha
    have hl : (-1 : ℝ) ≤ (q.val : ℝ) := by exact_mod_cast q.property.1
    have hu : (q.val : ℝ) ≤ 1 := by exact_mod_cast q.property.2
    constructor <;> linarith [ha'.1, ha'.2]

/-- Only the masses of two bounded intervals are needed for the Vitali contradiction. -/
theorem no_allSetMeasure_of_interval_masses
    (μ : @Measure ℝ ⊤)
    (htrans : ∀ (t : ℝ) (s : Set ℝ), μ ((fun x => x + t) '' s) = μ s)
    (hunit : μ (Icc (0 : ℝ) 1) = 1)
    (hbound : μ (Icc (-1 : ℝ) 2) ≠ ∞) : False := by
  classical
  let : Infinite RationalShifts :=
    Set.infinite_coe_iff.mpr (Set.Icc_infinite (by norm_num))
  obtain ⟨V, hdisj, hcover, hbounded⟩ := exists_vitali_translates
  let F : RationalShifts → Set ℝ := fun q => (fun x => x + (q.val : ℝ)) '' V
  have hsum : μ (⋃ q, F q) = ∑' _ : RationalShifts, μ V := by
    rw [measure_iUnion hdisj (fun _ => MeasurableSpace.measurableSet_top)]
    exact tsum_congr (fun q => htrans _ V)
  have hlower : 1 ≤ ∑' _ : RationalShifts, μ V := by
    rw [← hsum, ← hunit]
    exact measure_mono hcover
  have hupper : (∑' _ : RationalShifts, μ V) ≤ μ (Icc (-1 : ℝ) 2) := by
    rw [← hsum]
    exact measure_mono hbounded
  by_cases hz : μ V = 0
  · simp [hz] at hlower
  · rw [ENNReal.tsum_const_eq_top_of_ne_zero hz] at hupper
    exact hbound (top_unique hupper)

/-- No translation-invariant, countably additive extension of Lebesgue measure
exists on the full power set of the real line. -/
theorem no_countably_additive_banach_measure :
    Specs.ExpandedFA.P1.NoCountablyAdditiveBanachMeasure := by
  rintro ⟨μ, htrans, hagree⟩
  apply no_allSetMeasure_of_interval_masses μ htrans
  · rw [hagree _ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
    norm_num
  · rw [hagree _ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

end ExpandedFA.P1
