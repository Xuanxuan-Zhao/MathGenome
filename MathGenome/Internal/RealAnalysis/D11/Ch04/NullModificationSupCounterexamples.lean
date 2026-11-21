import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.NullModificationSupCounterexamples
import MathGenome.Internal.RealAnalysis.D11.Ch03.NonborelLebesgue
import MathGenome.Internal.RealAnalysis.D11.Ch04.AeCommonException
import MathGenome.Internal.RealAnalysis.D11.Ch04.MeasurableMapTests

/-! The null-modification and uncountable-supremum failures use the same kind
of witness as Chapter 3: a non-Borel subset of the middle-thirds Cantor set.
All measurability assertions use the original Borel domain.
-/

noncomputable section
open Set MeasureTheory

namespace D11.Ch04.NullModificationSupCounterexamples

theorem indicator_preimage_half :
    Specs.D11.Ch04.NullModificationSupCounterexamples.indicator_preimage_half := by
  classical
  intro N
  ext x
  by_cases hx : x ∈ N <;> norm_num [hx]

theorem indicator_not_borel :
    Specs.D11.Ch04.NullModificationSupCounterexamples.indicator_not_borel := by
  intro N hN hf
  apply hN
  rw [← indicator_preimage_half N]
  exact hf measurableSet_Ioi

theorem incomplete_modification_failure :
    Specs.D11.Ch04.NullModificationSupCounterexamples.incomplete_modification_failure := by
  intro N hNC hN
  have hout : ∀ x, x ∉ Specs.D11.Ch03.CantorSet.C_value →
      N.indicator (fun _ => (1 : ℝ)) x = 0 := by
    intro x hx
    exact indicator_of_notMem (fun h => hx (hNC h)) _
  refine ⟨Ch03.CantorSet.C_borel, Ch03.CantorSet.C_volume_zero,
    measurable_const, hout, ?_, indicator_not_borel N hN, indicator_preimage_half N⟩
  exact ⟨Specs.D11.Ch03.CantorSet.C_value,
    ⟨Ch03.CantorSet.C_borel, Ch03.CantorSet.C_volume_zero⟩, hout⟩

/-- A bounded real supremum of singleton indicators recovers the indicator of
their union. Nonemptiness is explicit because ℝ is conditionally complete. -/
theorem iSup_singleton_indicators (N : Set ℝ) (hN : N.Nonempty) :
    (fun x : ℝ => ⨆ a : N, ({a.val} : Set ℝ).indicator (fun _ => (1 : ℝ)) x) =
      N.indicator (fun _ => (1 : ℝ)) := by
  classical
  let : Nonempty N := hN.to_subtype
  funext x
  have hbound : BddAbove (range (fun a : N =>
      ({a.val} : Set ℝ).indicator (fun _ => (1 : ℝ)) x)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    by_cases hx : x = a.val <;> simp [hx]
  apply le_antisymm
  · apply ciSup_le
    intro a
    by_cases hx : x ∈ N
    · by_cases ha : x = a.val <;> simp [hx, ha]
    · have ha : x ≠ a.val := fun h => hx (h ▸ a.property)
      simp [hx, ha]
  · by_cases hx : x ∈ N
    · simpa [hx] using le_ciSup hbound (⟨x, hx⟩ : N)
    · obtain ⟨a⟩ := (inferInstance : Nonempty N)
      have ha : x ≠ a.val := fun h => hx (h ▸ a.property)
      simpa [hx, ha] using le_ciSup hbound a

theorem uncountable_sup_failure :
    Specs.D11.Ch04.NullModificationSupCounterexamples.uncountable_sup_failure := by
  intro N _ hN
  have hcount : ¬ N.Countable := fun h => hN h.measurableSet
  have hne : N.Nonempty := by
    by_contra h
    exact hN (by simp [not_nonempty_iff_eq_empty.mp h])
  have heq := iSup_singleton_indicators N hne
  refine ⟨hcount, ?_, heq, ?_⟩
  · intro a
    refine ⟨measurable_const.indicator (measurableSet_singleton a.val), ?_⟩
    intro x
    classical
    by_cases hx : x = a.val <;> simp [hx]
  · rw [heq]
    exact indicator_not_borel N hN

theorem exists_incomplete_modification :
    Specs.D11.Ch04.NullModificationSupCounterexamples.exists_incomplete_modification := by
  obtain ⟨N, hNC, hN⟩ := Ch03.NonborelLebesgue.exists_nonborel_cantor_subset
  exact ⟨N, hNC, incomplete_modification_failure N hNC hN⟩

theorem exists_uncountable_sup :
    Specs.D11.Ch04.NullModificationSupCounterexamples.exists_uncountable_sup := by
  obtain ⟨N, hNC, hN⟩ := Ch03.NonborelLebesgue.exists_nonborel_cantor_subset
  exact ⟨N, hNC, uncountable_sup_failure N hNC hN⟩

end D11.Ch04.NullModificationSupCounterexamples
