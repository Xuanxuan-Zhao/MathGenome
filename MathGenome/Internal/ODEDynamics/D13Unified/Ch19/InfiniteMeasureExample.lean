import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.InfiniteMeasureExample
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.MeasureDefinitions

/-! Translation on ℤ is an infinite-measure counterexample to recurrence. -/

namespace D13Unified.Ch19.InfiniteMeasureExample

open Set MeasureTheory
open scoped ENNReal
open Specs.D13Unified.Ch15.DiscreteDefinitions
open D13Unified.Ch19.MeasureDefinitions

abbrev translation : ℤ → ℤ :=
  Specs.D13Unified.Ch19.InfiniteMeasureExample.translation

theorem translation_preserves_count :
    PreservesMeasure translation (Measure.count : Measure ℤ) := by
  have hinj : Function.Injective translation := by
    intro x y h
    exact add_right_cancel h
  have hsurj : Function.Surjective translation := by
    intro y
    exact ⟨y - 1, sub_add_cancel y 1⟩
  apply (preservesMeasure_iff translation Measure.count).mpr
  refine ⟨measurable_of_countable _, ?_⟩
  intro E _
  calc
    Measure.count (translation ⁻¹' E) =
        Measure.count (translation '' (translation ⁻¹' E)) :=
      (Measure.count_injective_image hinj _).symm
    _ = Measure.count E := by rw [Set.image_preimage_eq E hsurj]

theorem count_univ_infinite : (Measure.count : Measure ℤ) Set.univ = ∞ := by
  exact Measure.count_apply_infinite Set.infinite_univ

theorem count_zero_singleton : (Measure.count : Measure ℤ) {0} = 1 := by
  exact Measure.count_singleton 0

theorem iterate_translation (n : ℕ) (z : ℤ) :
    iterate translation n z = z + (n : ℤ) := by
  induction n with
  | zero => change z = z + (0 : ℤ); exact (add_zero z).symm
  | succ n ih =>
    change translation^[n + 1] z = _
    rw [Function.iterate_succ_apply']
    change iterate translation n z + 1 = _
    rw [ih, Nat.cast_add, Nat.cast_one, add_assoc]

theorem no_positive_return :
    ∀ z ∈ ({0} : Set ℤ), ∀ n : ℕ, 0 < n →
      iterate translation n z ∉ ({0} : Set ℤ) := by
  intro z hz n hn
  have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
  subst z
  rw [iterate_translation]
  simpa using (show (n : ℤ) ≠ 0 from ne_of_gt (Int.natCast_pos.mpr hn))

theorem positive_iterate_singleton_disjoint :
    ∀ n : ℕ, 0 < n →
      (iterate translation n '' ({0} : Set ℤ)) ∩ {0} = ∅ := by
  intro n hn
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨⟨x, hx, rfl⟩, hz⟩
  exact no_positive_return x hx n hn hz

theorem recurrence_fails :
    ¬ (∀ᵐ z ∂(Measure.count : Measure ℤ), z ∈ ({0} : Set ℤ) →
      Set.Infinite {n : ℕ | 0 < n ∧ iterate translation n z ∈ ({0} : Set ℤ)}) := by
  intro h
  have hret := (Measure.ae_count_iff.mp h) 0 (Set.mem_singleton 0)
  have hempty : {n : ℕ | 0 < n ∧ iterate translation n 0 ∈ ({0} : Set ℤ)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro n ⟨hn, hmem⟩
    exact no_positive_return 0 (Set.mem_singleton 0) n hn hmem
  rw [hempty] at hret
  exact Set.finite_empty.not_infinite hret

end D13Unified.Ch19.InfiniteMeasureExample
