import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.TranslationDilation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Translations and scalar dilations, including arbitrary nonmeasurable sets.
The native Haar formula is transported through the upstream equality of
outer measures on *all* subsets. The completed measurable-space assertion is
proved separately from the splitting test, rather than identifying Borel
measurability with Lebesgue measurability. -/

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace D11.Ch03.TranslationDilation

open OuterVolume LebesgueMeasures

/-- An equivalence scaling an outer measure by a positive finite constant
preserves the full splitting test in both directions. -/
theorem caratheodory_image_iff {α : Type*} (m : OuterMeasure α) (e : α ≃ α)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hct : c ≠ ∞)
    (hm : ∀ S : Set α, m (e '' S) = c * m S) (E : Set α) :
    m.IsCaratheodory (e '' E) ↔ m.IsCaratheodory E := by
  constructor
  · intro h T
    have ht := h (e '' T)
    rw [← Set.image_inter e.injective, ← Set.image_sdiff e.injective] at ht
    simp only [hm, ← mul_add] at ht
    exact (ENNReal.mul_right_inj hc hct).mp ht
  · intro h T
    have ht := congrArg (c * ·) (h (e ⁻¹' T))
    rw [mul_add, ← hm, ← hm, ← hm, Set.image_inter e.injective,
      Set.image_sdiff e.injective, Set.image_preimage_eq T e.surjective] at ht
    exact ht

/-- The topology is the Euclidean topology inherited from `Point d`. -/
noncomputable def affineHomeomorph {d : ℕ} (a : Point d) (r : ℝ) (hr : r ≠ 0) :
    Point d ≃ₜ Point d :=
  (Homeomorph.smulOfNeZero r hr).trans (Homeomorph.addLeft a)

theorem affineHomeomorph_apply {d : ℕ} (a : Point d) (r : ℝ) (hr : r ≠ 0)
    (x : Point d) : affineHomeomorph a r hr x = a + r • x := rfl

/-- This native result, like the outer-volume statement, tests every subset. -/
theorem volume_affine (d : ℕ) (a : Point d) (r : ℝ) (E : Set (Point d)) :
    volume ((fun x => a + r • x) '' E) = ENNReal.ofReal (|r| ^ d) * volume E := by
  have hset : (fun x => a + r • x) '' E =
      (fun y => a + y) '' ((fun x => r • x) '' E) := by
    rw [image_image]
  rw [hset, image_add_left, measure_preimage_add, image_smul, Measure.addHaar_smul]
  simp only [finrank_euclideanSpace, Fintype.card_fin, abs_pow]

theorem outer_affine : Specs.D11.Ch03.TranslationDilation.outer_affine := by
  intro d _ a r E
  rw [← native_outer_agreement, ← native_outer_agreement]
  exact volume_affine d a r E

theorem borel_image_iff : Specs.D11.Ch03.TranslationDilation.borel_image_iff := by
  intro d _ a r hr E
  rw [← borel_structure d]
  exact (affineHomeomorph a r hr).toMeasurableEquiv.measurableSet_image

theorem lebesgue_image_iff : Specs.D11.Ch03.TranslationDilation.lebesgue_image_iff := by
  intro d _ a r hr E
  change (outerVolume d).IsCaratheodory ((fun x => a + r • x) '' E) ↔
    (outerVolume d).IsCaratheodory E
  exact caratheodory_image_iff (outerVolume d) (affineHomeomorph a r hr).toEquiv
    (ENNReal.ofReal (|r| ^ d))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos (abs_pos.mpr hr) d)))
    ENNReal.ofReal_ne_top (fun S => outer_affine d a r S) E

theorem zero_image : Specs.D11.Ch03.TranslationDilation.zero_image := by
  intro d _ a E
  rcases E.eq_empty_or_nonempty with rfl | hE
  · exact Or.inl ⟨rfl, image_empty _⟩
  · right
    exact ⟨hE, by simpa only [zero_smul, add_zero] using hE.image_const a⟩

theorem zero_image_measurable_null :
    Specs.D11.Ch03.TranslationDilation.zero_image_measurable_null := by
  intro d _ a E
  dsimp only
  have hF : MeasurableSet[borel (Point d)] ((fun x => a + (0 : ℝ) • x) '' E) := by
    rw [← borel_structure d]
    rcases zero_image d a E with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; exact MeasurableSet.empty
    · rw [h]; exact measurableSet_singleton a
  have hnull : Specs.D11.Ch03.LebesgueMeasures.coveringOuter d
      ((fun x => a + (0 : ℝ) • x) '' E) = 0 := by
    rw [outer_affine]
    simp [NeZero.ne d]
  have hL : MeasurableSet[lebesgueSpace d] ((fun x => a + (0 : ℝ) • x) '' E) :=
    (outerVolume d).isCaratheodory_of_measure_eq_zero hnull
  refine ⟨hF, hL, hnull, ?_, ?_⟩
  · exact (borel_apply d _ hF).trans hnull
  · exact (lebesgue_apply d _ hL).trans hnull

theorem borel_affine : Specs.D11.Ch03.TranslationDilation.borel_affine := by
  intro d _ a r E hE
  have hF : MeasurableSet[borel (Point d)] ((fun x => a + r • x) '' E) := by
    by_cases hr : r = 0
    · subst r; exact (zero_image_measurable_null d a E).1
    · exact (borel_image_iff d a r hr E).mpr hE
  refine ⟨hF, ?_⟩
  rw [borel_apply d _ hF, borel_apply d E hE]
  exact outer_affine d a r E

theorem lebesgue_affine : Specs.D11.Ch03.TranslationDilation.lebesgue_affine := by
  intro d _ a r E hE
  have hF : MeasurableSet[lebesgueSpace d] ((fun x => a + r • x) '' E) := by
    by_cases hr : r = 0
    · subst r; exact (zero_image_measurable_null d a E).2.1
    · exact (lebesgue_image_iff d a r hr E).mpr hE
  refine ⟨hF, ?_⟩
  rw [lebesgue_apply d _ hF, lebesgue_apply d E hE]
  exact outer_affine d a r E

end D11.Ch03.TranslationDilation
