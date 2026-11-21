import MathGenome.Internal.Specs.D07.Ch22.LocalizationIdealsExtensionSaturation
import Mathlib.RingTheory.Localization.Ideal

/-!
K07.22.localization_ideals.extension_saturation, paper.tex:7126–7156.

The localization ideal API works for arbitrary multiplicative submonoids,
including those containing zero. We identify its fraction notation `mk'`
with the canonical quotient fractions `Localization.mk` used upstream.
-/

universe u

namespace D07.Ch22.LocalizationIdealsExtensionSaturation

open Specs.D07.Ch22.LocalizationIdealsExtensionSaturation

/-- Extension is exactly the set of fractions with numerator in the ideal. -/
theorem extendedIdealFractions : ExtendedIdealFractions.{u} := by
  intro R _ S I z
  rw [IsLocalization.mem_map_algebraMap_iff S (Localization S)]
  constructor
  · rintro ⟨⟨a, s⟩, h⟩
    refine ⟨a, a.property, s, ?_⟩
    rw [Localization.mk_eq_mk'_apply]
    exact IsLocalization.eq_mk'_iff_mul_eq.mpr h
  · rintro ⟨a, ha, s, rfl⟩
    refine ⟨⟨⟨a, ha⟩, s⟩, ?_⟩
    rw [Localization.mk_eq_mk'_apply]
    exact IsLocalization.mk'_spec (Localization S) a s

/-- The existential multiplier is essential when denominators are zero divisors. -/
theorem contractionSaturation : ContractionSaturation.{u} := by
  intro R _ S I r
  rw [Ideal.mem_comap,
    IsLocalization.algebraMap_mem_map_algebraMap_iff S (Localization S)]
  exact ⟨fun ⟨s, hs, h⟩ => ⟨⟨s, hs⟩, h⟩,
    fun ⟨s, h⟩ => ⟨s, s.property, h⟩⟩

/-- All ideals in the localization come from contraction and extension. -/
theorem everyIdealExtended : EveryIdealExtended.{u} := by
  intro R _ S J
  exact IsLocalization.map_under S (Localization S) J

/-- Applying saturation to one gives exactly the intersection criterion. -/
theorem extensionTopIffMeets : ExtensionTopIffMeets.{u} := by
  intro R _ S I
  rw [Ideal.eq_top_iff_one, ← map_one (algebraMap R (Localization S)),
    IsLocalization.algebraMap_mem_map_algebraMap_iff S (Localization S)]
  simp only [mul_one]
  exact ⟨fun ⟨s, hs, hI⟩ => ⟨s, hI, hs⟩,
    fun ⟨s, hI, hs⟩ => ⟨s, hs, hI⟩⟩

end D07.Ch22.LocalizationIdealsExtensionSaturation
