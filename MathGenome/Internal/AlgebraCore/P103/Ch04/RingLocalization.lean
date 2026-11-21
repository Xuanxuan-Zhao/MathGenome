import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.RingLocalization

namespace P103.Ch04.RingLocalization

universe u v

variable (R : Type u) [CommRing R] (S : Submonoid R)

theorem denominatorsAreUnits : RingLocalizationSpecs.DenominatorsAreUnits R S :=
  IsLocalization.map_units (Localization S)

theorem everyElementIsFraction : RingLocalizationSpecs.EveryElementIsFraction R S := by
  intro x
  obtain ⟨a, s, h⟩ := IsLocalization.exists_mk'_eq S x
  exact ⟨a, s, (Localization.mk_eq_mk'_apply a s).trans h |>.symm⟩

theorem fractionOverOne : RingLocalizationSpecs.FractionOverOne R S := by
  intro a
  rfl

theorem fractionAddition : RingLocalizationSpecs.FractionAddition R S := by
  intro a b s t
  simpa only [add_comm] using (Localization.add_mk a s b t)

theorem fractionMultiplication : RingLocalizationSpecs.FractionMultiplication R S :=
  fun a b s t => Localization.mk_mul a b s t

theorem fractionEquality : RingLocalizationSpecs.FractionEquality R S := by
  intro a b s t
  simp only [Localization.mk_eq_mk', IsLocalization.eq, mul_sub, sub_eq_zero]

theorem zeroRingCriterion : RingLocalizationSpecs.ZeroRingCriterion R S :=
  IsLocalization.subsingleton_iff

theorem universalProperty : RingLocalizationSpecs.UniversalProperty.{u, v} R S := by
  intro B _ g hg
  refine ⟨IsLocalization.lift (S := Localization S) hg, IsLocalization.lift_comp hg, ?_⟩
  intro f hf
  apply IsLocalization.ringHom_ext S
  exact hf.trans (IsLocalization.lift_comp hg).symm

theorem factorizationValue : RingLocalizationSpecs.FactorizationValue.{u, v} R S := by
  intro B _ g hg f hf a s
  apply (Ring.eq_mul_inverse_iff_mul_eq _ _ _ (hg s)).mpr
  have hs : f (algebraMap R (Localization S) (s : R)) = g (s : R) :=
    RingHom.congr_fun hf (s : R)
  rw [← hs, ← map_mul, Localization.mk_eq_mk', IsLocalization.mk'_spec]
  exact RingHom.congr_fun hf a

end P103.Ch04.RingLocalization
