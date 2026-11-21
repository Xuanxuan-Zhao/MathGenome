import MathGenome.Internal.Specs.D07.Ch22.LocalRings
import MathGenome.Internal.D07.Ch22.LocalizationIdeals
import MathGenome.Internal.D07.Ch09.MaximalQuotient

/-!
K07.22.local_rings, paper.tex:7169–7182.

The localization and the extended ideal are the canonical objects from the
preceding construction. Primeness, with no regularity assumption on the
denominators, suffices for all the assertions below.
-/

universe u

namespace D07.Ch22.LocalRings

open Specs.D07.Ch22.LocalRings

theorem localCharacterization : LocalCharacterization.{u} := by
  intro R _
  constructor
  · intro h
    let := h
    exact ⟨inferInstance, IsLocalRing.maximal_ideal_unique R⟩
  · rintro ⟨_, h⟩
    exact IsLocalRing.of_unique_max_ideal h

theorem localizationNontrivial : LocalizationNontrivial.{u} := by
  intro R _ P _
  exact IsLocalization.AtPrime.nontrivial (Localization.AtPrime P) P

theorem localizationLocal : LocalizationLocal.{u} := by
  intro R _ P _
  exact IsLocalization.AtPrime.isLocalRing (Localization.AtPrime P) P

theorem fractionUnitIff : FractionUnitIff.{u} := by
  intro R _ P _ a s
  rw [Localization.mk_eq_mk'_apply]
  exact IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime P) P a s

theorem fractionInverse : FractionInverse.{u} := by
  intro R _ P _ a s ha
  have h : Localization.mk a s * Localization.mk (s : R) ⟨a, ha⟩ = 1 := by
    simp only [Localization.mk_eq_mk'_apply]
    exact IsLocalization.mk'_mul_mk'_eq_one (S := Localization.AtPrime P) ⟨a, ha⟩ s
  exact ⟨h, (mul_comm _ _).trans h⟩

theorem extendedIdealEqMaximal : ExtendedIdealEqMaximal.{u} := by
  intro R _ P _
  exact Localization.AtPrime.map_eq_maximalIdeal

theorem fractionMemIff : FractionMemIff.{u} := by
  intro R _ P _ a s
  rw [extendedIdealEqMaximal R P, Localization.mk_eq_mk'_apply]
  exact IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime P) P a s

theorem nonunitsExtendedIdeal : NonunitsExtendedIdeal.{u} := by
  intro R _ P _ x
  rw [extendedIdealEqMaximal R P, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem properIdealsContained : ProperIdealsContained.{u} := by
  intro R _ P _ J hJ
  rw [extendedIdealEqMaximal R P]
  exact IsLocalRing.le_maximalIdeal hJ

theorem uniqueMaximalIdeal : UniqueMaximalIdeal.{u} := by
  intro R _ P _
  rw [extendedIdealEqMaximal R P]
  exact ⟨inferInstance, fun J hJ => IsLocalRing.eq_maximalIdeal hJ⟩

theorem residueField : ResidueField.{u} := by
  intro R _ P _
  exact (D07.Ch09.MaximalQuotient.maximal_iff_isField_quotient
    (Localization.AtPrime P) (Ideal.map (algebraMap R (Localization.AtPrime P)) P)).mp
    (uniqueMaximalIdeal R P).1

/-- Here the nonzero residue already has a unit representative, so its
actual inverse in the localization also supplies both inverse equations
modulo the extended ideal. -/
theorem residueInverse : ResidueInverse.{u} := by
  classical
  intro R _ P _ x hx
  have hu : IsUnit x := by
    by_contra h
    exact hx (Ideal.Quotient.eq_zero_iff_mem.mpr ((nonunitsExtendedIdeal R P x).mpr h))
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
  refine ⟨y, ?_, ?_⟩
  · rw [hy, sub_self]
    exact Ideal.zero_mem _
  · rw [mul_comm y x, hy, sub_self]
    exact Ideal.zero_mem _

/-- Projection onto the first factor gives a prime in a ring with zero
divisors. Inverting (1,0) kills the nonzero element (0,1). -/
theorem noninjectivityExample : NoninjectivityExample := by
  let P : Ideal (ℤ × ℤ) := Ideal.comap (RingHom.fst ℤ ℤ) ⊥
  have hP : P.IsPrime := inferInstance
  refine ⟨P, hP, ?_⟩
  let := hP
  have hs : ((1, 0) : ℤ × ℤ) ∉ P := by
    simp [P, Ideal.mem_comap]
  have hz : algebraMap (ℤ × ℤ) (Localization.AtPrime P) (0, 1) = 0 := by
    apply (IsLocalization.map_eq_zero_iff P.primeCompl (Localization.AtPrime P) (0, 1)).mpr
    exact ⟨⟨(1, 0), hs⟩, by
      change ((1, 0) : ℤ × ℤ) * (0, 1) = 0
      decide⟩
  intro hinj
  have heq : ((0, 1) : ℤ × ℤ) = (0 : ℤ × ℤ) := hinj (hz.trans (map_zero _).symm)
  have h := congrArg Prod.snd heq
  exact one_ne_zero h

end D07.Ch22.LocalRings
