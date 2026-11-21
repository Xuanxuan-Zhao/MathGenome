import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.IntegralClosureLocalization
import Mathlib.RingTheory.Localization.Integral

/-! Integral closure commutes with arbitrary localization (Theorem 4.5).
The two denominator-clearing lemmas used below normalize a monic equation
and then multiply by an annihilating denominator. Neither cancels in A.
-/
namespace P103.Ch04.IntegralClosureLocalization

universe u v
open Specs

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  (S : Submonoid R)

/-- Localizing the inclusion C ⊆ A is injective. -/
theorem localized_inclusion_injective : Specs.InjectiveType.{u,v} := by
  intro R A _ _ _ S
  exact IsLocalization.mapₐ_injective_of_injective S (Localization S) _ _
    (integralClosure R A).val Subtype.val_injective

/-- Clearing the coefficient denominators and then the vanishing witness. -/
theorem clear_denominators : Specs.ClearingType.{u,v} := by
  intro R A _ _ _ S a s h
  let L := Localization (Algebra.algebraMapSubmonoid A S)
  have ha : IsIntegral (Localization S) (algebraMap A L a) := by
    have hs : IsIntegral (Localization S)
        (algebraMap A L (algebraMap R A (s : R))) := by
      rw [← IsScalarTower.algebraMap_apply R A L,
        IsScalarTower.algebraMap_apply R (Localization S) L]
      exact isIntegral_algebraMap
    have hh := h.mul hs
    change IsIntegral (Localization S)
      (IsLocalization.mk' L a (denominator R A S s) *
        algebraMap A L (denominator R A S s : A)) at hh
    rwa [IsLocalization.mk'_spec] at hh
  obtain ⟨t, ht⟩ := IsIntegral.exists_multiple_integral_of_isLocalization S _ ha
  have ht' : IsIntegral R (algebraMap A L ((t : R) • a)) := by
    simpa only [Submonoid.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply R A L] using ht
  obtain ⟨u, hu, huta⟩ :=
    IsLocalization.exists_isIntegral_smul_of_isIntegral_map (Sₘ := L) S ht'
  refine ⟨⟨u, hu⟩, t, ?_, ?_⟩
  · simpa only [Submonoid.coe_mul, Subtype.coe_mk, mul_smul] using huta
  · dsimp only [fraction]
    rw [IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [denominator, Subtype.coe_mk, Submonoid.coe_mul, Algebra.smul_def, map_mul]
    ring

private theorem inclusion_fraction (c : integralClosure R A) (s : S) :
    localizedInclusion R A S (fraction R (integralClosure R A) S c s) =
      fraction R A S (c : A) s := by
  simp only [localizedInclusion, fraction, IsLocalization.mapₐ_coe,
    IsLocalization.map_mk']
  rfl

private theorem localized_integral (x :
    Localization (Algebra.algebraMapSubmonoid (integralClosure R A) S)) :
    IsIntegral (Localization S) (localizedInclusion R A S x) := by
  have hx : IsIntegral (Localization S) x :=
    isIntegral_localization (R := R) (S := integralClosure R A)
      (M := S) (Rₘ := Localization S) x
  exact hx.map (localizedInclusion R A S)

/-- The image is exactly the integral elements of the ambient localization. -/
theorem image_eq_integralClosure : Specs.ImageType.{u,v} := by
  intro R A _ _ _ S
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact localized_integral S y
  · intro hx
    obtain ⟨a, ⟨_, s, hs, rfl⟩, rfl⟩ :=
      IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid A S) x
    change IsIntegral (Localization S) (fraction R A S a ⟨s, hs⟩) at hx
    obtain ⟨u, t, hc, he⟩ := clear_denominators R A S a ⟨s, hs⟩ hx
    refine ⟨fraction R (integralClosure R A) S ⟨_, hc⟩ (u * t * ⟨s, hs⟩), ?_⟩
    exact (inclusion_fraction S _ _).trans he.symm

/-- Every integral fraction, and only such a fraction, has an integral numerator. -/
theorem integral_iff_representable : Specs.RepresentationType.{u,v} := by
  intro R A _ _ _ S a s
  constructor
  · intro h
    obtain ⟨u, t, hc, he⟩ := clear_denominators R A S a s h
    exact ⟨⟨_, hc⟩, u * t * s, he⟩
  · rintro ⟨c, t, he⟩
    rw [he, ← inclusion_fraction S c t]
    exact localized_integral S _

end P103.Ch04.IntegralClosureLocalization
