import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.HeightOneIntersection
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.CodimensionTwoExtension

open TopologicalSpace CategoryTheory Opposite AlgebraicGeometry

set_option maxHeartbeats 400000

universe u
namespace AdvCommAlg.Normality

variable (A : Type u) [CommRing A] [IsDomain A]

private def genericPrime : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩

private lemma generic_mem (V : Opens (PrimeSpectrum A)) (p : PrimeSpectrum A)
    (hp : p ∈ V) : genericPrime A ∈ V := by
  exact ((PrimeSpectrum.le_iff_specializes _ _).mp (show genericPrime A ≤ p from bot_le)).mem_open V.isOpen hp

private lemma map_mk (p : PrimeSpectrum A) (a b : A) (hb : b ∉ p.asIdeal) :
    algebraMap (Localization.AtPrime p.asIdeal) (FractionRing A)
      (LocalizedModule.mk a ⟨b, hb⟩) =
        algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b := by
  change algebraMap (Localization.AtPrime p.asIdeal) (FractionRing A)
    (Localization.mk a ⟨b, hb⟩) = _
  rw [Localization.mk_eq_mk']
  have hb0 : b ≠ 0 := by
    intro h
    exact hb (h ▸ Ideal.zero_mem _)
  have hbK : algebraMap A (FractionRing A) b ≠ 0 := by
    intro h
    exact hb0 ((IsFractionRing.injective A (FractionRing A)) (by simpa using h))
  apply (eq_div_iff hbK).mpr
  · rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime p.asIdeal) (FractionRing A),
      ← map_mul, IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]

/-- A section has the same image in the fraction field at every point as at
its generic point. This uses the actual local-fraction condition in the sheaf. -/
private lemma section_fraction (U : Opens (PrimeSpectrum A))
    (hg : genericPrime A ∈ U) (s : (Spec.structureSheaf A).1.obj (op U))
    (p : PrimeSpectrum A) (hp : p ∈ U) :
    algebraMap (Localization.AtPrime p.asIdeal) (FractionRing A) (s.1 ⟨p, hp⟩) =
      algebraMap (Localization.AtPrime (genericPrime A).asIdeal) (FractionRing A)
        (s.1 ⟨genericPrime A, hg⟩) := by
  obtain ⟨V, hpV, i, a, b, h⟩ := s.2 ⟨p, hp⟩
  have hgV := generic_mem A V p hpV
  obtain ⟨hb, he⟩ := h ⟨p, hpV⟩
  obtain ⟨hbg, heg⟩ := h ⟨genericPrime A, hgV⟩
  change s.1 ⟨p, hp⟩ = LocalizedModule.mk a ⟨b, hb⟩ at he
  change s.1 ⟨genericPrime A, hg⟩ = LocalizedModule.mk a ⟨b, hbg⟩ at heg
  rw [he, heg, map_mk, map_mk]

/-- Restriction to an open containing all primes of height at most one is
bijective. The generic fraction is tested using SN-08, including height zero. -/
theorem codimensionTwo_restriction_bijective [IsNoetherianRing A]
    (hN : IsNormal A) (U : Opens (PrimeSpectrum A))
    (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 → p ∈ U) :
    Function.Bijective (algebraMap A ((Spec.structureSheaf A).1.obj (op U))) := by
  have hg : genericPrime A ∈ U := hU _ (by simp [genericPrime, Ideal.height_bot])
  constructor
  · intro a b hab
    have he := congrArg (fun s : (Spec.structureSheaf A).1.obj (op U) =>
      s.1 ⟨genericPrime A, hg⟩) hab
    change algebraMap A (Localization.AtPrime (genericPrime A).asIdeal) a =
      algebraMap A (Localization.AtPrime (genericPrime A).asIdeal) b at he
    apply IsFractionRing.injective A (FractionRing A)
    have he' := congrArg (algebraMap (Localization.AtPrime (genericPrime A).asIdeal)
      (FractionRing A)) he
    simpa only [← IsScalarTower.algebraMap_apply] using he'
  · intro s
    let z : FractionRing A :=
      algebraMap (Localization.AtPrime (genericPrime A).asIdeal) (FractionRing A)
        (s.1 ⟨genericPrime A, hg⟩)
    have hloc : ∀ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 →
        totalQuotientToAtPrime A p z ∈ Set.range
          (algebraMap (Localization.AtPrime p.asIdeal)
            (FractionRing (Localization.AtPrime p.asIdeal))) := by
      intro p hp
      have he := section_fraction A U hg s p (hU p hp)
      change algebraMap (Localization.AtPrime p.asIdeal) (FractionRing A)
        (s.1 ⟨p, hU p hp⟩) = z at he
      refine ⟨s.1 ⟨p, hU p hp⟩, ?_⟩
      rw [← he, totalQuotientToAtPrime_fractionMap]
    obtain ⟨a, ha⟩ := codimensionOne_membership A (normal_serreCondition_two A hN) z hloc
    refine ⟨a, Subtype.ext (funext fun p => ?_)⟩
    change algebraMap A (Localization.AtPrime p.1.asIdeal) a = s.1 p
    apply IsFractionRing.injective (Localization.AtPrime p.1.asIdeal) (FractionRing A)
    rw [← IsScalarTower.algebraMap_apply, ha]
    exact (section_fraction A U hg s p.1 p.2).symm

/-- Every genuine regular function on U extends uniquely to an element of A. -/
theorem codimensionTwo_extension_unique [IsNoetherianRing A]
    (hN : IsNormal A) (U : Opens (PrimeSpectrum A))
    (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 → p ∈ U)
    (s : (Spec.structureSheaf A).1.obj (op U)) :
    ∃! a : A, algebraMap A ((Spec.structureSheaf A).1.obj (op U)) a = s := by
  obtain ⟨a, ha⟩ := (codimensionTwo_restriction_bijective A hN U hU).surjective s
  exact ⟨a, ha, fun b hb => (codimensionTwo_restriction_bijective A hN U hU).injective
    (hb.trans ha.symm)⟩

/-- The isomorphism is induced by restriction of global regular functions. -/
theorem codimensionTwo_extension_ringEquiv [IsNoetherianRing A]
    (hN : IsNormal A) (U : Opens (PrimeSpectrum A))
    (hU : ∀ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 → p ∈ U) :
    ∃ e : A ≃+* (Spec.structureSheaf A).1.obj (op U),
      ∀ a : A, e a = algebraMap A ((Spec.structureSheaf A).1.obj (op U)) a := by
  exact ⟨RingEquiv.ofBijective (algebraMap A _) 
    (codimensionTwo_restriction_bijective A hN U hU), fun _ => rfl⟩

end AdvCommAlg.Normality
