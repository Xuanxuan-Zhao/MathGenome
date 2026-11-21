import MathGenome.Internal.Specs.D07.Ch10.Associates
import MathGenome.Internal.D07.Ch08.PrincipalDivisibility
import MathGenome.Internal.D07.Ch10.Divisibility
import Mathlib.Algebra.Polynomial.Degree.Units

/-!
Associates in a commutative nontrivial domain, K07.10.associates.
The canonical relation is connected to the source's unit-multiple convention,
mutual divisibility, and the upstream principal two-sided ideals. The final
specializations retain the zero cases in ℤ and in polynomials over any field.
-/

universe u

namespace D07.Ch10.Associates

open Specs.D07.Ch10.Associates

theorem associateCharacterization : AssociateCharacterization.{u} := by
  intro R _ _ a b
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h.symm
    exact ⟨u, by simpa only [mul_comm] using hu.symm⟩
  · rintro ⟨u, hu⟩
    exact (show Associated b a from
      ⟨u, by simpa only [mul_comm] using hu.symm⟩).symm

theorem associateEquivalence : AssociateEquivalence.{u} := by
  intro R _ _
  exact ⟨Associated.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

theorem associatesIffMutualDivisibility : AssociatesIffMutualDivisibility.{u} := by
  intro R _ _ a b
  exact dvd_dvd_iff_associated.symm

theorem mutualDivisibilityIffPrincipalIdeals : MutualDivisibilityIffPrincipalIdeals.{u} := by
  intro R _ _ a b
  have hab := (D07.Ch08.PrincipalDivisibility.principalDivisibility R a b).2
  have hba := (D07.Ch08.PrincipalDivisibility.principalDivisibility R b a).2
  constructor
  · rintro ⟨h₁, h₂⟩
    exact le_antisymm (hba.mp h₂) (hab.mp h₁)
  · intro h
    exact ⟨hab.mpr h.ge, hba.mpr h.le⟩

theorem associatesIffPrincipalIdeals : AssociatesIffPrincipalIdeals.{u} := by
  intro R _ _ a b
  exact (associatesIffMutualDivisibility R a b).trans
    (mutualDivisibilityIffPrincipalIdeals R a b)

theorem zeroAssociates : ZeroAssociates.{u} := by
  intro R _ _ b
  exact Associated.comm.trans (associated_zero_iff_eq_zero b)

theorem integerAssociates : IntegerAssociates := by
  intro a b
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (associateCharacterization ℤ a b).mp h
    rcases (D07.Ch08.Units.integerUnits (u : ℤ)).mp u.isUnit with h₁ | h₁
    · exact Or.inl (by simpa only [h₁, one_mul] using hu)
    · exact Or.inr (by simpa only [h₁, neg_one_mul] using hu)
  · rintro (h | h)
    · exact Associated.of_eq h
    · rw [h, ← neg_one_mul b]
      exact associated_unit_mul_left b (-1) isUnit_one.neg

theorem polynomialAssociates : PolynomialAssociates.{u} := by
  intro F _ f g
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (associateCharacterization (Polynomial F) f g).mp h
    obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
    exact ⟨c, isUnit_iff_ne_zero.mp hc, by rw [← hcu] at hu; exact hu⟩
  · rintro ⟨c, hc, h⟩
    rw [h]
    exact associated_unit_mul_left g (Polynomial.C c)
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))

end D07.Ch10.Associates
