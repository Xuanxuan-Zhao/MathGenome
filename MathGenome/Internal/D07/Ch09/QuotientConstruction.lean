import MathGenome.Internal.Specs.D07.Ch09.QuotientConstruction
import Mathlib.Algebra.Group.Ext
import Mathlib.Tactic.Abel

/-!
K07.09.quotient_construction, paper.tex:1516–1533.
The canonical ideal quotient is the additive-coset quotient with a ring
structure when the ideal is two-sided. Conversely, multiply the equality
`i + H = 0 + H` on each side to derive both absorption conditions.
-/

universe u

namespace D07.Ch09.QuotientConstruction

open Specs.D07.Ch09.QuotientConstruction
open Specs.D07.Ch08.IdealDefinition

theorem additive_coset_eq_iff_sub_mem : AdditiveCosetEqIffSubMem.{u} := by
  intro R _ H a b
  constructor
  · intro h
    have ha : a ∈ additiveCoset H a := ⟨0, H.zero_mem, add_zero a⟩
    obtain ⟨i, hi, hbi⟩ := h ▸ ha
    have hab : a - b = i := by rw [← hbi]; simp
    exact hab ▸ hi
  · intro hab
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨a - b + i, H.add_mem hab hi, ?_⟩
      simp only [sub_eq_add_neg]
      abel
    · rintro ⟨i, hi, rfl⟩
      have hba : b - a ∈ H := by simpa only [neg_sub] using H.neg_mem hab
      refine ⟨b - a + i, H.add_mem hba hi, ?_⟩
      simp only [sub_eq_add_neg]
      abel

theorem quotient_eq_iff_coset_eq : QuotientEqIffCosetEq.{u} := by
  intro R _ I _ a b
  exact (Ideal.Quotient.eq (I := I)).trans
    (additive_coset_eq_iff_sub_mem R I.toAddSubgroup a b).symm

theorem ring_construction : RingConstruction.{u} := by
  intro R _ I _
  refine ⟨Ideal.Quotient.ring I, ?_, rfl, rfl⟩
  apply AddCommGroup.ext
  rfl

theorem quotient_operations : QuotientOperations.{u} := by
  intro R _ I _
  exact ⟨fun a b => (map_add (Ideal.Quotient.mk I) a b).symm,
    fun a b => (map_mul (Ideal.Quotient.mk I) a b).symm,
    map_one (Ideal.Quotient.mk I), map_zero (Ideal.Quotient.mk I),
    fun a => (map_neg (Ideal.Quotient.mk I) a).symm⟩

theorem quotient_ring_laws : QuotientRingLaws.{u} := by
  intro R _ I _
  exact {
    mul_assoc := _root_.mul_assoc
    left_distrib := _root_.left_distrib
    right_distrib := _root_.right_distrib
    one_mul := _root_.one_mul
    mul_one := _root_.mul_one }

theorem addition_independent : AdditionIndependent.{u} := by
  intro R _ H a a' b b' ha hb
  apply (additive_coset_eq_iff_sub_mem R H _ _).mpr
  have h := H.add_mem ((additive_coset_eq_iff_sub_mem R H a a').mp ha)
    ((additive_coset_eq_iff_sub_mem R H b b').mp hb)
  convert h using 1
  abel

theorem multiplication_independent_iff_two_sided :
    MultiplicationIndependentIffTwoSided.{u} := by
  intro R _ H
  constructor
  · intro hind
    have hi0 : ∀ i : R, i ∈ H → additiveCoset H i = additiveCoset H 0 := by
      intro i hi
      exact (additive_coset_eq_iff_sub_mem R H i 0).mpr (by simpa using hi)
    constructor
    · intro r i hi
      have h := (additive_coset_eq_iff_sub_mem R H (r * i) (r * 0)).mp
        (hind r r i 0 rfl (hi0 i hi))
      simpa only [mul_zero, sub_zero] using h
    · intro i r hi
      have h := (additive_coset_eq_iff_sub_mem R H (i * r) (0 * r)).mp
        (hind i 0 r r (hi0 i hi) rfl)
      simpa only [zero_mul, sub_zero] using h
  · intro hH a a' b b' ha hb
    apply (additive_coset_eq_iff_sub_mem R H _ _).mpr
    have haa' := (additive_coset_eq_iff_sub_mem R H a a').mp ha
    have hbb' := (additive_coset_eq_iff_sub_mem R H b b').mp hb
    rw [show a * b - a' * b' = (a - a') * b + a' * (b - b') by
      rw [sub_mul, mul_sub]
      abel]
    exact H.add_mem (hH.2 (a - a') b haa') (hH.1 a' (b - b') hbb')

end D07.Ch09.QuotientConstruction
