import MathGenome.Internal.Specs.D07.Ch09.SecondIsomorphism
import MathGenome.Internal.D07.Ch09.FirstIsomorphism

/-!
K07.09.second_isomorphism, paper.tex:1583–1597.
Saturation is precisely the set A + I. The restriction of reduction modulo I
is onto and has kernel A ∩ I, so the unital result follows from the accepted
first isomorphism theorem. The last part repeats the construction with
nonunital maps and additive-coset congruence quotients.
-/

universe u

namespace D07.Ch09.SecondIsomorphism

open Specs.D07.Ch09.SecondIsomorphism

/-- A representative of the same coset differs by an element of I. -/
theorem sameCoset_iff_sum {R : Type u} [Ring R] (A : Set R)
    (I : Ideal R) [I.IsTwoSided] (x : R) :
    (∃ a ∈ A, Ideal.Quotient.mk I a = Ideal.Quotient.mk I x) ↔
      ∃ a ∈ A, ∃ i ∈ I, x = a + i := by
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨a, ha, x - a, Ideal.Quotient.eq.mp h.symm, ?_⟩
    exact ((add_comm a (x - a)).trans (sub_add_cancel x a)).symm
  · rintro ⟨a, ha, i, hi, rfl⟩
    refine ⟨a, ha, ?_⟩
    rw [map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hi, add_zero]

theorem sum_carrier : SumCarrier.{u} := by
  intro R _ A I _ x
  exact sameCoset_iff_sum (A : Set R) I x

theorem sum_inclusions : SumInclusions.{u} := by
  intro R _ A I _
  refine ⟨fun a ha => ⟨a, ha, rfl⟩, ?_⟩
  intro i hi
  refine ⟨0, A.zero_mem, ?_⟩
  rw [map_zero, (Ideal.Quotient.eq_zero_iff_mem).mpr hi]

theorem intersection_ideal_properties : IntersectionIdealProperties.{u} := by
  intro R _ A I _
  exact ⟨inferInstance, fun _ => Iff.rfl⟩

theorem restriction_surjective : RestrictionSurjective.{u} := by
  intro R _ A I _ y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha, h⟩ := x.property
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Ideal.Quotient.eq.mpr
  exact (Ideal.Quotient.eq (I := I)).mp h

theorem restriction_kernel : RestrictionKernel.{u} := by
  intro R _ A I _
  apply Ideal.ext
  intro a
  change Ideal.Quotient.mk _ (sumInclusion A I a) = 0 ↔ (a : R) ∈ I
  exact Ideal.Quotient.eq_zero_iff_mem

theorem second_isomorphism : SecondIsomorphism.{u} := by
  intro R _ A I _
  obtain ⟨e, he⟩ := D07.Ch09.FirstIsomorphism.first_isomorphism_of_surjective
    A (sumSubring A I ⧸ intersectionIdeal (sumSubring A I) I)
    (restriction A I) (restriction_surjective R A I)
  refine ⟨(Ideal.quotEquivOfEq (restriction_kernel R A I).symm).trans e, ?_⟩
  intro a
  simpa only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk] using he a

theorem nonUnital_sum_carrier : NonUnitalSumCarrier.{u} := by
  intro R _ A I _ x
  exact sameCoset_iff_sum (A : Set R) I x

theorem nonUnital_sum_inclusions : NonUnitalSumInclusions.{u} := by
  intro R _ A I _
  refine ⟨fun a ha => ⟨a, ha, rfl⟩, ?_⟩
  intro i hi
  refine ⟨0, A.zero_mem, ?_⟩
  change Ideal.Quotient.mk I 0 = Ideal.Quotient.mk I i
  rw [map_zero, (Ideal.Quotient.eq_zero_iff_mem).mpr hi]

theorem nonUnital_intersection_properties : NonUnitalIntersectionProperties.{u} := by
  intro R _ A I _
  refine ⟨fun _ => Iff.rfl, ?_⟩
  intro a b hb
  exact ⟨I.mul_mem_left (a : R) hb, I.mul_mem_right (a : R) hb⟩

theorem nonUnital_quotient_relation : NonUnitalQuotientRelation.{u} := by
  intro R _ A I _ a b
  rw [RingCon.eq]
  exact (Submodule.quotientRel_def I).trans Iff.rfl

theorem nonUnital_restriction_surjective : NonUnitalRestrictionSurjective.{u} := by
  intro R _ A I _ y
  obtain ⟨x, rfl⟩ := Quotient.mk''_surjective y
  obtain ⟨a, ha, h⟩ := x.property
  refine ⟨⟨a, ha⟩, ?_⟩
  apply (nonUnital_quotient_relation R (sumNonUnitalSubring A I) I _ _).mpr
  exact (Ideal.Quotient.eq (I := I)).mp h

theorem nonUnital_restriction_kernel : NonUnitalRestrictionKernel.{u} := by
  intro R _ A I _ a
  change (RingCon.toQuotient (nonUnitalSumInclusion A I a) :
    (nonUnitalCongruence (sumNonUnitalSubring A I) I).Quotient) =
    RingCon.toQuotient 0 ↔ (a : R) ∈ I
  rw [nonUnital_quotient_relation]
  change (a : R) - 0 ∈ I ↔ (a : R) ∈ I
  rw [sub_zero]

/-- The induced map between the two nonunital coset quotients. -/
def nonUnitalQuotientMap {R : Type u} [Ring R] (A : NonUnitalSubring R)
    (I : Ideal R) [I.IsTwoSided] :
    (nonUnitalCongruence A I).Quotient →ₙ+*
      (nonUnitalCongruence (sumNonUnitalSubring A I) I).Quotient where
  toFun := Quotient.map' (nonUnitalSumInclusion A I) (fun _ _ h => h)
  map_zero' := rfl
  map_add' x y := by
    induction x using Quotient.inductionOn' with | h a =>
      induction y using Quotient.inductionOn' with | h b => rfl
  map_mul' x y := by
    induction x using Quotient.inductionOn' with | h a =>
      induction y using Quotient.inductionOn' with | h b => rfl

theorem nonUnital_second_isomorphism : NonUnitalSecondIsomorphism.{u} := by
  intro R _ A I _
  have hinj : Function.Injective (nonUnitalQuotientMap A I) := by
    intro x y
    induction x using Quotient.inductionOn' with | h a =>
      induction y using Quotient.inductionOn' with | h b =>
        intro h
        change (RingCon.toQuotient (nonUnitalSumInclusion A I a) :
          (nonUnitalCongruence (sumNonUnitalSubring A I) I).Quotient) =
            RingCon.toQuotient (nonUnitalSumInclusion A I b) at h
        exact (nonUnital_quotient_relation R A I a b).mpr
          ((nonUnital_quotient_relation R (sumNonUnitalSubring A I) I _ _).mp h)
  have hsurj : Function.Surjective (nonUnitalQuotientMap A I) := by
    intro y
    obtain ⟨a, ha⟩ := nonUnital_restriction_surjective R A I y
    exact ⟨RingCon.toQuotient a, ha⟩
  exact ⟨RingEquiv.ofBijective (nonUnitalQuotientMap A I) ⟨hinj, hsurj⟩, fun _ => rfl⟩

end D07.Ch09.SecondIsomorphism
