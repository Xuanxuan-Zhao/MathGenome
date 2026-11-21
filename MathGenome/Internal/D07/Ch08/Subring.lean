import MathGenome.Internal.Specs.D07.Ch08.Subring
import MathGenome.Internal.D07.Ch08.RingDefinition

/-!
# Subring criteria and the nonunital example `2ℤ`

K07.08.subring, paper.tex:1273–1281. Derive zero, negation and addition
from nonemptiness and subtraction before constructing the bundled subring.
The subtype ring structures retain every ambient operation, including the
ambient identity in the unital case. No commutativity or nontriviality is
assumed in the general criteria.
-/

universe u

namespace D07.Ch08.Subring

open Specs.D07.Ch08.Subring

/-- The source's additive argument works in any nonempty subtraction-closed set. -/
theorem additiveClosureOfSub {R : Type u} [AddGroup R] (S : Set R)
    (hne : S.Nonempty) (hsub : ∀ a ∈ S, ∀ b ∈ S, a - b ∈ S) :
    AdditiveClosure S := by
  obtain ⟨s, hs⟩ := hne
  have hzero : (0 : R) ∈ S := by simpa only [sub_self] using hsub s hs s hs
  have hneg : ∀ a ∈ S, -a ∈ S := by
    intro a ha
    simpa only [zero_sub] using hsub 0 hzero a ha
  refine ⟨hzero, hneg, ?_⟩
  intro a ha b hb
  simpa only [sub_neg_eq_add] using hsub a ha (-b) (hneg b hb)

/-- Build the canonical nonunital subring from exactly the paper's hypotheses. -/
def nonUnitalSubringOfSubMul {R : Type u} [NonUnitalRing R] (S : Set R)
    (h : NonUnitalConditions S) : _root_.NonUnitalSubring R where
  carrier := S
  zero_mem' := (additiveClosureOfSub S h.1 h.2.1).1
  add_mem' := fun ha hb => (additiveClosureOfSub S h.1 h.2.1).2.2 _ ha _ hb
  neg_mem' := fun ha => (additiveClosureOfSub S h.1 h.2.1).2.1 _ ha
  mul_mem' := fun ha hb => h.2.2 _ ha _ hb

/-- In the unital case, membership of `1` supplies the needed nonemptiness. -/
def subringOfSubMul {R : Type u} [Ring R] (S : Set R)
    (h : UnitalConditions S) : _root_.Subring R where
  __ := nonUnitalSubringOfSubMul S ⟨⟨1, h.1⟩, h.2⟩
  one_mem' := h.1

theorem unitalSubringCharacterization : UnitalSubringCharacterization.{u} := by
  intro R _ S
  constructor
  · intro h
    exact ⟨subringOfSubMul S h, rfl⟩
  · rintro ⟨T, rfl⟩
    exact ⟨T.one_mem, (fun _ ha _ hb => T.sub_mem ha hb),
      (fun _ ha _ hb => T.mul_mem ha hb)⟩

theorem nonUnitalSubringCharacterization : NonUnitalSubringCharacterization.{u} := by
  intro R _ S
  constructor
  · intro h
    exact ⟨nonUnitalSubringOfSubMul S h, rfl⟩
  · rintro ⟨T, rfl⟩
    exact ⟨⟨0, T.zero_mem⟩, (fun _ ha _ hb => T.sub_mem ha hb),
      (fun _ ha _ hb => T.mul_mem ha hb)⟩

theorem unitalClosureConsequences : UnitalClosureConsequences.{u} := by
  intro R _ S h
  exact additiveClosureOfSub S ⟨1, h.1⟩ h.2.1

theorem nonUnitalClosureConsequences : NonUnitalClosureConsequences.{u} := by
  intro R _ S h
  exact additiveClosureOfSub S h.1 h.2.1

theorem unitalInheritedStructure : UnitalInheritedStructure.{u} := by
  intro R _ S h
  refine ⟨_root_.Subring.toRing (subringOfSubMul S h), rfl, rfl, ?_⟩
  exact ⟨(fun _ _ => rfl), (fun _ => rfl), (fun _ _ => rfl), (fun _ _ => rfl)⟩

theorem nonUnitalInheritedStructure : NonUnitalInheritedStructure.{u} := by
  intro R _ S h
  refine ⟨_root_.NonUnitalSubring.toNonUnitalRing (nonUnitalSubringOfSubMul S h), rfl, ?_⟩
  exact ⟨(fun _ _ => rfl), (fun _ => rfl), (fun _ _ => rfl), (fun _ _ => rfl)⟩

theorem evenIntegersNonUnitalSubring : EvenIntegersNonUnitalSubring := by
  apply (nonUnitalSubringCharacterization ℤ evenIntegers).mp
  refine ⟨⟨0, 0, (mul_zero 2).symm⟩, ?_, ?_⟩
  · rintro a ⟨k, rfl⟩ b ⟨l, rfl⟩
    exact ⟨k - l, (mul_sub 2 k l).symm⟩
  · rintro a ⟨k, rfl⟩ b ⟨l, rfl⟩
    exact ⟨k * (2 * l), mul_assoc 2 k (2 * l)⟩

/-- Any identity would act as an identity on `2`, forcing it to equal `1`. -/
theorem evenIntegersNoIdentity : EvenIntegersNoIdentity := by
  rintro ⟨e, ⟨k, hk⟩, he⟩
  have htwo : (2 : ℤ) ∈ evenIntegers := ⟨1, (mul_one 2).symm⟩
  have heone : e = 1 := mul_right_cancel₀ (by decide : (2 : ℤ) ≠ 0)
    (by simpa only [one_mul] using (he 2 htwo).1)
  have hdiv : (2 : ℤ) ∣ 1 := ⟨k, heone ▸ hk⟩
  exact (by decide : ¬ (2 : ℤ) ∣ 1) hdiv

theorem evenIntegersNotUnitalSubring : EvenIntegersNotUnitalSubring := by
  rintro ⟨T, hT⟩
  apply evenIntegersNoIdentity
  refine ⟨1, ?_, ?_⟩
  · rw [← hT]
    exact T.one_mem
  · intro x _
    exact ⟨one_mul x, mul_one x⟩

end D07.Ch08.Subring
