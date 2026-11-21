import MathGenome.Internal.Specs.D07.Ch08.IdealDefinition
import MathGenome.Internal.D07.Ch08.MatrixRing

/-! K07.08.ideal_definition: left, right, and two-sided ideals. -/

universe u v

namespace D07.Ch08.IdealDefinition

open Specs.D07.Ch08.IdealDefinition

theorem leftIdealCharacterization : LeftIdealCharacterization.{u} := by
  intro R _ H
  constructor
  · intro h
    let I : Ideal R := {
      carrier := H
      zero_mem' := H.zero_mem
      add_mem' := H.add_mem
      smul_mem' := h }
    exact ⟨I, rfl⟩
  · rintro ⟨I, rfl⟩ r a ha
    exact I.mul_mem_left r ha

theorem rightIdealCharacterization : RightIdealCharacterization.{u} := by
  intro R _ H
  constructor
  · intro h
    let I : Ideal Rᵐᵒᵖ := {
      carrier := {x | MulOpposite.unop x ∈ H}
      zero_mem' := H.zero_mem
      add_mem' := fun ha hb => H.add_mem ha hb
      smul_mem' := fun r a ha => h (MulOpposite.unop a) (MulOpposite.unop r) ha }
    exact ⟨I, fun _ => Iff.rfl⟩
  · rintro ⟨I, hI⟩ a r ha
    exact (hI (a * r)).mp (I.mul_mem_left (MulOpposite.op r) ((hI a).mpr ha))

theorem twoSidedIdealCharacterization : TwoSidedIdealCharacterization.{u} := by
  intro R _ I
  constructor
  · intro h
    exact ⟨fun r a ha => I.mul_mem_left r ha,
      fun a r ha => h.mul_mem_of_left r ha⟩
  · intro h
    exact ⟨fun r ha => h.2 _ r ha⟩

theorem commutativeCoincidence : CommutativeCoincidence.{u} := by
  intro R _ H
  have h : IsLeftIdeal H ↔ IsRightIdeal H := by
    constructor
    · intro h a r ha
      rw [mul_comm]
      exact h r a ha
    · intro h r a ha
      rw [mul_comm]
      exact h a r ha
  exact ⟨h, ⟨fun hL => ⟨hL, h.mp hL⟩, fun hT => hT.1⟩⟩

theorem properIdealNotSubring : ProperIdealNotSubring.{u} := by
  intro R _ H hside hproper
  rintro ⟨S, hS⟩
  have h1 : (1 : R) ∈ H := by
    rw [← hS]
    exact S.one_mem
  apply hproper
  apply AddSubgroup.ext
  intro a
  constructor
  · intro _
    trivial
  · intro _
    rcases hside with hL | hR
    · simpa only [mul_one] using hL a 1 h1
    · simpa only [one_mul] using hR 1 a h1

theorem columnLeftIdeal : ColumnLeftIdeal.{u} := by
  intro R _ n j
  have h : IsLeftIdeal (columnSubgroup (R := R) j) := by
    intro B A hA i k hk
    change ∑ l, B i l * A l k = 0
    apply Finset.sum_eq_zero
    intro l _
    rw [hA l k hk, mul_zero]
  exact ⟨h, (leftIdealCharacterization (Matrix (Fin n) (Fin n) R) _).mp h⟩

theorem columnMatrixUnitWitnesses : ColumnMatrixUnitWitnesses.{u} := by
  intro R _ _ n i j hij
  refine ⟨?_, ?_, ?_⟩
  · intro a k hk
    simp [Ne.symm hk]
  · exact (D07.Ch08.MatrixRing.matrixUnitProduct R n i j j i).trans (ite_eq_left rfl)
  · intro h
    have hentry := h i i hij
    simp at hentry

theorem columnNotRight : ColumnNotRight.{u} := by
  intro R _ _ n i j hij
  obtain ⟨hmem, hprod, hnot⟩ := columnMatrixUnitWitnesses R n i j hij
  have h : ¬ IsRightIdeal (columnSubgroup (R := R) j) := by
    intro hright
    apply hnot
    rw [← hprod]
    exact hright _ _ hmem
  exact ⟨h, fun htwo => h htwo.2⟩

theorem columnNotKernel : ColumnNotKernel.{u, v} := by
  intro R _ _ n i j hij S _
  rintro ⟨f, hf⟩
  apply (columnNotRight R n i j hij).1
  intro A B hA
  apply (hf (A * B)).mpr
  rw [map_mul, (hf A).mp hA, zero_mul]

end D07.Ch08.IdealDefinition
