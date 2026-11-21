import MathGenome.Internal.Specs.D07.Ch01.FreeGroupUniversalPropertyReducedWords

/-!
# Unique reduced signed words in the canonical free group

The canonical free group is the quotient of signed lists by adjacent inverse
cancellation. Mathlib's reduction theorem supplies a finite cancellation path
to a reduced word and proves that equal quotient elements have the same
reduction. We identify its predicates explicitly with the source's alphabet
and no-adjacent-inverse condition, then prove normal form and operation laws.
All statements allow arbitrary generator types, including empty ones.
-/

namespace D07.Ch01.FreeGroupUniversalPropertyReducedWords

open Specs.D07.Ch01.FreeGroupUniversalPropertyReducedWords

universe u

theorem signed_letters : SignedLetters.{u} := by
  intro S s
  constructor
  · rfl
  · rw [FreeGroup.of, FreeGroup.inv_mk]
    rfl

theorem reduced_iff : ReducedIff.{u} := by
  intro S w
  constructor
  · intro h p q s b hw
    exact h.not_step (hw ▸ (FreeGroup.Red.Step.not (L₁ := p) (L₂ := q)))
  · intro h
    apply FreeGroup.IsReduced.of_forall_not_step
    intro z hz
    cases hz with
    | not => exact h _ _ _ _ rfl

theorem cancellation_step : CancellationStep.{u} := by
  intro S v w
  constructor
  · intro h
    cases h with
    | not => exact ⟨_, _, _, _, rfl, rfl⟩
  · rintro ⟨p, q, s, b, rfl, rfl⟩
    exact FreeGroup.Red.Step.not

theorem unique_reduced_representative : UniqueReducedRepresentative.{u} := by
  intro S x
  classical
  refine ⟨x.toWord, ⟨(reduced_iff S _).mp FreeGroup.isReduced_toWord,
    FreeGroup.mk_toWord⟩, ?_⟩
  intro w hw
  have hr := (reduced_iff S w).mpr hw.1
  have he := congrArg FreeGroup.toWord hw.2
  simpa only [FreeGroup.toWord_mk, hr.reduce_eq] using he

theorem reduction_normal_form : ReductionNormalForm.{u} := by
  intro S w
  classical
  refine ⟨FreeGroup.reduce w, FreeGroup.reduce.red, ?_, FreeGroup.reduce.self, ?_⟩
  · exact (reduced_iff S _).mp (FreeGroup.IsReduced.of_reduce_eq FreeGroup.reduce.idem)
  · intro z hz hred
    have hr := (reduced_iff S z).mpr hred
    exact (hr.red_iff_eq.mp (FreeGroup.reduce.rev hz)).symm

theorem multiplication_normal_form : MultiplicationNormalForm.{u} := by
  intro S x y v w _ hv _ hw
  obtain ⟨r, hpath, hr, he, _⟩ := reduction_normal_form S (v ++ w)
  have hprod : FreeGroup.mk (v ++ w) = x * y := by
    rw [← FreeGroup.mul_mk, hv, hw]
  refine ⟨r, ⟨hr, he.trans hprod, hpath⟩, ?_⟩
  intro z hz
  obtain ⟨n, _, hn⟩ := unique_reduced_representative S (x * y)
  exact (hn z ⟨hz.1, hz.2.1⟩).trans (hn r ⟨hr, he.trans hprod⟩).symm

theorem inverse_normal_form : InverseNormalForm.{u} := by
  intro S w hw
  classical
  have hr := (reduced_iff S w).mpr hw
  change Reduced (FreeGroup.invRev w) ∧
    FreeGroup.mk (FreeGroup.invRev w) = (FreeGroup.mk w)⁻¹
  constructor
  · apply (reduced_iff S _).mp
    apply FreeGroup.IsReduced.of_reduce_eq
    rw [FreeGroup.reduce_invRev, hr.reduce_eq]
  · exact FreeGroup.inv_mk.symm

theorem empty_word : EmptyWord.{u} := by
  intro S
  exact ⟨(reduced_iff S []).mp FreeGroup.IsReduced.nil, rfl⟩

theorem empty_generators : EmptyGenerators.{u} := by
  intro S _
  constructor
  · intro w
    cases w with
    | nil => rfl
    | cons a _ => exact isEmptyElim a.1
  · intro x
    exact Subsingleton.elim x 1

end D07.Ch01.FreeGroupUniversalPropertyReducedWords
