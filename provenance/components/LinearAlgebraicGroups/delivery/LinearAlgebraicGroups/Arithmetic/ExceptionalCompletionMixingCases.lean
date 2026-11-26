import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalCompletionMixingCases
import Specs.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
import LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRadicalGeneration
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
set_option autoImplicit false

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalCompletionMixingCases

open Specs.Arithmetic.ExceptionalCompletionMixingCases (ExceptionalMixingCases)
open Specs.Arithmetic.LocalProjectedClosure (LocalNormalClosure FiniteCovolumeSubgroup)
open Specs.Arithmetic.LocalQuotientMixing (IsExceptionalCase MixingCases)
open Specs.ExceptionalLocalRadicalGeneration (HasAbsoluteTypeE)

open private exceptionalFormCases from
  LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRadicalGeneration

/-- The marked local classification places the original exceptional group
among the groups in the local mixing statement. -/
theorem exceptionalCompletionMixingCases_conditional
    (_normalClosure : LocalNormalClosure.{u})
    (_finiteCovolume : FiniteCovolumeSubgroup.{u}) :
    ExceptionalMixingCases.{u} := by
  intro F _ _ _ _ J hsimple hsc htype
  obtain ⟨n, hn, hJ⟩ : ∃ n : ℕ, (n = 6 ∨ n = 7 ∨ n = 8) ∧ HasAbsoluteTypeE J n := by
    rcases htype with h₆ | h₇ | h₈
    · exact ⟨6, Or.inl rfl, h₆⟩
    · exact ⟨7, Or.inr (Or.inl rfl), h₇⟩
    · exact ⟨8, Or.inr (Or.inr rfl), h₈⟩
  have ofExceptional (h : IsExceptionalCase J) : MixingCases J :=
    .inr (.inr (.inr (.inr ⟨hsc, .inl h⟩)))
  rcases exceptionalFormCases hsimple hsc n hn hJ with
    ⟨_, hsplit⟩ | ⟨h₆, hinner, hnonsplit, _⟩ | ⟨h₇, hinner, hnonsplit, _⟩ | ⟨h₆, houter, _⟩
  · exact .inl ⟨hsplit, hsc⟩
  · subst n
    exact ofExceptional (.inl ⟨hJ, hinner, hnonsplit⟩)
  · subst n
    exact ofExceptional (.inr (.inl ⟨hJ, hinner, hnonsplit⟩))
  · subst n
    exact ofExceptional (.inr (.inr ⟨hJ, houter⟩))

end LinearAlgebraicGroups.Arithmetic.ExceptionalCompletionMixingCases

universe v8_closure_55004833504e1daa_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalCompletionMixingCases».«exceptionalCompletionMixingCases» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«ExceptionalCompletionMixingCases».«ExceptionalMixingCases».{v8_closure_55004833504e1daa_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalCompletionMixingCases».«exceptionalCompletionMixingCases_conditional».{v8_closure_55004833504e1daa_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localNormalClosure».{v8_closure_55004833504e1daa_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localProjectedClosure».{v8_closure_55004833504e1daa_u0})
