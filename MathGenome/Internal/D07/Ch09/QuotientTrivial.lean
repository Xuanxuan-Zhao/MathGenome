import MathGenome.Internal.Specs.D07.Ch09.QuotientTrivial
import MathGenome.Internal.D07.Ch08.UnitInIdeal
import MathGenome.Internal.D07.Ch09.QuotientProjection
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
K07.09.quotient_trivial, paper.tex:1547–1554.
Triviality is equivalent to `1 = 0`, then to `1 ∈ I`, then to `I = ⊤`.
The zero-ideal isomorphism and its inverse act by the stated formulas.
There is no commutativity, nontriviality, or properness assumption.
-/

universe u

namespace D07.Ch09.QuotientTrivial

open Specs.D07.Ch09.QuotientTrivial

theorem trivial_iff_one_eq_zero : TrivialIffOneEqZero.{u} := by
  intro R _ I _
  exact subsingleton_iff_zero_eq_one.symm.trans eq_comm

theorem one_eq_zero_iff_one_mem : OneEqZeroIffOneMem.{u} := by
  intro R _ I _
  simpa only [map_one] using
    D07.Ch09.QuotientProjection.quotient_zero_iff_mem R I 1

theorem trivial_iff_top : TrivialIffTop.{u} := by
  intro R _ I _
  exact (trivial_iff_one_eq_zero R I).trans
    ((one_eq_zero_iff_one_mem R I).trans
      (D07.Ch08.UnitInIdeal.leftIdealTopIffOne R I).symm)

theorem nontrivial_iff_proper : NontrivialIffProper.{u} := by
  intro R _ I _
  exact Ideal.Quotient.nontrivial_iff

theorem zero_ideal_class_eq : ZeroIdealClassEq.{u} := by
  intro R _ a b
  simpa only [Ideal.mem_bot, sub_eq_zero] using
    D07.Ch09.QuotientProjection.quotient_eq_iff_sub_mem R (⊥ : Ideal R) a b

theorem zero_ideal_quotient_equivalence : ZeroIdealQuotientEquivalence.{u} := by
  intro R _
  exact ⟨RingEquiv.quotientBot R, RingEquiv.quotientBot_mk,
    RingEquiv.quotientBot_symm_mk⟩

end D07.Ch09.QuotientTrivial
