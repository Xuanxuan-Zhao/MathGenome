import MathGenome.Internal.Specs.D07.Ch08.FieldIdeals
import MathGenome.Internal.D07.Ch08.DomainField
import MathGenome.Internal.D07.Ch08.FieldIdealsMatrixRingSimplicity
import MathGenome.Internal.D07.Ch08.UnitInIdeal

/-! Fields characterized by their two-sided ideals, and the necessity
of commutativity, as witnessed by the canonical matrix rings. -/

universe u

namespace D07.Ch08.FieldIdeals

open Specs.D07.Ch08.FieldIdeals

theorem nonzeroUnitsIffTrivialIdeals : NonzeroUnitsIffTrivialIdeals.{u} := by
  intro R _
  classical
  constructor
  · intro hunits I
    by_cases hzero : ∀ a : R, a ∈ I → a = 0
    · left
      apply TwoSidedIdeal.ext
      intro a
      constructor
      · intro ha
        simpa only [TwoSidedIdeal.mem_bot] using hzero a ha
      · intro ha
        have ha0 : a = 0 := by simpa only [TwoSidedIdeal.mem_bot] using ha
        rw [ha0]
        exact I.zero_mem
    · push Not at hzero
      obtain ⟨a, ha, hne⟩ := hzero
      right
      apply (TwoSidedIdeal.orderIsoIdeal (R := R)).injective
      change I.asIdeal = (⊤ : TwoSidedIdeal R).asIdeal
      rw [TwoSidedIdeal.top_asIdeal]
      exact (UnitInIdeal.leftIdealTopIffContainsUnit R I.asIdeal).mpr
        ⟨a, ha, hunits a hne⟩
  · intro hideals a hne
    have ha : a ∈ TwoSidedIdeal.span {a} :=
      TwoSidedIdeal.subset_span (Set.mem_singleton a)
    rcases hideals (TwoSidedIdeal.span {a}) with hbot | htop
    · rw [hbot] at ha
      have ha0 : a = 0 := by simpa only [TwoSidedIdeal.mem_bot] using ha
      exact (hne ha0).elim
    · exact (UnitInIdeal.principalIdealTopIffIsUnit R a).mp htop

theorem fieldCriterion : FieldCriterion.{u} := by
  intro R s _
  constructor
  · intro hfield
    have h := (DomainField.fieldCharacterization R s.toRing).mpr hfield
    exact (nonzeroUnitsIffTrivialIdeals R).mp h.2.1
  · intro hideals
    exact (DomainField.fieldCharacterization R s.toRing).mp
      ⟨zero_ne_one, (nonzeroUnitsIffTrivialIdeals R).mpr hideals, mul_comm⟩

theorem matrixCounterexample : MatrixCounterexample.{u} := by
  intro F _ n hn
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  obtain ⟨A, B, hA, hB, hAB⟩ :=
    FieldIdealsMatrixRingSimplicity.hasZeroDivisors F n hn
  exact ⟨⟨⟨A, 0, hA⟩⟩,
    FieldIdealsMatrixRingSimplicity.simplicity F n hnpos,
    MatrixRing.noncommutative F n hn,
    ⟨A, B, hA, hB, hAB⟩,
    FieldIdealsMatrixRingSimplicity.notDivisionRing F n hn⟩

end D07.Ch08.FieldIdeals
