import MathGenome.Internal.Specs.D07.Ch10.UfdDefinition

/-! The UFD definition, its unit convention, and its boundary examples.
All factor multisets are finite, with multiplicity. The ambient ring and
domain assumptions are retained even though some library lemmas apply to
more general multiplicative structures. -/

universe u

namespace D07.Ch10.UfdDefinition

open Specs.D07.Ch10.UfdDefinition

/-- A UFD is a commutative nontrivial domain whose multiplicative monoid
has unique factorization. We retain Mathlib's canonical predicate. -/
def IsUfd (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  UniqueFactorizationMonoid R

theorem ufdCharacterization : UfdCharacterization.{u} := by
  intro R _ _
  constructor
  · intro h
    let _ : UniqueFactorizationMonoid R := h
    refine ⟨?_, fun _ _ hs ht hst => UniqueFactorizationMonoid.factors_unique hs ht hst⟩
    intro a ha hnu
    obtain ⟨s, hs, heq, hne⟩ := (WfDvdMonoid.not_isUnit_iff_exists_factors_eq a ha).mp hnu
    exact ⟨s, hne, hs, heq⟩
  · rintro ⟨hex, huniq⟩
    refine UniqueFactorizationMonoid.of_existsUnique_irreducible_factors ?_ huniq
    intro a ha
    by_cases hu : IsUnit a
    · refine ⟨0, fun _ hp => (Multiset.notMem_zero _ hp).elim, ?_⟩
      simpa only [Multiset.prod_zero] using (associated_one_iff_isUnit.mpr hu).symm
    · obtain ⟨s, _, hs, heq⟩ := hex a ha hu
      exact ⟨s, hs, Associated.of_eq heq⟩

private theorem associated_iff_leading_unit {R : Type u} [CommRing R] [IsDomain R]
    (a b : R) : Associated a b ↔ ∃ v : Rˣ, b = (v : R) * a := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, by simpa only [mul_comm] using hv.symm⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by simpa only [mul_comm] using hv.symm⟩

theorem leadingUnitCharacterization : LeadingUnitCharacterization.{u} := by
  intro R _ _
  constructor
  · intro h
    let _ : UniqueFactorizationMonoid R := h
    constructor
    · intro a ha
      obtain ⟨s, hs, hassoc⟩ := WfDvdMonoid.exists_factors a ha
      obtain ⟨v, hv⟩ := (associated_iff_leading_unit s.prod a).mp hassoc
      exact ⟨v, s, hs, hv⟩
    · intro v w s t hs ht heq
      apply UniqueFactorizationMonoid.factors_unique hs ht
      exact ((associated_iff_leading_unit s.prod ((v : R) * s.prod)).mpr ⟨v, rfl⟩).trans
        ((Associated.of_eq heq).trans
          ((associated_iff_leading_unit t.prod ((w : R) * t.prod)).mpr ⟨w, rfl⟩).symm)
  · rintro ⟨hex, huniq⟩
    refine UniqueFactorizationMonoid.of_existsUnique_irreducible_factors ?_ ?_
    · intro a ha
      obtain ⟨v, s, hs, hv⟩ := hex a ha
      exact ⟨s, hs, (associated_iff_leading_unit s.prod a).mpr ⟨v, hv⟩⟩
    · intro s t hs ht hassoc
      obtain ⟨v, hv⟩ := (associated_iff_leading_unit s.prod t.prod).mp hassoc
      apply huniq v 1 s t hs ht
      simpa only [Units.val_one, one_mul] using hv.symm

theorem chosenRepresentatives : ChosenRepresentatives.{u} := by
  intro R _ _ _ rep hrep a ha
  obtain ⟨s, hs, hsa⟩ := WfDvdMonoid.exists_factors a ha
  have hprod : Associated s.prod (s.map rep).prod := by
    clear hsa
    induction s using Multiset.induction_on with
    | empty => simp only [Multiset.map_zero, Multiset.prod_zero]; rfl
    | cons p s ih =>
      simp only [Multiset.prod_cons, Multiset.map_cons]
      exact (hrep p (hs p (Multiset.mem_cons_self _ _))).mul_mul
        (ih (fun q hq => hs q (Multiset.mem_cons_of_mem hq)))
  obtain ⟨v, hv⟩ := (associated_iff_leading_unit (s.map rep).prod a).mp
    (hprod.symm.trans hsa)
  refine ⟨v, s, hs, ?_, hv⟩
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hq
  exact (hrep p (hs p hp)).irreducible (hs p hp)

theorem zeroBoundary : ZeroBoundary.{u} := by
  intro R _ _
  rintro ⟨v, s, hs, heq⟩
  have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun hp => (hs 0 hp).ne_zero rfl)
  exact (mul_ne_zero (Units.ne_zero v) hprod) heq.symm

theorem unitBoundary : UnitBoundary.{u} := by
  intro R _ _
  constructor
  · intro a
    simp only [Multiset.prod_zero, mul_one]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v, hv.symm⟩
    · rintro ⟨v, rfl⟩
      exact v.isUnit
  · intro a v s hs heq
    constructor
    · intro hu
      apply Multiset.eq_zero_of_forall_notMem
      intro p hp
      apply (hs p hp).not_isUnit
      apply isUnit_of_dvd_unit ?_ hu
      rw [heq]
      exact (Multiset.dvd_prod hp).trans (dvd_mul_left s.prod (v : R))
    · intro hz
      rw [heq, hz, Multiset.prod_zero, mul_one]
      exact v.isUnit

theorem fieldIsUfd : FieldIsUfd.{u} := by
  intro F _
  apply (ufdCharacterization F).mpr
  constructor
  · intro a ha hnu
    exact (hnu (isUnit_iff_ne_zero.mpr ha)).elim
  · intro s t hs ht _
    have hempty (s : Multiset F) (hs : ∀ p ∈ s, Irreducible p) : s = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro p hp
      exact (hs p hp).not_isUnit (isUnit_iff_ne_zero.mpr (hs p hp).ne_zero)
    rw [hempty s hs, hempty t ht]
    exact Multiset.rel_zero_left.mpr rfl

end D07.Ch10.UfdDefinition
