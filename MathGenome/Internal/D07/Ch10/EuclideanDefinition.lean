import MathGenome.Internal.Specs.D07.Ch10.EuclideanDefinition

/-! The precise Euclidean-domain definition and examples, K07.10.euclidean_definition.
No instance of Mathlib's stronger `EuclideanDomain` class is assumed or constructed.
-/

universe u

namespace D07.Ch10.EuclideanDefinition

open Specs.D07.Ch10.EuclideanDefinition

/-- Euclidean domains in the source's well-founded relation sense. -/
abbrev IsEuclidean : EuclideanPredicateType.{u} :=
  @Specs.D07.Ch10.EuclideanDefinition.IsEuclidean

/-- Quotient, remainder, and relation are additional chosen data. -/
abbrev EuclideanData : EuclideanDataType.{u} :=
  @Specs.D07.Ch10.EuclideanDefinition.EuclideanData

theorem divisionDataCharacterization : DivisionDataCharacterization.{u} := by
  intro R _ _
  constructor
  · rintro ⟨d⟩
    exact ⟨d.smaller, d.wellFounded, fun a b hb =>
      ⟨d.quotient a b, d.remainder a b, d.division a b hb, d.decrease a b hb⟩⟩
  · rintro ⟨smaller, hwf, hdiv⟩
    classical
    -- Total functions can be selected classically; their zero-divisor values
    -- carry no axioms, since only nonzero divisors occur in the definition.
    have htotal : ∀ a b : R, ∃ q r : R,
        b ≠ 0 → a = q * b + r ∧ (r = 0 ∨ smaller r b) := by
      intro a b
      by_cases hb : b = 0
      · exact ⟨0, 0, fun h => (h hb).elim⟩
      · obtain ⟨q, r, heq, hlt⟩ := hdiv a b hb
        exact ⟨q, r, fun _ => ⟨heq, hlt⟩⟩
    exact ⟨{
      smaller := smaller
      wellFounded := hwf
      quotient := fun a b => (htotal a b).choose
      remainder := fun a b => (htotal a b).choose_spec.choose
      division := fun a b hb => ((htotal a b).choose_spec.choose_spec hb).1
      decrease := fun a b hb => ((htotal a b).choose_spec.choose_spec hb).2 }⟩

theorem naturalSizeSuffices : NaturalSizeSuffices.{u} := by
  intro R _ _ size hdiv
  exact ⟨fun a b => size a < size b, (measure size).wf, hdiv⟩

theorem integerDivisionData : IntegerDivisionData := by
  refine ⟨{
    smaller := fun a b : ℤ => a.natAbs < b.natAbs
    wellFounded := (measure Int.natAbs).wf
    quotient := fun a b => a / b
    remainder := fun a b => a % b
    division := ?_
    decrease := ?_ }, rfl, rfl, rfl⟩
  · intro a b _
    exact (Int.ediv_mul_add_emod a b).symm
  · intro a b hb
    right
    apply Int.ofNat_lt.mp
    rw [Int.natAbs_of_nonneg (Int.emod_nonneg a hb)]
    exact Int.emod_lt a hb

theorem integersEuclidean : IntegersEuclidean := by
  obtain ⟨d, _⟩ := integerDivisionData
  exact (divisionDataCharacterization ℤ).mp ⟨d⟩

theorem fieldDivisionData : FieldDivisionData.{u} := by
  intro K _
  refine ⟨{
    smaller := fun _ _ : K => False
    wellFounded := ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩
    quotient := fun a b => a / b
    remainder := fun _ _ => 0
    division := ?_
    decrease := fun _ _ _ => Or.inl rfl }, rfl, rfl, rfl⟩
  intro a b hb
  rw [div_mul_cancel₀ a hb, add_zero]

theorem fieldsEuclidean : FieldsEuclidean.{u} := by
  intro K _
  obtain ⟨d, _⟩ := fieldDivisionData K
  exact (divisionDataCharacterization K).mp ⟨d⟩

end D07.Ch10.EuclideanDefinition
