import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.YoungPermutationCharacter
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SchurTableauFormula
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.CharacteristicIsometry
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.YoungRule

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

abbrev orderedYoungMultiplicity := @Specs.AdvancedFiniteGroupRepresentations.orderedYoungMultiplicity
abbrev semistandardContentCount := @Specs.AdvancedFiniteGroupRepresentations.semistandardContentCount

/-- Finite-alphabet specialization of the characteristic of a Specht module.
There is no cutoff on the alphabet size. -/
theorem schurPolynomial_eq_character_sum {n : ℕ} (lam : Partition n) (r : ℕ)
    (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule lam))
    (hρ : InheritedSpechtAction lam ρ) :
    schurPolynomial lam r = ∑ ν : Partition n,
      (ρ.character (cycleRepresentative ν) / (zFactor ν : ℂ)) • partitionPowerSum r ν := by
  have h := congrArg (degreeSpecialization n r) (characteristic_specht lam ρ hρ)
  change degreeSpecialization n r
    (∑ ν : Partition n, (representationClassFunction ρ (cycleClass ν) / (zFactor ν : ℂ)) •
      stablePartitionPowerSum ν) = degreeSpecialization n r (stableSchur lam) at h
  simp only [map_sum, map_smul] at h
  change (∑ ν : Partition n, (representationClassFunction ρ (cycleClass ν) / (zFactor ν : ℂ)) •
    (stablePartitionPowerSum ν).val r) = (stableSchur lam).val r at h
  simpa only [stablePartitionPowerSum_specialization, stableSchur_specialization,
    representationClassFunction_cycleClass] using h.symm

/-- The trace pairing computes the dimension of the ordered-row Hom space. -/
theorem orderedYoungMultiplicity_eq_character_sum {n r : ℕ} (lam : Partition n)
    (μ : Fin r → ℕ)
    (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule lam)) :
    (orderedYoungMultiplicity lam μ ρ : ℂ) =
      ∑ ν : Partition n, (zFactor ν : ℂ)⁻¹ *
        (naturalCoefficient μ (partitionPowerSum r ν) *
          ρ.character (cycleRepresentative ν)) := by
  classical
  let : Invertible (Nat.card (SymmetricGroup n) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  calc
    (orderedYoungMultiplicity lam μ ρ : ℂ) =
        (Nat.card (SymmetricGroup n) : ℂ)⁻¹ *
          ∑ g : SymmetricGroup n, (orderedRowRepresentation μ).character g *
            ρ.character g⁻¹ :=
      (Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ
        (orderedRowRepresentation μ)).symm
    _ = (Nat.card (SymmetricGroup n) : ℂ)⁻¹ *
        ∑ g : SymmetricGroup n,
          naturalCoefficient μ (partitionPowerSum r (cyclePartition g)) *
            ρ.character (cycleRepresentative (cyclePartition g)) := by
      apply congrArg (fun z : ℂ => (Nat.card (SymmetricGroup n) : ℂ)⁻¹ * z)
      apply Finset.sum_congr rfl
      intro g _
      rw [symmetricGroup_character_inv]
      change youngPermutationCharacter μ g * _ = _
      rw [young_permutation_character_of_permutation]
      exact congrArg (fun z : ℂ => naturalCoefficient μ
        (partitionPowerSum r (cyclePartition g)) * z)
          (character_eq_of_cyclePartition_eq ρ _ _ (cycleRepresentative_type _).symm)
    _ = _ := sum_cyclePartition (fun ν : Partition n =>
      naturalCoefficient μ (partitionPowerSum r ν) * ρ.character (cycleRepresentative ν))

theorem young_rule_coefficient : Specs.AdvancedFiniteGroupRepresentations.young_rule_coefficientType := by
  intro n r lam μ _hμ ρ hρ
  change (orderedYoungMultiplicity lam μ ρ : ℂ) =
    naturalCoefficient μ (schurPolynomial lam r)
  rw [orderedYoungMultiplicity_eq_character_sum, schurPolynomial_eq_character_sum lam r ρ hρ]
  change _ = (∑ ν : Partition n,
    (ρ.character (cycleRepresentative ν) / (zFactor ν : ℂ)) • partitionPowerSum r ν).coeff
      (Finsupp.equivFunOnFinite.symm μ)
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [MvPolynomial.coeff_smul]
  change _ = _ * naturalCoefficient μ (partitionPowerSum r ν)
  ring

/-- Coefficients of the tableau generating polynomial count tableaux with
exactly the specified content, even for an empty alphabet. -/
theorem schur_coefficient_eq_content_count {n r : ℕ} (lam : Partition n)
    (μ : Fin r → ℕ) :
    naturalCoefficient μ (schurPolynomial lam r) = (semistandardContentCount lam μ : ℂ) := by
  classical
  rw [schurPolynomial_eq_tableauSum, tableauSum_eq_sum_tableauWeight]
  change (∑ T : SemistandardFilling lam r, tableauWeight T).coeff
    (Finsupp.equivFunOnFinite.symm μ) = _
  rw [MvPolynomial.coeff_sum]
  simp_rw [tableauWeight_eq_monomial, MvPolynomial.coeff_monomial]
  simp [semistandardContentCount, Specs.AdvancedFiniteGroupRepresentations.semistandardContentCount,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem young_rule_tableaux : Specs.AdvancedFiniteGroupRepresentations.young_rule_tableauxType := by
  intro n r lam μ hμ ρ hρ
  have h := (young_rule_coefficient lam μ hμ ρ hρ).trans
    (schur_coefficient_eq_content_count lam μ)
  exact_mod_cast h

end AdvancedFiniteGroupRepresentations
