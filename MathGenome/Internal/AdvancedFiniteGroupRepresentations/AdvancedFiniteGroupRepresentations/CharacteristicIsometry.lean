import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.StableSymmetricFunctions
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.FrobeniusCharacterFormula
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CharacteristicIsometry

noncomputable section
open scoped BigOperators DirectSum
namespace AdvancedFiniteGroupRepresentations

abbrev ClassFunction := Specs.AdvancedFiniteGroupRepresentations.ClassFunction
abbrev cycleClass := @Specs.AdvancedFiniteGroupRepresentations.cycleClass
abbrev characteristic := @Specs.AdvancedFiniteGroupRepresentations.characteristic
abbrev classFunctionPairing := @Specs.AdvancedFiniteGroupRepresentations.classFunctionPairing
abbrev representationClassFunction := @Specs.AdvancedFiniteGroupRepresentations.representationClassFunction

theorem cycleClass_spec {n : ℕ} (ν : Partition n) :
    conjugacyCyclePartition (cycleClass ν) = ν :=
  Classical.epsilon_spec ((conjugacyCyclePartition_bijective n).2 ν)

theorem cycleClass_cyclePartition {n : ℕ} (σ : SymmetricGroup n) :
    cycleClass (cyclePartition σ) = ConjClasses.mk σ :=
  (conjugacyCyclePartition_bijective n).1 (cycleClass_spec _)

theorem cycleClass_label {n : ℕ} (c : ConjClasses (SymmetricGroup n)) :
    cycleClass (conjugacyCyclePartition c) = c :=
  (conjugacyCyclePartition_bijective n).1 (cycleClass_spec _)

def classFunctionCoordinates (n : ℕ) : ClassFunction n ≃ₗ[ℂ] (Partition n →₀ ℂ) where
  toFun f := Finsupp.equivFunOnFinite.symm (fun ν => f (cycleClass ν) / (zFactor ν : ℂ))
  invFun c k := (zFactor (conjugacyCyclePartition k) : ℂ) * c (conjugacyCyclePartition k)
  left_inv f := by
    funext k
    change (zFactor (conjugacyCyclePartition k) : ℂ) *
      (f (cycleClass (conjugacyCyclePartition k)) / (zFactor (conjugacyCyclePartition k) : ℂ)) = f k
    rw [cycleClass_label]
    have hz : (zFactor (conjugacyCyclePartition k) : ℂ) ≠ 0 := by
      exact_mod_cast (zFactor_pos (conjugacyCyclePartition k)).ne'
    field_simp
  right_inv c := by
    ext ν
    change ((zFactor (conjugacyCyclePartition (cycleClass ν)) : ℂ) *
      c (conjugacyCyclePartition (cycleClass ν))) / (zFactor ν : ℂ) = c ν
    rw [cycleClass_spec]
    have hz : (zFactor ν : ℂ) ≠ 0 := by exact_mod_cast (zFactor_pos ν).ne'
    field_simp
  map_add' f g := by ext ν; simp [add_div]
  map_smul' a f := by ext ν; simp [mul_div_assoc]

theorem characteristic_eq_synthesis {n : ℕ} (f : ClassFunction n) :
    characteristic f = powerSumSynthesis n (classFunctionCoordinates n f) := by
  classical
  change _ = Finsupp.linearCombination ℂ stablePartitionPowerSum _
  rw [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype (classFunctionCoordinates n f)
    (fun ν c => c • stablePartitionPowerSum ν) (fun _ => zero_smul ℂ _)]
  rfl

theorem characteristic_linearEquiv (n : ℕ) :
    ∃ e : ClassFunction n ≃ₗ[ℂ] stableDegree n, ∀ f, e f = characteristic f := by
  refine ⟨(classFunctionCoordinates n).trans (powerSumCoordinateEquiv n).symm, ?_⟩
  intro f
  exact (characteristic_eq_synthesis f).symm

theorem characteristic_coordinates {n : ℕ} (f : ClassFunction n) :
    powerSumCoordinateEquiv n (characteristic f) = classFunctionCoordinates n f := by
  rw [characteristic_eq_synthesis]
  exact (powerSumCoordinateEquiv n).apply_symm_apply _

theorem classFunctionPairing_eq_sum {n : ℕ} (f g : ClassFunction n) :
    classFunctionPairing f g = ∑ ν : Partition n,
      (zFactor ν : ℂ)⁻¹ * f (cycleClass ν) * star (g (cycleClass ν)) := by
  have h := sum_cyclePartition (fun ν => f (cycleClass ν) * star (g (cycleClass ν)))
  simp_rw [cycleClass_cyclePartition] at h
  simpa only [classFunctionPairing, Specs.AdvancedFiniteGroupRepresentations.classFunctionPairing,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin, mul_assoc] using h

theorem characteristic_isometry {n : ℕ} (f g : ClassFunction n) :
    hallPairing (DirectSum.of (fun n => stableDegree n) n (characteristic f))
      (DirectSum.of (fun n => stableDegree n) n (characteristic g)) = classFunctionPairing f g := by
  classical
  rw [hallPairing_of_left, DirectSum.of_eq_same, degreeHallPairing,
    characteristic_coordinates, characteristic_coordinates, classFunctionPairing_eq_sum]
  apply Finset.sum_congr rfl
  intro ν _
  change (f (cycleClass ν) / (zFactor ν : ℂ)) * star (g (cycleClass ν) / (zFactor ν : ℂ)) *
    (zFactor ν : ℂ) = _
  rw [star_div₀, star_natCast]
  have hz : (zFactor ν : ℂ) ≠ 0 := by exact_mod_cast (zFactor_pos ν).ne'
  field_simp

/-- The actual trace, evaluated on the conjugacy class labelled by ν. -/
theorem representationClassFunction_cycleClass {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (SymmetricGroup n) V)
    (ν : Partition n) :
    representationClassFunction ρ (cycleClass ν) = ρ.character (cycleRepresentative ν) := by
  conv_lhs => rw [← cycleRepresentative_type ν, cycleClass_cyclePartition]
  rfl

theorem stableAlternatingCoordinates_schur {n r : ℕ} (hr : n ≤ r)
    (lam μ : Partition n) :
    stableAlternatingCoordinates n r (stableSchur lam) μ = if μ = lam then 1 else 0 := by
  classical
  change naturalCoefficient (shiftedPartition r μ)
    (vandermonde r * (stableSchur lam).val r) = _
  rw [stableSchur_specialization, schurPolynomial_characterization lam r
    ((partition_length_le_size lam).trans hr)]
  change naturalCoefficient (shiftedPartition r μ) (alternant (shiftedPartition r lam)) = _
  rw [naturalCoefficient_alternant _ _ (shiftedPartition_strictAnti μ) (shiftedPartition_strictAnti lam)]
  have he : shiftedPartition r μ = shiftedPartition r lam ↔ μ = lam :=
    ⟨fun h => partition_eq_of_diagram_eq μ lam (diagram_eq_of_shiftedPartition_eq μ lam
      ((partition_length_le_size μ).trans hr) ((partition_length_le_size lam).trans hr) h),
      fun h => congrArg (shiftedPartition r) h⟩
  simp only [he]

theorem characteristic_specht {n : ℕ} (lam : Partition n)
    (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule lam))
    (hρ : InheritedSpechtAction lam ρ) :
    characteristic (representationClassFunction ρ) = stableSchur lam := by
  classical
  rw [inheritedSpechtAction_eq lam ρ hρ]
  apply stableAlternatingCoordinates_injective n (n+1) (by omega)
  ext μ
  rw [characteristic_eq_synthesis, stableAlternatingCoordinates_synthesis]
  rw [stableAlternatingCoordinates_schur (by omega)]
  change (∑ ν : Partition n, alternatingPowerSumMatrix n (n+1) μ ν *
    ((representationClassFunction (spechtRepresentation lam) (cycleClass ν)) / (zFactor ν : ℂ))) = _
  have hc (ν : Partition n) : alternatingPowerSumMatrix n (n+1) μ ν =
      spechtCycleCharacter μ ν :=
    frobeniusCoefficient_eq_spechtCycleCharacter (n+1) (by omega) (by omega) μ ν
  simp_rw [hc, representationClassFunction_cycleClass]
  have h := spechtCycleCharacter_orthogonal μ lam
  convert h using 1
  apply Finset.sum_congr rfl
  intro ν _
  change spechtCycleCharacter μ ν * (spechtCycleCharacter lam ν / (zFactor ν : ℂ)) = _
  ring

end AdvancedFiniteGroupRepresentations
