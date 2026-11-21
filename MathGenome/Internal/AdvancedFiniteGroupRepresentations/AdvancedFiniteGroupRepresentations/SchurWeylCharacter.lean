import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.CharacteristicIsometry
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.MultiplicityTraceAverage
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.LengthBound
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SchurWeylCharacter

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
universe u
namespace AdvancedFiniteGroupRepresentations

/-- Specialize the characteristic identity to a literal finite alphabet. -/
theorem schur_frobenius_polynomial {n : ℕ} (p : Partition n)
    (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (hρ : InheritedSpechtAction p ρ) (d : ℕ) :
    schurPolynomial p d = ∑ ν : Partition n,
      (representationClassFunction ρ (cycleClass ν) / (zFactor ν : ℂ)) •
        partitionPowerSum d ν := by
  have h := congrArg (degreeSpecialization n d) (characteristic_specht p ρ hρ)
  simp only [characteristic, Specs.AdvancedFiniteGroupRepresentations.characteristic,
    map_sum, map_smul] at h
  change (∑ ν : Partition n,
    (representationClassFunction ρ (cycleClass ν) / (zFactor ν : ℂ)) •
      (stablePartitionPowerSum ν).val d) = (stableSchur p).val d at h
  simpa only [stablePartitionPowerSum_specialization, stableSchur_specialization] using h.symm

theorem schur_character_polynomial :
    Specs.AdvancedFiniteGroupRepresentations.schur_character_polynomialType := by
  intro n p ρ hρ d x
  change MvPolynomial.eval x (schurPolynomial p d) = _
  rw [schur_frobenius_polynomial p ρ hρ d]
  simp only [MvPolynomial.smul_eq_C_mul, map_sum, map_mul, MvPolynomial.eval_C]

/-- The usual diagonal calculation of the trace of every power. -/
theorem trace_pow_of_diagonal {V : Type u} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {d : ℕ} (b : Module.Basis (Fin d) ℂ V)
    (x : Fin d → ℂ) (g : LinearGroup V) (hg : ∀ i, g (b i) = x i • b i)
    (k : ℕ) :
    LinearMap.trace ℂ V (g.toLinearMap ^ k) = ∑ i, x i ^ k := by
  classical
  have hp (k : ℕ) (i : Fin d) : (g.toLinearMap ^ k) (b i) = x i ^ k • b i := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul]
      change x i ^ k • g (b i) = _
      rw [hg]
      simp [pow_succ, smul_smul, mul_comm]
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hp]
  simp

/-- Evaluation of a power sum is the trace of the corresponding power. -/
theorem eval_powerSum_diagonal {V : Type u} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {d : ℕ} (b : Module.Basis (Fin d) ℂ V)
    (x : Fin d → ℂ) (g : LinearGroup V) (hg : ∀ i, g (b i) = x i • b i)
    (k : ℕ) :
    MvPolynomial.eval x (powerSum d k) = LinearMap.trace ℂ V (g.toLinearMap ^ k) := by
  rw [trace_pow_of_diagonal b x g hg]
  simp [powerSum, Specs.AdvancedFiniteGroupRepresentations.powerSum]

/-- The complete cycle partition includes fixed points as parts of size one. -/
theorem cycleTraceProduct_diagonal {V : Type u} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {n d : ℕ} (b : Module.Basis (Fin d) ℂ V)
    (x : Fin d → ℂ) (g : LinearGroup V) (hg : ∀ i, g (b i) = x i • b i)
    (s : SymmetricGroup n) :
    cycleTraceProduct V s g = MvPolynomial.eval x (partitionPowerSum d (cyclePartition s)) := by
  classical
  change (((cyclePartition s).parts.map
    (fun k => LinearMap.trace ℂ V (g.toLinearMap ^ k))).prod) = _
  rw [Finset.prod_multiset_map_count]
  simp only [partitionPowerSum, Specs.AdvancedFiniteGroupRepresentations.partitionPowerSum,
    MvPolynomial.eval_prod, MvPolynomial.eval_pow,
    Specs.AdvancedFiniteGroupRepresentations.cycleMultiplicity]
  simp_rw [eval_powerSum_diagonal b x g hg]

/-- FR-D08: the diagonal character on the Hom-defined multiplicity space. -/
theorem schurWeyl_diagonal_character :
    Specs.AdvancedFiniteGroupRepresentations.schurWeyl_diagonal_characterType.{u} := by
  intro V _ _ _ n d p b x _hx g hg
  rw [multiplicity_trace_average V p (spechtRepresentation p) (fun _ _ => rfl) g,
    schur_character_polynomial p (spechtRepresentation p) (fun _ _ => rfl) d x]
  have hc (s : SymmetricGroup n) : (spechtRepresentation p).character s⁻¹ =
      representationClassFunction (spechtRepresentation p) (cycleClass (cyclePartition s)) := by
    rw [symmetricGroup_character_inv, cycleClass_cyclePartition]
    rfl
  simp_rw [hc, cycleTraceProduct_diagonal b x g hg]
  have h := sum_cyclePartition (fun ν =>
    representationClassFunction (spechtRepresentation p) (cycleClass ν) *
      MvPolynomial.eval x (partitionPowerSum d ν))
  calc
    _ = ∑ ν : Partition n, (zFactor ν : ℂ)⁻¹ *
        (representationClassFunction (spechtRepresentation p) (cycleClass ν) *
          MvPolynomial.eval x (partitionPowerSum d ν)) := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ν _
      rw [div_eq_mul_inv]
      ring

theorem schurWeyl_character_length_cutoff :
    Specs.AdvancedFiniteGroupRepresentations.schurWeyl_character_length_cutoffType.{u} := by
  intro V _ _ _ n d p b hp g x
  have hd : Module.finrank ℂ V = d := by
    simpa using Module.finrank_eq_card_basis b
  have hn : ¬ Nontrivial (TensorMultiplicity V p) := by
    rw [tensorMultiplicity_nonzero_iff V p, hd]
    exact Nat.not_le_of_gt hp
  let : Subsingleton (TensorMultiplicity V p) := not_nontrivial_iff_subsingleton.mp hn
  constructor
  · change LinearMap.trace ℂ (TensorMultiplicity V p) (tensorMultiplicityOperator V p g) = 0
    rw [Subsingleton.elim (tensorMultiplicityOperator V p g) 0, map_zero]
  · change MvPolynomial.eval x (schurPolynomial p d) = 0
    rw [schurPolynomial_eq_zero_of_length_gt p hp, map_zero]

theorem schurWeyl_empty_character :
    Specs.AdvancedFiniteGroupRepresentations.schurWeyl_empty_characterType.{u} := by
  intro V _ _ _ d g x
  obtain ⟨e, he⟩ := tensorMultiplicity_empty_line V
  have ho : tensorMultiplicityOperator V emptyPartition g = 1 := by
    apply LinearMap.ext
    intro f
    apply e.injective
    exact he g f
  have hf : Module.finrank ℂ (TensorMultiplicity V emptyPartition) = 1 := by
    simpa using e.finrank_eq
  constructor
  · change LinearMap.trace ℂ (TensorMultiplicity V emptyPartition)
      (tensorMultiplicityOperator V emptyPartition g) = 1
    rw [ho, LinearMap.trace_one, hf, Nat.cast_one]
  · change MvPolynomial.eval x (schurPolynomial emptyPartition d) = 1
    rw [empty_schurPolynomial, map_one]

end AdvancedFiniteGroupRepresentations
