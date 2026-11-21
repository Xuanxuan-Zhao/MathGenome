import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.Conventions

/-! Native complex C*-algebras and their original norms and involutions.
The definitions use the independent source conventions; states carry algebraic
linearity, positivity and normalization, with no assumed norm bound. -/

noncomputable section
namespace ExpandedFA.CStar.Conventions
universe u

abbrev nonnegativeScalars : Set ℂ := Spec.NonnegativeScalarsValue
abbrev CStarUnitization : Spec.CStarUnitizationType.{u} := Spec.CStarUnitizationValue
abbrev unitizationInclusion : Spec.UnitizationInclusionType.{u} := Spec.UnitizationInclusionValue
abbrev nonunitalSpectrum : Spec.NonunitalSpectrumType.{u} := Spec.NonunitalSpectrumValue
abbrev unitalSpectrum : Spec.UnitalSpectrumType.{u} := Spec.UnitalSpectrumValue
abbrev IsSelfAdjoint : Spec.SelfAdjointType.{u} := Spec.SelfAdjointValue
abbrev IsNormal : Spec.NormalType.{u} := Spec.NormalValue
abbrev IsUnitary : Spec.UnitaryType.{u} := Spec.UnitaryValue
abbrev IsPositive : Spec.PositiveType.{u} := Spec.PositiveValue
abbrev orderRelation : Spec.OrderRelationType.{u} := Spec.OrderRelationValue
abbrev IsPositiveFunctional : Spec.PositiveFunctionalType.{u} := Spec.PositiveFunctionalValue
abbrev State : Spec.StateType.{u} := Spec.StateValue
abbrev Operator : Spec.OperatorType.{u} := Spec.OperatorValue
abbrev operatorCStarStructure : Spec.OperatorStructureType.{u} := Spec.OperatorStructureValue

theorem native_cstar_axioms : Spec.NativeAxioms.{u} := by
  intro A _
  exact ⟨inferInstance, fun a => by simpa only [pow_two] using CStarRing.norm_star_mul_self (x := a),
    norm_star, star_mul, star_smul, star_star⟩

theorem selfAdjoint_identification : Spec.SelfAdjointIdentification.{u} := by
  intro A _ a
  rfl

theorem normal_identification : Spec.NormalIdentification.{u} := by
  intro A _ _ a
  exact ⟨fun h => h.star_comm_self.eq, fun h => ⟨h⟩⟩

theorem unitary_identification : Spec.UnitaryIdentification.{u} := by
  intro A _ _ a
  rfl

theorem operator_star_eq_adjoint : Spec.OperatorStarAdjoint.{u} := by
  intro H _ _ _ T
  rfl

theorem operator_algebra : Spec.OperatorAlgebra.{u} := by
  intro H _ _ _ S T x
  exact ⟨rfl, rfl, by simpa only [pow_two] using CStarRing.norm_star_mul_self (x := T)⟩

theorem unitization_native : Spec.UnitizationNative.{u} := by
  intro A _
  exact ⟨inferInstance, fun x => by simpa only [pow_two] using CStarRing.norm_star_mul_self (x := x),
    Unitization.isometry_inr⟩

theorem unitization_norm : Spec.UnitizationNorm.{u} := by
  intro A _ x
  simpa only [Algebra.algebraMap_eq_smul_one] using Unitization.norm_eq_sup x

/-- The first coordinate is a star-algebra isomorphism when the algebra is zero. -/
theorem zero_unitization_alternative : Spec.ZeroUnitizationAlternative.{u} := by
  intro A _ _
  let e : Unitization ℂ A ≃⋆ₐ[ℂ] ℂ :=
    { toFun := fun x => x.fst
      invFun := fun z => Unitization.inl z
      left_inv := fun x => Unitization.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ => rfl
      map_mul' := Unitization.fst_mul
      map_add' := Unitization.fst_add
      map_smul' := fun _ _ => rfl
      map_star' := fun _ => rfl }
  refine ⟨e, fun _ => rfl, ?_⟩
  intro x
  change ‖x.fst‖ = ‖x‖
  rw [Unitization.norm_eq_sup]
  have hT : algebraMap ℂ (A →L[ℂ] A) x.fst + ContinuousLinearMap.mul ℂ A x.snd = 0 :=
    Subsingleton.elim _ _
  simp only [hT, norm_zero, sup_eq_left.mpr (norm_nonneg _)]

/-- An already-unital algebra's larger unitization is its C*-direct sum with ℂ. -/
theorem unital_unitization_alternative : Spec.UnitalUnitizationAlternative.{u} := by
  intro A _
  let e : Unitization ℂ A ≃⋆ₐ[ℂ] (A × ℂ) :=
    { toFun := fun x => (x.snd + x.fst • (1 : A), x.fst)
      invFun := fun p => Unitization.mk (p.2, p.1 - p.2 • (1 : A))
      left_inv := by intro x; ext <;> simp
      right_inv := by intro p; ext <;> simp
      map_mul' := by
        intro x y
        ext <;> simp [Unitization.snd_mul, Unitization.fst_mul, add_mul, mul_add,
          smul_smul, add_assoc, add_comm, mul_comm]
      map_add' := by
        intro x y
        ext <;> simp [add_smul, add_assoc, add_left_comm]
      map_smul' := by intro z x; ext <;> simp [smul_add, smul_smul]
      map_star' := by intro x; ext <;> simp [star_add, star_smul] }
  refine ⟨e, fun _ => rfl, ?_⟩
  intro x
  change max ‖x.snd + x.fst • (1 : A)‖ ‖x.fst‖ = ‖x‖
  rw [Unitization.norm_eq_sup]
  have hm : algebraMap ℂ (A →L[ℂ] A) x.fst + ContinuousLinearMap.mul ℂ A x.snd =
      ContinuousLinearMap.mul ℂ A (x.snd + x.fst • (1 : A)) := by
    ext a
    simp [Algebra.algebraMap_eq_smul_one, add_comm]
  rw [hm, ContinuousLinearMap.opNorm_mul_apply, max_comm]

theorem mem_nonunitalSpectrum_iff : Spec.NonunitalSpectrumMembership.{u} := by
  intro A _ a z
  change (¬ IsUnit (algebraMap ℂ (Unitization ℂ A) z - _)) ↔ _
  rw [Algebra.algebraMap_eq_smul_one]

theorem nonunitalSpectrum_eq_banach : Spec.BanachSpectrumCompatibility.{u} := by
  intro A _ a
  exact AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv ℂ)
    (WithLp.toLp 1 (a : Unitization ℂ A))

theorem unital_spectrum_alternative : Spec.UnitalSpectrumAlternative.{u} := by
  intro A _ a
  change spectrum ℂ (a : Unitization ℂ A) = spectrum ℂ a ∪ {0}
  rw [← Unitization.quasispectrum_eq_spectrum_inr, quasispectrum_eq_spectrum_union_zero]

theorem zero_spectrum_alternative : Spec.ZeroSpectrumAlternative.{u} := by
  intro A _ _ a
  have ha : a = 0 := Subsingleton.elim _ _
  change spectrum ℂ (a : Unitization ℂ A) = {0}
  rw [ha, Unitization.inr_zero]
  exact spectrum.zero_eq

theorem positive_unital_identification : Spec.PositiveUnitalIdentification.{u} := by
  intro A _ a
  change (_root_.IsSelfAdjoint a ∧ Spec.NonunitalSpectrumValue A a ⊆ _) ↔ _
  rw [unital_spectrum_alternative A a]
  have hz : (0 : ℂ) ∈ Spec.NonnegativeScalarsValue := ⟨rfl, le_rfl⟩
  simp only [Set.union_subset_iff, Set.singleton_subset_iff, hz, and_true]

theorem state_identification : Spec.StateIdentification.{u} := by
  intro A _ φ
  constructor
  · rintro ⟨s, rfl⟩
    exact s.property
  · intro h
    exact ⟨⟨φ, h⟩, rfl⟩

theorem zero_algebra_no_states : Spec.ZeroAlgebraNoStates.{u} := by
  intro A _ _
  refine ⟨fun s => ?_⟩
  have h : s.val (1 : A) = 0 :=
    (congrArg s.val (Subsingleton.elim (1 : A) 0)).trans s.val.map_zero
  exact zero_ne_one (h.symm.trans s.property.2)

end ExpandedFA.CStar.Conventions
