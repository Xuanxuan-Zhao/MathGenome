import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.CharacteristicIsometry
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CharacteristicMultiplication

noncomputable section
open scoped BigOperators DirectSum
open Classical
namespace AdvancedFiniteGroupRepresentations

abbrev blockEmbedding := Specs.AdvancedFiniteGroupRepresentations.blockEmbedding
abbrev blockYoungSubgroup := Specs.AdvancedFiniteGroupRepresentations.blockYoungSubgroup
abbrev externalClassFunction := @Specs.AdvancedFiniteGroupRepresentations.externalClassFunction
abbrev ordinaryInduction := @Specs.AdvancedFiniteGroupRepresentations.ordinaryInduction
abbrev inducedExternal := @Specs.AdvancedFiniteGroupRepresentations.inducedExternal

theorem blockEmbedding_apply_left {a b : ℕ} (σ : SymmetricGroup a)
    (τ : SymmetricGroup b) (i : Fin a) :
    blockEmbedding a b (σ, τ) (Fin.castAdd b i) = Fin.castAdd b (σ i) := by
  simp [blockEmbedding, Specs.AdvancedFiniteGroupRepresentations.blockEmbedding,
    Equiv.permCongr_apply]

theorem blockEmbedding_apply_right {a b : ℕ} (σ : SymmetricGroup a)
    (τ : SymmetricGroup b) (i : Fin b) :
    blockEmbedding a b (σ, τ) (Fin.natAdd a i) = Fin.natAdd a (τ i) := by
  simp [blockEmbedding, Specs.AdvancedFiniteGroupRepresentations.blockEmbedding,
    Equiv.permCongr_apply]

theorem blockEmbedding_injective (a b : ℕ) : Function.Injective (blockEmbedding a b) :=
  finSumFinEquiv.permCongrHom.injective.comp Equiv.Perm.sumCongrHom_injective

/-- Relabeling does not change the multiset of nontrivial cycle lengths. -/
theorem cycleType_permCongr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  let f : α ≃ {b : β // b ∈ Set.univ} := e.trans (Equiv.Set.univ β).symm
  have he : e.permCongr σ = σ.extendDomain f := by
    ext b
    rw [Equiv.Perm.extendDomain_apply_subtype _ _ (Set.mem_univ b)]
    rfl
  rw [he, Equiv.Perm.cycleType_extendDomain]

theorem cycleType_sumCongr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    (Equiv.Perm.sumCongr σ τ).cycleType = σ.cycleType + τ.cycleType := by
  let el := (Equiv.Set.rangeInl α β).symm
  let er := (Equiv.Set.rangeInr α β).symm
  have hl : Equiv.Perm.sumCongr σ (1 : Equiv.Perm β) = σ.extendDomain el := by
    ext x
    cases x with
    | inl a => exact (Equiv.Perm.extendDomain_apply_image σ el a).symm
    | inr b =>
      rw [Equiv.Perm.extendDomain_apply_not_subtype σ el (by simp)]
      rfl
  have hr : Equiv.Perm.sumCongr (1 : Equiv.Perm α) τ = τ.extendDomain er := by
    ext x
    cases x with
    | inl a =>
      rw [Equiv.Perm.extendDomain_apply_not_subtype τ er (by simp)]
      rfl
    | inr b => exact (Equiv.Perm.extendDomain_apply_image τ er b).symm
  have hd : Equiv.Perm.Disjoint (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β))
      (Equiv.Perm.sumCongr (1 : Equiv.Perm α) τ) := by
    intro x
    cases x <;> simp
  have hm : Equiv.Perm.sumCongr σ τ =
      Equiv.Perm.sumCongr σ (1 : Equiv.Perm β) * Equiv.Perm.sumCongr (1 : Equiv.Perm α) τ := by
    ext x
    cases x <;> rfl
  rw [hm, hd.cycleType_mul, hl, hr, Equiv.Perm.cycleType_extendDomain,
    Equiv.Perm.cycleType_extendDomain]

/-- The complete cycle multiset on a disjoint pair of label blocks. -/
theorem cyclePartition_blockEmbedding_parts {a b : ℕ}
    (σ : SymmetricGroup a) (τ : SymmetricGroup b) :
    (cyclePartition (blockEmbedding a b (σ, τ))).parts =
      (cyclePartition σ).parts + (cyclePartition τ).parts := by
  have hc : (blockEmbedding a b (σ, τ)).cycleType = σ.cycleType + τ.cycleType := by
    change (finSumFinEquiv.permCongr (Equiv.Perm.sumCongr σ τ)).cycleType = _
    rw [cycleType_permCongr, cycleType_sumCongr]
  have ha := σ.sum_cycleType_le
  have hb := τ.sum_cycleType_le
  simp only [Fintype.card_fin] at ha hb
  rw [cyclePartition_parts, cyclePartition_parts, cyclePartition_parts,
    ← Equiv.Perm.sum_cycleType, ← Equiv.Perm.sum_cycleType,
    ← Equiv.Perm.sum_cycleType, hc, Multiset.sum_add]
  have hn : a + b - (σ.cycleType.sum + τ.cycleType.sum) =
      (a - σ.cycleType.sum) + (b - τ.cycleType.sum) := by omega
  rw [hn, Multiset.replicate_add]
  ac_rfl

theorem partitionPowerSum_eq_multiset {n : ℕ} (r : ℕ) (ν : Partition n) :
    partitionPowerSum r ν = (ν.parts.map (powerSum r)).prod := by
  exact (Finset.prod_multiset_map_count ν.parts (powerSum r)).symm

theorem partitionPowerSum_blockEmbedding {a b : ℕ} (r : ℕ)
    (σ : SymmetricGroup a) (τ : SymmetricGroup b) :
    partitionPowerSum r (cyclePartition (blockEmbedding a b (σ, τ))) =
      partitionPowerSum r (cyclePartition σ) * partitionPowerSum r (cyclePartition τ) := by
  simp only [partitionPowerSum_eq_multiset, cyclePartition_blockEmbedding_parts,
    Multiset.map_add, Multiset.prod_add]

/-- The induction sum is independent of the representative of a conjugacy class. -/
theorem inductionSum_conj {H G : Type*} [Group H] [Group G]
    [Fintype H] [Fintype G] (φ : H →* G) (F : H → ℂ) (σ y : G) :
    (∑ x : G, ∑ h : H, if x * φ h * x⁻¹ = σ then F h else 0) =
      ∑ x : G, ∑ h : H, if x * φ h * x⁻¹ = y * σ * y⁻¹ then F h else 0 := by
  classical
  apply Fintype.sum_equiv (Equiv.mulLeft y)
  intro x
  apply Finset.sum_congr rfl
  intro h _
  have he : (y * x) * φ h * (y * x)⁻¹ = y * σ * y⁻¹ ↔
      x * φ h * x⁻¹ = σ := by
    rw [show (y * x) * φ h * (y * x)⁻¹ = y * (x * φ h * x⁻¹) * y⁻¹ by group]
    exact (MulAut.conj y).injective.eq_iff
  change (if x * φ h * x⁻¹ = σ then F h else 0) =
    (if (y*x) * φ h * (y*x)⁻¹ = y * σ * y⁻¹ then F h else 0)
  rw [he]

theorem ordinaryInduction_mk {H G : Type*} [Group H] [Group G]
    [Fintype H] [Fintype G] (φ : H →* G) (F : H → ℂ) (σ : G) :
    ordinaryInduction φ F (ConjClasses.mk σ) =
      (Fintype.card H : ℂ)⁻¹ * ∑ x : G, ∑ h : H,
        if x * φ h * x⁻¹ = σ then F h else 0 := by
  classical
  have ho : IsConj σ (ConjClasses.mk σ).out :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (Quotient.out_eq _).symm
  obtain ⟨y, hy⟩ := isConj_iff.mp ho
  change _ * _ = _ * _
  congr 1
  rw [← hy]
  exact (inductionSum_conj φ F σ y).symm

/-- The characteristic formula as an average over all permutations, in any
finite alphabet. This is the class-size formula, with no character assumption. -/
theorem characteristic_specialization_average {n : ℕ} (f : ClassFunction n) (r : ℕ) :
    (characteristic f).val r = (n.factorial : ℂ)⁻¹ •
      ∑ σ : SymmetricGroup n, f (ConjClasses.mk σ) • partitionPowerSum r (cyclePartition σ) := by
  classical
  apply MvPolynomial.ext
  intro d
  have h := sum_cyclePartition (fun ν => f (cycleClass ν) * (partitionPowerSum r ν).coeff d)
  simp_rw [cycleClass_cyclePartition] at h
  change ((∑ ν : Partition n, (f (cycleClass ν) / (zFactor ν : ℂ)) •
    stablePartitionPowerSum ν).val r).coeff d = _
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    stablePartitionPowerSum_specialization, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, smul_eq_mul]
  convert h.symm using 1 <;> simp only [Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin, div_eq_mul_inv]
  congr 1
  funext ν
  ring

/-- Averaging an induced function against a conjugacy-invariant vector-valued
weight reduces to averaging its restriction over the inducing group. -/
theorem induction_average {H G M : Type*} [Group H] [Group G]
    [Fintype H] [Fintype G] [AddCommGroup M] [Module ℂ M]
    (φ : H →* G) (F : H → ℂ) (w : G → M)
    (hw : ∀ x h, w (x * φ h * x⁻¹) = w (φ h)) :
    (Fintype.card G : ℂ)⁻¹ •
        (∑ σ : G, ordinaryInduction φ F (ConjClasses.mk σ) • w σ) =
      (Fintype.card H : ℂ)⁻¹ • ∑ h : H, F h • w (φ h) := by
  classical
  simp_rw [ordinaryInduction_mk, mul_smul, Finset.sum_smul]
  rw [← Finset.smul_sum, smul_comm]
  congr 1
  have hs : (∑ σ : G, ∑ x : G, ∑ h : H,
      (if x * φ h * x⁻¹ = σ then F h else 0) • w σ) =
      (Fintype.card G : ℂ) • ∑ h : H, F h • w (φ h) := by
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext x
      rw [Finset.sum_comm]
    simp only [ite_smul, zero_smul]
    simp [hw, Nat.cast_smul_eq_nsmul ℂ]
  rw [hs, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]
  exact one_smul ℂ _

theorem characteristic_induction_specialization {a b : ℕ}
    (f : ClassFunction a) (g : ClassFunction b) (r : ℕ) :
    (characteristic (inducedExternal f g)).val r =
      (characteristic f).val r * (characteristic g).val r := by
  have hw (x : SymmetricGroup (a+b)) (h : SymmetricGroup a × SymmetricGroup b) :
      partitionPowerSum r (cyclePartition (x * blockEmbedding a b h * x⁻¹)) =
        partitionPowerSum r (cyclePartition (blockEmbedding a b h)) := by
    congr 1
    exact (isConj_iff_cyclePartition_eq _ _).mp
      (isConj_iff.mpr ⟨x⁻¹, by group⟩)
  have hi := induction_average (blockEmbedding a b) (externalClassFunction f g)
    (fun σ => partitionPowerSum r (cyclePartition σ)) hw
  simp only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Nat.cast_mul] at hi
  rw [characteristic_specialization_average]
  change (↑(a+b).factorial : ℂ)⁻¹ •
    (∑ σ, ordinaryInduction (blockEmbedding a b) (externalClassFunction f g)
      (ConjClasses.mk σ) • partitionPowerSum r (cyclePartition σ)) = _
  rw [hi, Fintype.sum_prod_type, characteristic_specialization_average f,
    characteristic_specialization_average g]
  simp only [externalClassFunction, Specs.AdvancedFiniteGroupRepresentations.externalClassFunction,
    partitionPowerSum_blockEmbedding, smul_mul_smul_comm, mul_inv_rev]
  rw [mul_comm ((a.factorial : ℂ)⁻¹) ((b.factorial : ℂ)⁻¹)]
  congr 1
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]

theorem characteristic_induction_product {a b : ℕ}
    (f : ClassFunction a) (g : ClassFunction b) :
    DirectSum.of (fun n => stableDegree n) (a+b) (characteristic (inducedExternal f g)) =
      DirectSum.of (fun n => stableDegree n) a (characteristic f) *
        DirectSum.of (fun n => stableDegree n) b (characteristic g) := by
  apply stableRealization_injective
  funext r
  change stableSpecialization r
    (DirectSum.of (fun n => stableDegree n) (a+b) (characteristic (inducedExternal f g))) =
    stableSpecialization r
      (DirectSum.of (fun n => stableDegree n) a (characteristic f) *
        DirectSum.of (fun n => stableDegree n) b (characteristic g))
  rw [map_mul, stableSpecialization_of, stableSpecialization_of, stableSpecialization_of]
  exact characteristic_induction_specialization f g r

theorem frobenius_characteristic :
    Specs.AdvancedFiniteGroupRepresentations.frobenius_characteristicType :=
  ⟨characteristic_linearEquiv, @characteristic_isometry, @characteristic_specht,
    @characteristic_induction_product⟩

end AdvancedFiniteGroupRepresentations
