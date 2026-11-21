import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.UniversalEnveloping

namespace Shared.Lie
attribute [local instance 100] LieRing.ofAssociativeRing
universe u v w w'
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- Induction on sums and products of the canonical generators and scalars. -/
@[elab_as_elim] theorem enveloping_induction {P : U k g → Prop}
    (scalar : ∀ r, P (algebraMap k (U k g) r))
    (generator : ∀ x, P (inclusion k g x))
    (mul : ∀ a b, P a → P b → P (a*b))
    (add : ∀ a b, P a → P b → P (a+b)) (a : U k g) : P a := by
  obtain ⟨t, rfl⟩ := (UniversalEnvelopingAlgebra.ringCon k g).mk'_surjective a
  change P (tensorQuotient k g t)
  induction t using TensorAlgebra.induction with
  | algebraMap r => simpa using scalar r
  | ι x => exact generator x
  | mul a b ha hb => simpa using mul _ _ ha hb
  | add a b ha hb => simpa using add _ _ ha hb

theorem quotient : Specs.Shared.Lie.quotientType k g := by
  constructor
  · exact (UniversalEnvelopingAlgebra.ringCon k g).mk'_surjective
  · intro x y
    exact ((inclusion k g).map_lie x y).symm

theorem universal : Specs.Shared.Lie.universalType.{u,v,w} k g := by
  intro A _ _ f
  refine ⟨UniversalEnvelopingAlgebra.lift k f, ?_, ?_⟩
  · exact UniversalEnvelopingAlgebra.lift_ι_apply k f
  · intro F h
    exact (UniversalEnvelopingAlgebra.lift_unique k f F).mp (funext h)

theorem augmentation_properties : Specs.Shared.Lie.augmentationType k g := by
  constructor
  · intro x
    exact UniversalEnvelopingAlgebra.lift_ι_apply k (0 : g →ₗ⁅k⁆ k) x
  · intro r
    exact (augmentation k g).commutes r

variable (M : Type w) [AddCommGroup M] [Module k M]

theorem action_tower : Specs.Shared.Lie.actionTowerType k g M := by
  intro a
  letI := actionModule k g M a
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change a (algebraMap k (U k g) r) m = r • m
  rw [a.commutes]
  rfl

theorem action_roundtrip : Specs.Shared.Lie.actionRoundtripType k g M := by
  intro a h
  ext u m
  rfl

theorem representation_properties : Specs.Shared.Lie.representationType k g M := by
  constructor
  · intro ρ x m
    exact congrArg (fun f : Module.End k M => f m)
      (UniversalEnvelopingAlgebra.lift_ι_apply k ρ x)
  · exact (representationEquiv k g M).apply_symm_apply

theorem module_restriction [Module (U k g) M] [IsScalarTower k (U k g) M] :
    Specs.Shared.Lie.moduleRestrictionType k g M := by
  intro u m
  have h := (representationEquiv k g M).apply_symm_apply
    (Algebra.lsmul k k M : U k g →ₐ[k] Module.End k M)
  exact congrArg (fun a : ModuleAction k g M => a u m) h

theorem lie_extension [LieRingModule g M] [LieModule k g M] :
    Specs.Shared.Lie.lieExtensionType k g M := by
  exact (representation_properties k g M).1 (LieModule.toEnd k g M)

theorem morphism_correspondence : Specs.Shared.Lie.morphismType.{u,v,w,w'} k g M := by
  intro N _ _ ρ σ f
  constructor
  · intro h x m
    have h' := h (inclusion k g x) m
    simpa only [(representation_properties k g M).1,
      (representation_properties k g N).1] using h'
  · intro h u
    induction u using enveloping_induction k g with
    | scalar r =>
      intro m
      simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
    | generator x =>
      intro m
      simpa only [(representation_properties k g M).1,
        (representation_properties k g N).1] using h x m
    | mul a b ha hb =>
      intro m
      simp only [map_mul, Module.End.mul_apply, ha, hb]
    | add a b ha hb =>
      intro m
      simp only [map_add, LinearMap.add_apply, ha, hb]

/-- The equivalence on morphisms leaves the underlying linear map unchanged. -/
def intertwinerEquiv {N : Type w'} [AddCommGroup N] [Module k N]
    (ρ : Representation k g M) (σ : Representation k g N) :
    {f : M →ₗ[k] N // LieIntertwines ρ σ f} ≃
    {f : M →ₗ[k] N // Intertwines (representationEquiv k g M ρ)
      (representationEquiv k g N σ) f} where
  toFun f := ⟨f.1, (morphism_correspondence k g M N ρ σ f.1).mpr f.2⟩
  invFun f := ⟨f.1, (morphism_correspondence k g M N ρ σ f.1).mp f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Each word lies in the step indexed by its length (or any larger index). -/
theorem word_mem {m : ℤ} (xs : List g) (h : (xs.length : ℤ) ≤ m) :
    word k g xs ∈ filtration k g m :=
  Submodule.subset_span ⟨xs, h, rfl⟩

theorem filtration_mono : Monotone (filtration k g) := by
  intro i j hij
  apply Submodule.span_mono
  rintro a ⟨xs, h, rfl⟩
  exact ⟨xs, h.trans hij, rfl⟩

theorem filtration_negative (m : ℤ) (h : m < 0) : filtration k g m = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro a ⟨xs, hx, rfl⟩
  have : (0 : ℤ) ≤ xs.length := Int.natCast_nonneg _
  exact False.elim ((not_le_of_gt h) (this.trans hx))

theorem one_mem_filtration : (1 : U k g) ∈ filtration k g 0 := by
  simpa [word] using word_mem k g [] (le_refl (0 : ℤ))

theorem inclusion_mem_filtration (x : g) : inclusion k g x ∈ filtration k g 1 := by
  simpa [word] using word_mem k g [x] (le_refl (1 : ℤ))

theorem word_append (xs ys : List g) : word k g (xs ++ ys) = word k g xs * word k g ys := by
  simp [word, List.map_append, List.prod_append]

theorem mul_mem_filtration (i j : ℤ) (a b : U k g)
    (ha : a ∈ filtration k g i) (hb : b ∈ filtration k g j) :
    a*b ∈ filtration k g (i+j) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨xs, hx, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨ys, hy, rfl⟩ := hb
      rw [← word_append]
      apply word_mem
      simpa only [List.length_append, Nat.cast_add] using add_le_add hx hy
    | zero => simpa using (filtration k g (i+j)).zero_mem
    | add b c hb hc ihb ihc =>
      simpa only [mul_add] using (filtration k g (i+j)).add_mem ihb ihc
    | smul r b hb ih =>
      simpa only [Algebra.mul_smul_comm] using (filtration k g (i+j)).smul_mem r ih
  | zero => simpa using (filtration k g (i+j)).zero_mem
  | add a c ha hc iha ihc =>
    simpa only [add_mul] using (filtration k g (i+j)).add_mem iha ihc
  | smul r a ha ih =>
    simpa only [Algebra.smul_mul_assoc] using (filtration k g (i+j)).smul_mem r ih

theorem filtration_exhaustive (a : U k g) : ∃ m : ℤ, a ∈ filtration k g m := by
  induction a using enveloping_induction k g with
  | scalar r =>
    refine ⟨0, ?_⟩
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (filtration k g 0).smul_mem r (one_mem_filtration k g)
  | generator x => exact ⟨1, inclusion_mem_filtration k g x⟩
  | mul a b ha hb =>
    obtain ⟨i, hi⟩ := ha
    obtain ⟨j, hj⟩ := hb
    exact ⟨i+j, mul_mem_filtration k g i j a b hi hj⟩
  | add a b ha hb =>
    obtain ⟨i, hi⟩ := ha
    obtain ⟨j, hj⟩ := hb
    exact ⟨max i j, (filtration k g (max i j)).add_mem
      (filtration_mono k g (le_max_left _ _) hi)
      (filtration_mono k g (le_max_right _ _) hj)⟩

theorem filtration_properties : Specs.Shared.Lie.filtrationType k g :=
  ⟨filtration_mono k g, filtration_negative k g, one_mem_filtration k g,
    inclusion_mem_filtration k g, mul_mem_filtration k g, filtration_exhaustive k g⟩

theorem underlying_tower (N : Type w) [AddCommGroup N] [Module (U k g) N] :
    Specs.Shared.Lie.underlyingTowerType k g N := by
  letI := underlyingModule k g N
  apply IsScalarTower.of_algebraMap_smul
  intro r n
  rfl

theorem lie_roundtrip : Specs.Shared.Lie.lieRoundtripType k g M := by
  intro ρ
  rfl

theorem module_roundtrip [Module (U k g) M] [IsScalarTower k (U k g) M] :
    Specs.Shared.Lie.moduleRoundtripType k g M := by
  apply Module.ext
  rfl

theorem morphism_equivalence : Specs.Shared.Lie.morphismEquivType.{u,v,w,w'} k g M := by
  intro N _ _ ρ σ
  exact ⟨intertwinerEquiv k g M ρ σ, fun _ => rfl⟩

/-- The object correspondence expressed using native unital module structures. -/
def compatibleModulesEquiv : Representation k g M ≃ CompatibleModule k g M where
  toFun ρ := ⟨actionModule k g M (representationEquiv k g M ρ),
    action_tower k g M (representationEquiv k g M ρ)⟩
  invFun a := by
    letI := a.val
    letI := a.property
    exact (representationEquiv k g M).symm (Algebra.lsmul k k M)
  left_inv ρ := by
    change (representationEquiv k g M).symm _ = ρ
    apply (representationEquiv k g M).injective
    rw [(representationEquiv k g M).apply_symm_apply]
    ext u m
    rfl
  right_inv a := by
    apply Subtype.ext
    apply Module.ext
    funext u m
    change representationEquiv k g M
      ((representationEquiv k g M).symm _) u m = _
    rw [(representationEquiv k g M).apply_symm_apply]
    rfl

theorem module_structures : Specs.Shared.Lie.moduleStructuresType k g M :=
  ⟨compatibleModulesEquiv k g M, fun _ _ _ => rfl⟩

-- Public constructions, with independently specified types and values.
def envelopingAlgebra := U k g
def canonicalLieMap := inclusion k g
def quotientMap := tensorQuotient k g
def augmentationMap := augmentation k g
def wordLengthFiltration := filtration k g
def modulesEquiv := representationEquiv k g M

end Shared.Lie

namespace Shared.Lie
-- Closed, fully quantified declarations for the submission bindings.
universe u v w w'
theorem quotient_spec : Specs.Shared.Lie.quotientExpected.{u,v} := quotient
theorem universal_spec : Specs.Shared.Lie.universalExpected.{u,v,w} := universal
theorem augmentation_spec : Specs.Shared.Lie.augmentationExpected.{u,v} := augmentation_properties
theorem filtration_spec : Specs.Shared.Lie.filtrationExpected.{u,v} := filtration_properties
theorem actionTower_spec : Specs.Shared.Lie.actionTowerExpected.{u,v,w} := action_tower
theorem actionRoundtrip_spec : Specs.Shared.Lie.actionRoundtripExpected.{u,v,w} := action_roundtrip
theorem representation_spec : Specs.Shared.Lie.representationExpected.{u,v,w} := representation_properties
theorem moduleRestriction_spec : Specs.Shared.Lie.moduleRestrictionExpected.{u,v,w} := module_restriction
theorem lieExtension_spec : Specs.Shared.Lie.lieExtensionExpected.{u,v,w} := lie_extension
theorem morphism_spec : Specs.Shared.Lie.morphismExpected.{u,v,w,w'} := morphism_correspondence
theorem underlyingTower_spec : Specs.Shared.Lie.underlyingTowerExpected.{u,v,w} := underlying_tower
theorem lieRoundtrip_spec : Specs.Shared.Lie.lieRoundtripExpected.{u,v,w} := lie_roundtrip
theorem moduleRoundtrip_spec : Specs.Shared.Lie.moduleRoundtripExpected.{u,v,w} := module_roundtrip
theorem moduleStructures_spec : Specs.Shared.Lie.moduleStructuresExpected.{u,v,w} := module_structures
theorem morphismEquiv_spec : Specs.Shared.Lie.morphismEquivExpected.{u,v,w,w'} := morphism_equivalence
end Shared.Lie
