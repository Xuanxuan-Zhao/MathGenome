import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic

namespace ALG02GroupTheory.Extensions

universe u v w v'

variable {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]

/-- A right inverse to the prescribed projection that takes the identity to the identity. -/
abbrev NormalizedSection (S : GroupExtension N E Q) :=
  {s : S.Section // s 1 = 1}

open scoped Pointwise

/-- The kernel image and the subgroup multiply to the whole group and intersect trivially. -/
def IsComplement (S : GroupExtension N E Q) (H : Subgroup E) : Prop :=
  (S.inl.range : Set E) * (H : Set E) = Set.univ ∧ S.inl.range ⊓ H = ⊥

/-- A map fixing the two prescribed end groups. -/
def IsExtensionMap {E' : Type v'} [Group E'] (S : GroupExtension N E Q)
    (T : GroupExtension N E' Q) (f : E →* E') : Prop :=
  f.comp S.inl = T.inl ∧ T.rightHom.comp f = S.rightHom

/-- The same exact extension model with the kernel written additively. -/
abbrev AbelianKernelExtension (A : Type u) (E : Type v) (Q : Type w)
    [AddCommGroup A] [Group E] [Group Q] :=
  GroupExtension (Multiplicative A) E Q

variable (S : GroupExtension N E Q)

/-- Shift any set section by the inverse of its value at the identity. -/
def normalizeSection (s : S.Section) : NormalizedSection S :=
  ⟨{ toFun := fun q => (s 1)⁻¹ * s q
     rightInverse_rightHom := fun q => by
       simp only [map_mul, map_inv, s.rightHom_section, inv_one, one_mul] },
   inv_mul_cancel (s 1)⟩

theorem normalizedSectionExists : Nonempty (NormalizedSection S) :=
  ⟨normalizeSection S S.surjInvRightHom⟩

theorem complementProjectionBijective {H : Subgroup E} (hH : IsComplement S H) :
    Function.Bijective (S.rightHom.domRestrict H) := by
  constructor
  · apply (S.rightHom.domRestrict H).ker_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro h hp
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hk : (h : E) ∈ S.inl.range ⊓ H :=
      ⟨by rw [S.range_inl_eq_ker_rightHom]; exact hp, h.property⟩
    rwa [hH.2, Subgroup.mem_bot] at hk
  · intro q
    obtain ⟨e, he⟩ := S.rightHom_surjective q
    have hm : e ∈ (S.inl.range : Set E) * (H : Set E) := by
      rw [hH.1]
      exact Set.mem_univ e
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hm
    have ha' : S.rightHom a = 1 := by
      change a ∈ S.inl.range at ha
      rw [S.range_inl_eq_ker_rightHom] at ha
      exact ha
    refine ⟨⟨b, hb⟩, ?_⟩
    change S.rightHom b = q
    rw [← he, ← hab, map_mul, ha', one_mul]

theorem splittingRangeIsComplement (s : S.Splitting) : IsComplement S s.toMonoidHom.range := by
  constructor
  · apply Set.eq_univ_of_forall
    intro e
    apply Set.mem_mul.mpr
    refine ⟨e * (s (S.rightHom e))⁻¹, ?_, s (S.rightHom e), ⟨S.rightHom e, rfl⟩,
      inv_mul_cancel_right _ _⟩
    change e * (s (S.rightHom e))⁻¹ ∈ S.inl.range
    simp [S.range_inl_eq_ker_rightHom]
  · apply le_antisymm ?_ bot_le
    intro e he
    obtain ⟨q, rfl⟩ := he.2
    have hk : s q ∈ S.inl.range := he.1
    rw [S.range_inl_eq_ker_rightHom] at hk
    have hp : q = 1 := (s.rightHom_splitting q).symm.trans hk
    rw [Subgroup.mem_bot, hp, map_one]

/-- Restrict the prescribed projection to the complement. -/
noncomputable def complementProjection (H : {H : Subgroup E // IsComplement S H}) :
    H.val ≃* Q :=
  MulEquiv.ofBijective (S.rightHom.domRestrict H.val) (complementProjectionBijective S H.property)

@[simp]
theorem complementProjection_apply (H : {H : Subgroup E // IsComplement S H}) (h : H.val) :
    complementProjection S H h = S.rightHom h := rfl

/-- Invert the restricted projection and include the complement in the middle group. -/
noncomputable def splittingOfComplement (H : {H : Subgroup E // IsComplement S H}) :
    S.Splitting where
  __ := H.val.subtype.comp (complementProjection S H).symm.toMonoidHom
  rightInverse_rightHom := (complementProjection S H).apply_symm_apply

theorem splittingOfComplement_mem (H : {H : Subgroup E // IsComplement S H}) (q : Q) :
    splittingOfComplement S H q ∈ H.val :=
  ((complementProjection S H).symm q).property

@[simp]
theorem splittingOfComplement_rightHom (H : {H : Subgroup E // IsComplement S H}) (h : H.val) :
    splittingOfComplement S H (S.rightHom h) = (h : E) :=
  congrArg Subtype.val ((complementProjection S H).symm_apply_apply h)

/-- The image of a splitting and the inverse of the restricted projection are inverse maps. -/
noncomputable def splittingComplementEquiv :
    S.Splitting ≃ {H : Subgroup E // IsComplement S H} where
  toFun s := ⟨s.toMonoidHom.range, splittingRangeIsComplement S s⟩
  invFun := splittingOfComplement S
  left_inv s := by
    apply DFunLike.ext
    intro q
    let h : s.toMonoidHom.range := ⟨s q, ⟨q, rfl⟩⟩
    have hq : S.rightHom h = q := s.rightHom_splitting q
    simpa only [hq] using
      splittingOfComplement_rightHom S ⟨s.toMonoidHom.range, splittingRangeIsComplement S s⟩ h
  right_inv H := by
    apply Subtype.ext
    ext e
    change (∃ q, splittingOfComplement S H q = e) ↔ e ∈ H.val
    exact ⟨fun ⟨q, hq⟩ => hq ▸ splittingOfComplement_mem S H q,
      fun he => ⟨S.rightHom e, splittingOfComplement_rightHom S H ⟨e, he⟩⟩⟩

theorem splittingsCorrespondToComplements :
    ∃ e : S.Splitting ≃ {H : Subgroup E // IsComplement S H},
      (∀ s : S.Splitting, (e s).val = s.toMonoidHom.range) ∧
      (∀ H : {H : Subgroup E // IsComplement S H},
        (∀ q : Q, e.symm H q ∈ H.val) ∧
        (∀ h : H.val, e.symm H (S.rightHom h) = (h : E))) :=
  ⟨splittingComplementEquiv S, fun _ => rfl,
    fun H => ⟨splittingOfComplement_mem S H, splittingOfComplement_rightHom S H⟩⟩

theorem fixedEndMapIsEquivalence {E' : Type v'} [Group E']
    {S : GroupExtension N E Q} {T : GroupExtension N E' Q} (f : E →* E')
    (hf : IsExtensionMap S T f) : ∃ e : S.Equiv T, e.toMulEquiv.toMonoidHom = f :=
  ⟨GroupExtension.Equiv.ofMonoidHom f hf.1 hf.2, rfl⟩

end ALG02GroupTheory.Extensions
