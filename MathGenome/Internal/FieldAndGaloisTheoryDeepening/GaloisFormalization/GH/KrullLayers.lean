import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers
import Mathlib.FieldTheory.Galois.Infinite
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.ProfiniteExactSequence

/-! Finite Galois layers in the intrinsic Krull topology. -/

namespace GaloisFormalization.GH.KrullLayers

universe u v w

open scoped Topology
open IntermediateField

noncomputable section

variable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]

/-- The automorphism group with Mathlib's intrinsic Krull topology. -/
abbrev GaloisGroup := Gal(L/k)

/-- The absolute Galois group of the chosen separable closure. -/
abbrev AbsoluteGaloisGroup [IsSepClosure k L] := GaloisGroup k L

abbrev profiniteGroup [IsGalois k L] : ProfiniteGrp :=
  InfiniteGalois.profiniteGalGrp k L

abbrev OpenNormalSubgroup :=
  {H : Subgroup Gal(L/k) // IsOpen (H : Set Gal(L/k)) ∧ H.Normal}

theorem layers_directed :
    Nonempty (FiniteGaloisIntermediateField k L) ∧
      Directed (· ≤ ·) (id : FiniteGaloisIntermediateField k L →
        FiniteGaloisIntermediateField k L) :=
  ⟨⟨⊥⟩, fun E F => ⟨E ⊔ F, le_sup_left, le_sup_right⟩⟩

variable {k L}

/-- A finite layer's Galois group, with its intrinsic discrete Krull topology. -/
abbrev LayerGroup (E : FiniteGaloisIntermediateField k L) := Gal(E/k)

/-- The subgroup fixing the layer pointwise. -/
abbrev layerKernel (E : FiniteGaloisIntermediateField k L) : Subgroup Gal(L/k) :=
  E.toIntermediateField.fixingSubgroup

theorem layer_finite_discrete (E : FiniteGaloisIntermediateField k L) :
    Finite (LayerGroup E) ∧ DiscreteTopology (LayerGroup E) :=
  ⟨inferInstance, inferInstance⟩

/-- Restriction to the embedded finite layer. -/
def restrict (E : FiniteGaloisIntermediateField k L) : Gal(L/k) →ₜ* LayerGroup E where
  toMonoidHom := AdvancedFieldTheory.restriction E.toIntermediateField
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous _

/-- Restriction along the inclusion of one finite layer into another. -/
def transition {E F : FiniteGaloisIntermediateField k L} (h : E ≤ F) :
    LayerGroup F →ₜ* LayerGroup E where
  toMonoidHom := AdvancedFieldTheory.stageRestriction h
  continuous_toFun := continuous_of_discreteTopology

@[simp]
theorem restrict_apply (E : FiniteGaloisIntermediateField k L) (σ : Gal(L/k)) (x : E) :
    (restrict E σ x : L) = σ (x : L) :=
  AdvancedFieldTheory.restriction_apply E.toIntermediateField σ x

/-- The inclusion of a layer's units intertwines restriction and evaluation. -/
theorem restrict_units_apply (E : FiniteGaloisIntermediateField k L) (σ : Gal(L/k)) (u : Eˣ) :
    Units.map (algebraMap E L).toMonoidHom (restrict E σ • u) =
      σ • Units.map (algebraMap E L).toMonoidHom u := by
  apply Units.ext
  exact restrict_apply E σ (u : E)

@[simp]
theorem transition_apply {E F : FiniteGaloisIntermediateField k L}
    (h : E ≤ F) (σ : LayerGroup F) (x : E) :
    (transition h σ x : L) = (σ (IntermediateField.inclusion h x) : L) :=
  AdvancedFieldTheory.stageRestriction_apply h σ x

theorem restrict_surjective [IsGalois k L] (E : FiniteGaloisIntermediateField k L) :
    Function.Surjective (restrict E) :=
  (AdvancedFieldTheory.galois_restriction_exact E.toIntermediateField).2.2.2.1

theorem transition_surjective {E F : FiniteGaloisIntermediateField k L} (h : E ≤ F) :
    Function.Surjective (transition h) :=
  AdvancedFieldTheory.stageRestriction_surjective h

theorem restrict_comp {E F : FiniteGaloisIntermediateField k L} (h : E ≤ F) :
    restrict E = (transition h).comp (restrict F) :=
  ContinuousMonoidHom.ext fun σ =>
    DFunLike.congr_fun (AdvancedFieldTheory.restriction_comp h) σ

@[simp]
theorem transition_refl (E : FiniteGaloisIntermediateField k L) :
    transition (le_refl E) = ContinuousMonoidHom.id (LayerGroup E) :=
  ContinuousMonoidHom.ext fun σ =>
    DFunLike.congr_fun (AdvancedFieldTheory.stageRestriction_self E.toIntermediateField) σ

theorem transition_comp {E F D : FiniteGaloisIntermediateField k L}
    (hEF : E ≤ F) (hFD : F ≤ D) :
    transition (hEF.trans hFD) = (transition hEF).comp (transition hFD) :=
  ContinuousMonoidHom.ext fun σ =>
    DFunLike.congr_fun (AdvancedFieldTheory.stageRestriction_comp hEF hFD) σ

theorem layerKernel_isOpen (E : FiniteGaloisIntermediateField k L) :
    IsOpen (layerKernel E : Set Gal(L/k)) :=
  E.toIntermediateField.fixingSubgroup_isOpen

@[simp]
theorem restrict_ker (E : FiniteGaloisIntermediateField k L) :
    (restrict E).toMonoidHom.ker = layerKernel E :=
  AdvancedFieldTheory.restriction_ker E.toIntermediateField

instance layerKernel_normal (E : FiniteGaloisIntermediateField k L) :
    (layerKernel E).Normal := by
  rw [← restrict_ker]
  infer_instance

theorem quotient_restriction [IsGalois k L] (E : FiniteGaloisIntermediateField k L) :
    ∃! e : (Gal(L/k) ⧸ layerKernel E) ≃ₜ* LayerGroup E,
      ∀ σ : Gal(L/k), e (QuotientGroup.mk σ) = restrict E σ :=
  AdvancedFieldTheory.restriction_quotient_topologicalIsomorphism E.toIntermediateField

theorem layerKernels_basis (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [IsGalois k L] :
    (𝓝 (1 : Gal(L/k))).HasBasis
      (fun _ : FiniteGaloisIntermediateField k L => True)
      (fun E => (layerKernel E : Set Gal(L/k))) := by
  simpa only [AdvancedFieldTheory.KrullTopology.finiteGaloisKernel_eq_fixingSubgroup] using
    AdvancedFieldTheory.KrullTopology.finiteGaloisKernels_nhds_one k L

@[simp]
theorem layerKernel_bot (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] :
    layerKernel (⊥ : FiniteGaloisIntermediateField k L) = ⊤ :=
  IntermediateField.fixingSubgroup_bot

@[simp]
theorem fixedField_layerKernel [IsGalois k L] (E : FiniteGaloisIntermediateField k L) :
    fixedField (layerKernel E) = E.toIntermediateField :=
  AdvancedFieldTheory.fixedField_fixingSubgroup k L E.toIntermediateField

theorem layerKernel_le_iff [IsGalois k L] {E F : FiniteGaloisIntermediateField k L} :
    layerKernel F ≤ layerKernel E ↔ E ≤ F :=
  (IntermediateField.le_iff_le (H := layerKernel F) (K := E.toIntermediateField)).symm.trans
    (by rw [fixedField_layerKernel]; rfl)

@[simp]
theorem fixedField_top (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [IsGalois k L] :
    fixedField (⊤ : Subgroup Gal(L/k)) = (⊥ : IntermediateField k L) := by
  rw [← layerKernel_bot k L, fixedField_layerKernel]
  rfl

theorem mem_range_algebraMap_iff_fixed [IsGalois k L] (x : L) :
    x ∈ Set.range (algebraMap k L) ↔ ∀ σ : Gal(L/k), σ x = x := by
  rw [← IntermediateField.mem_bot, ← fixedField_top k L, IntermediateField.mem_fixedField_iff]
  simp

/-- The Galois correspondence restricted to the finite layers and open normal subgroups. -/
theorem openNormalCorrespondence (k : Type u) (L : Type v) [Field k] [Field L]
    [Algebra k L] [IsGalois k L] :
    ∃ e : FiniteGaloisIntermediateField k L ≃o (OpenNormalSubgroup k L)ᵒᵈ,
      (∀ E, (OrderDual.ofDual (e E)).val = layerKernel E) ∧
      (∀ H : OpenNormalSubgroup k L,
        (e.symm (OrderDual.toDual H)).toIntermediateField = fixedField H.val) := by
  have fixing_eq (H : OpenNormalSubgroup k L) : (fixedField H.val).fixingSubgroup = H.val :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H.val, H.val.isClosed_of_isOpen H.prop.1⟩
  let fieldOf (H : OpenNormalSubgroup k L) : FiniteGaloisIntermediateField k L := by
    have h : IsOpen ((fixedField H.val).fixingSubgroup : Set Gal(L/k)) ∧
        (fixedField H.val).fixingSubgroup.Normal := by
      rw [fixing_eq H]
      exact H.prop
    let properties :=
      (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (fixedField H.val)).mp h
    exact
      { toIntermediateField := fixedField H.val
        finiteDimensional := properties.1
        isGalois := properties.2 }
  let e : FiniteGaloisIntermediateField k L ≃o (OpenNormalSubgroup k L)ᵒᵈ :=
    { toFun := fun E => OrderDual.toDual ⟨layerKernel E, layerKernel_isOpen E, inferInstance⟩
      invFun := fun H => fieldOf (OrderDual.ofDual H)
      left_inv := fun E => FiniteGaloisIntermediateField.val_injective (fixedField_layerKernel E)
      right_inv := fun H => Subtype.ext (fixing_eq (OrderDual.ofDual H))
      map_rel_iff' := fun {E F} => layerKernel_le_iff (E := E) (F := F) }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

theorem exists_layer_mem [IsGalois k L] (x : L) :
    ∃ E : FiniteGaloisIntermediateField k L, x ∈ E.toIntermediateField :=
  ⟨FiniteGaloisIntermediateField.adjoin k {x},
    FiniteGaloisIntermediateField.subset_adjoin k {x} (Set.mem_singleton x)⟩

/-- The field with discrete topology is a continuous Krull coefficient space. -/
theorem continuous_fieldAction (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [IsGalois k L] [TopologicalSpace L] [DiscreteTopology L] : ContinuousSMul Gal(L/k) L :=
  continuousSMul_iff_stabilizer_isOpen.mpr stabilizer_isOpen_of_isIntegral

/-- The corresponding continuous action on the discrete unit group. -/
theorem continuous_unitsAction (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [IsGalois k L] [TopologicalSpace Lˣ] [DiscreteTopology Lˣ] : ContinuousSMul Gal(L/k) Lˣ := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro u
  convert (stabilizer_isOpen_of_isIntegral (K := k) (u : L)) using 1
  ext σ
  change σ • u = u ↔ σ (u : L) = (u : L)
  constructor
  · exact congrArg Units.val
  · intro h
    apply Units.ext
    exact h

private theorem fixedUnitsOfRange {F : Type w} [Field F] {G : Type*} [Group G]
    [MulSemiringAction G L] [MulDistribMulAction G Lˣ]
    (smul_val : ∀ (g : G) (u : Lˣ), (↑(g • u) : L) = g • (u : L))
    (i : F →+* L) (hi : ∀ x : L, (∀ g : G, g • x = x) ↔ x ∈ Set.range i) :
    ∃ e : Fˣ ≃* FixedPoints.subgroup G Lˣ, ∀ u : Fˣ, (e u : Lˣ) = Units.map i.toMonoidHom u := by
  have hrange : (Units.map i.toMonoidHom).range = FixedPoints.subgroup G Lˣ := by
    ext u
    constructor
    · rintro ⟨v, rfl⟩
      intro g
      apply Units.ext
      rw [smul_val]
      exact (hi (i (v : F))).mpr ⟨v, rfl⟩ g
    · intro hu
      have hfix (g : G) : g • (u : L) = (u : L) := by
        rw [← smul_val, (FixedPoints.mem_subgroup G Lˣ u).mp hu g]
      obtain ⟨x, hx⟩ := (hi (u : L)).mp hfix
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact u.ne_zero (by simpa using hx.symm)
      exact ⟨Units.mk0 x hx0, Units.ext hx⟩
  refine ⟨(MonoidHom.ofInjective (Units.map_injective i.injective)).trans
    (MulEquiv.subgroupCongr hrange), ?_⟩
  intro u
  rfl

/-- The layer's units identify with the fixed units via the field inclusion. -/
theorem fixedUnits_layer [IsGalois k L] (E : FiniteGaloisIntermediateField k L) :
    ∃ e : Eˣ ≃* FixedPoints.subgroup (layerKernel E) Lˣ,
      ∀ u : Eˣ, (e u : Lˣ) = Units.map (algebraMap E L) u := by
  refine fixedUnitsOfRange (G := layerKernel E) (fun _ _ => rfl) (algebraMap E L) ?_
  intro x
  change (∀ g : layerKernel E, (g : Gal(L/k)) x = x) ↔
    x ∈ Set.range (algebraMap E L)
  have hfix : (∀ g : layerKernel E, (g : Gal(L/k)) x = x) ↔ x ∈ E.toIntermediateField := by
    rw [← fixedField_layerKernel E, mem_fixedField_iff]
    exact Subtype.forall
  exact hfix.trans ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩

/-- The full Galois group's fixed units are the scalar units. -/
theorem fixedUnits_base (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [IsGalois k L] :
    ∃ e : kˣ ≃* FixedPoints.subgroup Gal(L/k) Lˣ,
      ∀ u : kˣ, (e u : Lˣ) = Units.map (algebraMap k L) u := by
  apply fixedUnitsOfRange (fun _ _ => rfl)
  intro x
  exact (mem_range_algebraMap_iff_fixed x).symm

end

end GaloisFormalization.GH.KrullLayers
