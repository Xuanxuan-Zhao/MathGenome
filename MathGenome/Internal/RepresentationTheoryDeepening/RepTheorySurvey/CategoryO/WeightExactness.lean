import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.WeightExactness
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Isomorphisms

open scoped DirectSum

namespace RepTheorySurvey.CategoryO.WeightExactness

variable {H : Type*} [LieRing H] [LieAlgebra ℂ H]
variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [LieRingModule H X] [LieModule ℂ H X]
  [AddCommGroup Y] [Module ℂ Y] [LieRingModule H Y] [LieModule ℂ H Y]

private theorem mem_weightSpace {μ : Module.Dual ℂ H} {x : X} :
    x ∈ weightSpace X μ ↔ ∀ a : H, ⁅a, x⁆ = μ a • x :=
  LieModule.mem_weightSpace μ x

/-- Apply one factor of the interpolation polynomial at each induction step. -/
private theorem component_mem_of_separating_element (S : LieSubmodule ℂ H X) (a : H)
    (μ : Module.Dual ℂ H) (t : Finset (Module.Dual ℂ H))
    (v : Module.Dual ℂ H → X)
    (hμv : v μ ∈ weightSpace X μ)
    (hv : ∀ ν ∈ t, v ν ∈ weightSpace X ν)
    (hsep : ∀ ν ∈ t, μ a ≠ ν a)
    (hsum : v μ + ∑ ν ∈ t, v ν ∈ S) : v μ ∈ S := by
  classical
  induction t using Finset.induction_on generalizing v with
  | empty => simpa using hsum
  | insert ν t hν ih =>
    let T : Module.End ℂ X := (LieModule.toEnd ℂ H X a : Module.End ℂ X) - ν a • LinearMap.id
    have hTv {ξ : Module.Dual ℂ H} (hx : v ξ ∈ weightSpace X ξ) :
        T (v ξ) = (ξ a - ν a) • v ξ := by
      change ⁅a, v ξ⁆ - ν a • v ξ = _
      rw [mem_weightSpace.mp hx a, sub_smul]
    have hTmem : T (v μ + ∑ ξ ∈ insert ν t, v ξ) ∈ S :=
      S.sub_mem (S.lie_mem hsum) (S.smul_mem _ hsum)
    rw [map_add, map_sum, Finset.sum_insert hν, hTv (hv ν (Finset.mem_insert_self _ _)),
      sub_self, zero_smul, zero_add] at hTmem
    have hscaled : T (v μ) ∈ S := ih (fun ξ => T (v ξ))
      (hTv hμv ▸ (weightSpace X μ).smul_mem _ hμv)
      (fun ξ hξ => by
        have hx := hv ξ (Finset.mem_insert_of_mem hξ)
        rw [hTv hx]
        exact (weightSpace X ξ).smul_mem _ hx)
      (fun ξ hξ => hsep ξ (Finset.mem_insert_of_mem hξ)) hTmem
    rw [hTv hμv] at hscaled
    have hne : μ a - ν a ≠ 0 := sub_ne_zero.mpr (hsep ν (Finset.mem_insert_self ν t))
    simpa [smul_smul, inv_mul_cancel₀ hne] using S.smul_mem (μ a - ν a)⁻¹ hscaled

private theorem component_mem (S : LieSubmodule ℂ H X)
    (s : Finset (Module.Dual ℂ H)) (v : Module.Dual ℂ H → X)
    (hv : ∀ ν ∈ s, v ν ∈ weightSpace X ν)
    (hsum : (∑ ν ∈ s, v ν) ∈ S) {μ : Module.Dual ℂ H} (hμ : μ ∈ s) :
    v μ ∈ S := by
  classical
  let d (ν : ↥(s.erase μ)) : Module.Dual ℂ H := μ - ν.val
  obtain ⟨a, ha⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists d (by
    intro ν
    by_contra! hz
    apply (Finset.ne_of_mem_erase ν.property)
    exact LinearMap.ext fun a => (sub_eq_zero.mp (hz a)).symm)
  rw [← Finset.add_sum_erase s v hμ] at hsum
  exact component_mem_of_separating_element S a μ (s.erase μ) v (hv μ hμ)
    (fun ν hν => hv ν (Finset.mem_of_mem_erase hν))
    (fun ν hν => sub_ne_zero.mp (ha ⟨ν, hν⟩)) hsum

/-- The ordinary weight spaces are independent, with no dimension restriction. -/
theorem weightSpaces_independent :
    iSupIndep (weightSpace X (H := H)) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum μ hμ
  have hsum' : (∑ ν ∈ s, v ν) ∈ (⊥ : LieSubmodule ℂ H X) := by
    rw [hsum]
    exact zero_mem _
  exact (LieSubmodule.mem_bot _).mp (component_mem ⊥ s v hv hsum' hμ)

/-- Stable subspaces split into their intersections with the ordinary weight spaces. -/
theorem stableSubspace : Spec.stableSubspace := by
  intro H _ _ X _ _ _ _ S hX
  classical
  have hinter (μ : Module.Dual ℂ H) :
      (weightSpace S μ).map S.toSubmodule.subtype = S.toSubmodule ⊓ weightSpace X μ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, mem_weightSpace.mpr (fun a =>
        congrArg Subtype.val ((mem_weightSpace (X := ↥S)).mp hy a))⟩
    · rintro ⟨hx, hxμ⟩
      exact ⟨⟨x, hx⟩, (mem_weightSpace (X := ↥S)).mpr (fun a =>
        Subtype.ext (mem_weightSpace.mp hxμ a)), rfl⟩
  have hspan : (⨆ μ : Module.Dual ℂ H, S.toSubmodule ⊓ weightSpace X μ) = S.toSubmodule := by
    refine le_antisymm (iSup_le fun _ => inf_le_left) ?_
    intro x hx
    have hmem : x ∈ ⨆ μ : Module.Dual ℂ H, weightSpace X μ := by
      rw [DirectSum.IsInternal.submodule_iSup_eq_top hX]
      exact Submodule.mem_top
    obtain ⟨v, hv, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hmem
    change (∑ ν ∈ v.support, v ν) = x at hsum
    rw [← hsum] at hx ⊢
    exact Submodule.sum_mem _ fun ν hν => Submodule.mem_iSup_of_mem ν
      ⟨component_mem S v.support v (fun ξ _ => hv ξ) hx hν, hv ν⟩
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top weightSpaces_independent ?_,
    hinter, hspan⟩
  apply Submodule.map_injective_of_injective S.toSubmodule.injective_subtype
  rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype]
  simpa only [hinter] using hspan

private theorem weightSpace_map_le (f : X →ₗ⁅ℂ,H⁆ Y) (μ : Module.Dual ℂ H) :
    (weightSpace X μ).map (f : X →ₗ[ℂ] Y) ≤ weightSpace Y μ := by
  rintro _ ⟨x, hx, rfl⟩
  exact (weightMap f μ ⟨x, hx⟩).property

private theorem weightSpace_map_eq (f : X →ₗ⁅ℂ,H⁆ Y)
    (hX : IsWeightModule (H := H) X) (hf : Function.Surjective f) :
    (fun μ => (weightSpace X μ).map (f : X →ₗ[ℂ] Y)) = weightSpace Y (H := H) := by
  classical
  have hspan : (⨆ μ : Module.Dual ℂ H, (weightSpace X μ).map (f : X →ₗ[ℂ] Y)) = ⊤ := by
    rw [← Submodule.map_iSup, DirectSum.IsInternal.submodule_iSup_eq_top hX, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hf
  exact (iSupIndep.le_iff_eq_of_iSup_eq_top weightSpaces_independent hspan).mp (weightSpace_map_le f)

/-- A surjection from a weight module surjects on every ordinary weight space. -/
theorem weightMap_surjective (f : X →ₗ⁅ℂ,H⁆ Y)
    (hX : IsWeightModule (H := H) X) (hf : Function.Surjective f)
    (μ : Module.Dual ℂ H) : Function.Surjective (weightMap f μ) := by
  intro y
  have hy : (y : Y) ∈ (weightSpace X μ).map (f : X →ₗ[ℂ] Y) := by
    rw [congrFun (weightSpace_map_eq f hX hf) μ]
    exact y.property
  obtain ⟨x, hx, he⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- The induced weight spaces of the quotient are the corresponding weight-space quotients. -/
theorem quotient : Spec.quotient := by
  intro H _ _ X _ _ _ _ S hX
  classical
  let q := LieSubmodule.Quotient.mk' S
  have hq : Function.Surjective q := LieSubmodule.Quotient.surjective_mk' S
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top weightSpaces_independent ?_, ?_⟩
  · rw [← weightSpace_map_eq q hX hq, ← Submodule.map_iSup,
      DirectSum.IsInternal.submodule_iSup_eq_top hX, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hq
  · intro μ
    let qμ := weightMap q μ
    have hker : S.toSubmodule.comap (weightSpace X μ).subtype = qμ.ker := by
      ext x
      change ((x : weightSpace X μ) : X) ∈ S ↔ qμ x = 0
      rw [← LieSubmodule.Quotient.mk_eq_zero S]
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    refine ⟨(Submodule.quotEquivOfEq _ _ hker).trans
      (qμ.quotKerEquivOfSurjective (weightMap_surjective q hX hq μ)), ?_⟩
    intro x
    simp only [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
    rfl

/-- The ordinary weight-space maps take short exact sequences to short exact sequences. -/
theorem shortExact : Spec.shortExact := by
  intro H _ _ X _ _ _ _ Y _ _ _ _ Z _ _ _ _ f g hY hf hex hg μ
  refine ⟨fun x y hxy => Subtype.ext (hf (congrArg Subtype.val hxy)), ?_,
    weightMap_surjective g hY hg μ⟩
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (hex (y : Y)).mp (congrArg Subtype.val hy)
    have hxμ : x ∈ weightSpace X μ := by
      apply mem_weightSpace.mpr
      intro a
      apply hf
      rw [f.map_lie, map_smul, hx, mem_weightSpace.mp y.property a]
    exact ⟨⟨x, hxμ⟩, Subtype.ext hx⟩
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    exact (hex (f x)).mpr ⟨x, rfl⟩

/-- Algebraic direct sums preserve the ordinary weight decomposition. -/
theorem directSum : Spec.directSum := by
  classical
  intro H _ _ ι V _ _ _ _ hV
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top weightSpaces_independent ?_
  apply top_unique
  intro x _
  refine DirectSum.induction_on x (Submodule.zero_mem _) ?_ (fun x y hx hy => Submodule.add_mem _ hx hy)
  intro i v
  let f := DirectSum.lieModuleOf ℂ ι H V i
  have hmap :
      (⨆ μ : Module.Dual ℂ H, weightSpace (V i) μ).map (f : V i →ₗ[ℂ] ⨁ j, V j) ≤
        ⨆ μ : Module.Dual ℂ H, weightSpace (⨁ j, V j) μ := by
    rw [Submodule.map_iSup]
    exact iSup_le fun μ => (weightSpace_map_le f μ).trans (le_iSup _ μ)
  apply hmap
  refine ⟨v, ?_, rfl⟩
  rw [DirectSum.IsInternal.submodule_iSup_eq_top (hV i)]
  exact Submodule.mem_top

/-- The restricted enveloping action gives exactly the usual joint eigenvector equations. -/
theorem envelopingWeightSpace : Spec.envelopingWeightSpace := by
  intro L V _ _ _ _ _ _ h μ v
  simp only [weightSpace, LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace]
  rfl

end RepTheorySurvey.CategoryO.WeightExactness
