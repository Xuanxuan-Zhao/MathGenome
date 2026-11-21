import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.UniversalCentral
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.CentralPresentation

namespace ALG02GroupTheory.Extensions.UniversalCentral

open CentralPresentation (PresentationGroup projection)
open Spec (freePresentation)
open scoped commutatorElement

universe u v w t u' v' t'

/-- A central target admits at most one map over the base from a perfect group. -/
private theorem hom_over_eq
    {E : Type v} {G : Type w} [Group E] [Group G]
    {K : Type u'} {D : Type v'} [Group K] [Group D] [Group.IsPerfect E]
    {T : GroupExtension K D G} (hT : IsCentralExtension T)
    {f g : E →* D} (h : T.rightHom.comp f = T.rightHom.comp g) :
    f = g := by
  let d (x : E) := f x * (g x)⁻¹
  have hd (x : E) : d x ∈ Subgroup.center D := by
    apply (isCentralExtension_iff_ker_le_center T).mp hT
    have hx : T.rightHom (f x) = T.rightHom (g x) := DFunLike.congr_fun h x
    simp [MonoidHom.mem_ker, d, hx]
  let δ : E →* Subgroup.center D :=
    { toFun := fun x => ⟨d x, hd x⟩
      map_one' := Subtype.ext (by simp [d])
      map_mul' := fun x y => Subtype.ext <| calc
        d (x * y) = f x * (d y * (g x)⁻¹) := by simp [d, mul_assoc]
        _ = f x * ((g x)⁻¹ * d y) := by rw [Subgroup.mem_center_iff.mp (hd y) (g x)⁻¹]
        _ = d x * d y := by simp [d, mul_assoc] }
  have hδ : commutator E ≤ δ.ker := Abelianization.commutator_subset_ker δ
  apply MonoidHom.ext
  intro x
  have hx : δ x = 1 :=
    MonoidHom.mem_ker.mp (hδ (Group.IsPerfect.mem_commutator (g := x)))
  have hx' : d x = 1 := congrArg Subtype.val hx
  exact mul_inv_eq_one.mp hx'

/-- Lift the free generators, then restrict to the commutator subgroup and pass
to the quotient by commutators with the relators. -/
theorem presentation_unique_hom : Spec.PresentationUniqueHom.{u, v, w, u', v'} := by
  intro R F G _ _ _ _ _ S K D _ _ T hT
  let lifts (x : IsFreeGroup.Generators F) : D :=
    (T.rightHom_surjective (S.rightHom (IsFreeGroup.of x))).choose
  let φ : F →* D := IsFreeGroup.lift lifts
  have hφ : T.rightHom.comp φ = S.rightHom := by
    apply IsFreeGroup.ext_hom
    intro x
    change T.rightHom (IsFreeGroup.lift lifts (IsFreeGroup.of x)) = _
    rw [IsFreeGroup.lift_of]
    exact (T.rightHom_surjective (S.rightHom (IsFreeGroup.of x))).choose_spec
  have hRelator (r : F) (hr : r ∈ S.inl.range) : φ r ∈ Subgroup.center D := by
    apply (isCentralExtension_iff_ker_le_center T).mp hT
    have hr' : S.rightHom r = 1 := MonoidHom.mem_ker.mp (S.range_inl_eq_ker_rightHom ▸ hr)
    exact MonoidHom.mem_ker.mpr ((DFunLike.congr_fun hφ r).trans hr')
  have hDenom : HopfFormula.denominator S.inl.range ≤ φ.ker := by
    apply Subgroup.commutator_le.mpr
    intro a _ r hr
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hRelator r hr) (φ a))
  let lift : PresentationGroup S →* D :=
    QuotientGroup.lift _ (φ.comp (commutator F).subtype) (fun x hx => hDenom hx)
  have hLift : T.rightHom.comp lift = projection S := by
    apply MonoidHom.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | _ a => exact DFunLike.congr_fun hφ a.val
  let _ := CentralPresentation.presentation_perfect S
  exact ⟨lift, hLift, fun f hf => hom_over_eq hT (hf.trans hLift.symm)⟩

/-- The extension constructed from the given free presentation is universal. -/
theorem presentation_isUniversal
    {R : Type u} {F : Type v} {G : Type w} [Group R] [Group F] [Group G]
    [IsFreeGroup F] [Group.IsPerfect G] (S : GroupExtension R F G) :
    IsUniversalCentralExtension.{v, v, w, t} (CentralPresentation.extension S) := by
  refine ⟨CentralPresentation.extension_central S, ?_⟩
  intro K D _ _ T hT
  exact presentation_unique_hom S T hT

theorem perfect_of_universal : Spec.PerfectOfUniversal.{u, v, w, t} := by
  intro N E G _ _ _ S hS
  let A := Abelianization E
  let T : GroupExtension A (A × G) G :=
    { inl := MonoidHom.inl A G
      rightHom := MonoidHom.snd A G
      inl_injective := fun _ _ h => congrArg Prod.fst h
      range_inl_eq_ker_rightHom := by
        ext ⟨a, g⟩
        change (∃ b : A, (b, (1 : G)) = (a, g)) ↔ g = 1
        simp [eq_comm]
      rightHom_surjective := fun g => ⟨(1, g), rfl⟩ }
  have hT : IsCentralExtension T := by
    rintro _ ⟨a, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro x
    change (x.1 * a, x.2 * 1) = (a * x.1, 1 * x.2)
    simp [mul_comm x.1 a]
  obtain ⟨_, _, hk⟩ :=
    IsUniversalCentralExtension.existsUniqueHomOverArbitrary.{u, v, w, t, v, max v w} hS T hT
  let f : E →* A × G := Abelianization.of.prod S.rightHom
  let g : E →* A × G := (1 : E →* A).prod S.rightHom
  have hfg : f = g := (hk f (by ext; rfl)).trans (hk g (by ext; rfl)).symm
  have hPerfect : Group.IsPerfect E := by
    constructor
    rw [← Abelianization.ker_of]
    apply top_unique
    intro x _
    exact MonoidHom.mem_ker.mpr (congrArg Prod.fst (DFunLike.congr_fun hfg x))
  exact ⟨hPerfect, Group.IsPerfect.ofSurjective S.rightHom_surjective⟩

theorem universal_comparison : Spec.UniversalComparison.{u, v, w, t, u', v', t'} := by
  intro N E G _ _ _ S K D _ _ T hS hT
  obtain ⟨f, hf, hf_unique⟩ :=
    IsUniversalCentralExtension.existsUniqueHomOverArbitrary.{u, v, w, t, u', v'} hS T hT.1
  obtain ⟨g, hg, _⟩ :=
    IsUniversalCentralExtension.existsUniqueHomOverArbitrary.{u', v', w, t', u, v} hT S hS.1
  have hgf : g.comp f = MonoidHom.id E := by
    let _ := (perfect_of_universal.{u, v, w, t} hS).1
    apply hom_over_eq hS.1
    rw [← MonoidHom.comp_assoc, hg, hf, MonoidHom.comp_id]
  have hfg : f.comp g = MonoidHom.id D := by
    let _ := (perfect_of_universal.{u', v', w, t'} hT).1
    apply hom_over_eq hT.1
    rw [← MonoidHom.comp_assoc, hf, hg, MonoidHom.comp_id]
  let e : E ≃* D :=
    { toFun := f
      invFun := g
      left_inv := DFunLike.congr_fun hgf
      right_inv := DFunLike.congr_fun hfg
      map_mul' := f.map_mul }
  refine ⟨e, hf, fun e' he' => MulEquiv.ext fun x => ?_⟩
  have h : e'.toMonoidHom = f := hf_unique e'.toMonoidHom he'
  exact DFunLike.congr_fun h x

theorem exists_universal_iff_perfect : Spec.ExistsUniversalIffPerfect.{w, t} := by
  intro G _
  constructor
  · rintro ⟨N, E, _, _, S, hS⟩
    exact (perfect_of_universal.{w, w, w, t} hS).2
  · intro hG
    exact ⟨_, _, _, _, CentralPresentation.extension (freePresentation G),
      presentation_isUniversal.{w, w, w, t} (freePresentation G)⟩

theorem universal_kernel_homology : Spec.UniversalKernelHomology.{u, v, w, t} := by
  intro N E G _ _ _ S hS
  let _ := (perfect_of_universal.{u, v, w, t} hS).2
  let P := freePresentation G
  obtain ⟨e, he, _⟩ :=
    universal_comparison.{w, w, w, 0, u, v, t} (presentation_isUniversal P) hS
  have hKer : (projection P).ker.map e.toMonoidHom = S.rightHom.ker := by
    change S.rightHom.comp e.toMonoidHom = projection P at he
    rw [← he, ← MonoidHom.comap_ker, Subgroup.map_comap_eq_self_of_surjective e.surjective]
  obtain ⟨hopfKernel, hopf, d, hd, hHopf⟩ :=
    CentralPresentation.homology_kernel_identification P
  let kernelComparison :=
    (e.subgroupMap (projection P).ker).trans (MulEquiv.subgroupCongr hKer)
  refine ⟨hopfKernel.trans kernelComparison, e, hopf, d, he, hd, fun x => ⟨(hHopf x).1, ?_⟩⟩
  change e (hopfKernel x).val = e (CentralPresentation.kernelInclusion P (hopf x))
  exact congrArg e (hHopf x).2

theorem universal_presentation : Spec.UniversalPresentation.{u, v, w, t} := by
  intro R F G _ _ _ _ _ S
  have hS := presentation_isUniversal.{u, v, w, t} S
  exact ⟨CentralPresentation.extension S, rfl, rfl, hS,
    CentralPresentation.presentation_perfect S, universal_kernel_homology.{v, v, w, t} hS⟩

end ALG02GroupTheory.Extensions.UniversalCentral
