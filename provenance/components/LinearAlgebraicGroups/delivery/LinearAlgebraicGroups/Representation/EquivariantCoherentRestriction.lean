import Specs.LinearAlgebraicGroups.Representation.EquivariantCoherentRestriction
import LinearAlgebraicGroups.Representation.EquivariantAffineModules
import LinearAlgebraicGroups.Representation.EquivariantCoherentOpenExtension
import LinearAlgebraicGroups.Representation.EquivariantCoherentSupportFiltration
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.EquivariantCoherentRestriction

open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.EquivariantAffineModules
open Specs.EquivariantCoherentRestriction
open Specs.CharacterDescent (Character)
open EquivariantAffineModules
open EquivariantCoherentOpenExtension
  (restrictCoherent restrictCoherent_isEquivariantPullback openPullback_shortExact)
open EquivariantCoherentSubobjectExtension
  (pullbackLinearization_map linearized_of_pullbackLinearizationComparison)
open Specs.EquivariantCoherentOpenExtension (supportedClasses)
open SheafOfModules Scheme.Modules

noncomputable section

/-- The pullback to the open complement of a closed direct image is zero.
Disjointness of the two ranges suffices for this vanishing. -/
theorem openPullback_pushforward_isZero {X Y Z : Scheme} (i : Z ⟶ X) (j : Y ⟶ X)
    [IsOpenImmersion j] (h : Disjoint (Set.range i) (Set.range j)) (M : Z.Modules) :
    IsZero ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pushforward i).obj M)) := by
  let N := (Scheme.Modules.pushforward i).obj M
  apply ((Scheme.Modules.restrictFunctorIsoPullback j).app N).isZero_iff.mp
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Scheme.Modules.hom_ext
  intro U
  have hU : i ⁻¹ᵁ (j ''ᵁ U) = ⊥ := by
    apply bot_unique
    intro z hz
    change i z ∈ j '' (U : Set Y) at hz
    obtain ⟨y, _, hy⟩ := hz
    exact (Set.disjoint_left.mp h (Set.mem_range_self z) ⟨y, hy⟩).elim
  let S : TopCat.Sheaf Ab Z := ⟨M.presheaf, M.isSheaf⟩
  have hz : IsZero Γ(M, i ⁻¹ᵁ (j ''ᵁ U)) := (S.isTerminalOfEqEmpty hU).isZero
  have hh : IsZero Γ(N.restrict j, U) := (N.restrictAppIso j U).isZero_iff.mpr
    (by rw [Scheme.Modules.pushforward_obj_obj]; exact hz)
  exact hh.eq_of_src _ _

/-- The composition on classes of a direct image and restriction to a disjoint
open is zero once the maps have the specified effect on sheaves. -/
theorem restrict_comp_push_eq_zero {k : Type u} [Field k] {T : GroupScheme k} {X Y Z : SchemeOver k}
    {a : ModObj T.X X} {b : ModObj T.X Z} {c : ModObj T.X Y}
    (i : Z ⟶ X) (j : Y ⟶ X) [IsOpenImmersion j.left]
    (h : Disjoint (Set.range i.left) (Set.range j.left))
    (push : GZero b →ₗ[CharacterRing T] GZero a) (res : GZero a →ₗ[CharacterRing T] GZero c)
    (hpush : ∀ H, ∃ (F : EquivariantCoherent a), Nonempty
      (F.sheaf ≅ (Scheme.Modules.pushforward i.left).obj H.sheaf) ∧
        push (classOf H) = classOf F)
    (hres : ∀ F, ∃ (H : EquivariantCoherent c), Nonempty (Pull j F.sheaf ≅ H.sheaf) ∧
      res (classOf F) = classOf H) : res.comp push = 0 := by
  apply classMap_ext
  intro H
  obtain ⟨F, ⟨e⟩, hF⟩ := hpush H
  obtain ⟨K, ⟨d⟩, hK⟩ := hres F
  rw [LinearMap.comp_apply, hF, hK, LinearMap.zero_apply]
  apply classOf_isZero
  exact ((Scheme.Modules.pullback j.left).mapIso e).symm.trans d |>.isZero_iff.mp
    (openPullback_pushforward_isZero i.left j.left h H.sheaf)


section TwistRestriction

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {c : ModObj T.X Y}

open private evalPullIso twistLinearizationIso twistLinearizationIso_hom
  from LinearAlgebraicGroups.Representation.EquivariantAffineModules

private theorem projectedCharacter_pullback (f : Y ⟶ X) (χ : Character T) :
    (𝟙 T.X ⊗ₘ f).left.appTop ((fst T.X X).left.appTop (characterFunction χ)) =
      (fst T.X Y).left.appTop (characterFunction χ) := by
  have h : (𝟙 T.X ⊗ₘ f) ≫ fst T.X X = fst T.X Y := by simp
  change (((𝟙 T.X ⊗ₘ f).left.appTop).hom.comp ((fst T.X X).left.appTop).hom) _ = _
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ← Over.comp_left, h]

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackLinearization_twist_hom {f : Y ⟶ X}
    (hf : IsEquivariantMap a c f) {F : X.left.Modules}
    (L : Linearization a F) (χ : Character T) :
    (pullbackLinearization hf (twistLinearization L χ)).iso.hom =
      (pullbackLinearization hf L).iso.hom ≫
        multiply _ ((fst T.X Y).left.appTop (characterFunction χ)) := by
  simp only [pullbackLinearization, pullbackLinearizationIso, evalPullIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  change _ ≫ _ ≫ (Scheme.Modules.pullback (𝟙 T.X ⊗ₘ f).left).map
      (twistLinearizationIso (a := a) χ L.iso).hom ≫ _ = _
  rw [twistLinearizationIso_hom, Functor.map_comp, Category.assoc, pullback_multiply,
    projectedCharacter_pullback, multiply_natural_assoc, multiply_natural]

private theorem isLinearizedMap_of_twist {F H : EquivariantCoherent a} {χ : Character T}
    (e : F.sheaf ≅ H.sheaf)
    (he : H.lin.iso.hom =
      (Scheme.Modules.pullback (snd T.X X).left).map e.inv ≫ F.lin.iso.hom ≫
        multiply _ ((fst T.X X).left.appTop (characterFunction χ)) ≫
        (Scheme.Modules.pullback a.smul.left).map e.hom) :
    IsLinearizedMap (twistLinearization F.lin χ) H.lin e.hom := by
  unfold IsLinearizedMap
  change (twistLinearizationIso (a := a) χ F.lin.iso).hom ≫ _ = _
  rw [twistLinearizationIso_hom, he, ← Functor.map_comp_assoc, e.hom_inv_id,
    (Scheme.Modules.pullback (snd T.X X).left).map_id, Category.id_comp, Category.assoc]

theorem restrictCoherent_isTwist (j : Y ⟶ X) [IsOpenImmersion j.left]
    (hj : IsEquivariantMap a c j) {χ : Character T} {F H : EquivariantCoherent a}
    (h : IsTwist χ F H) : IsTwist χ (restrictCoherent j hj F) (restrictCoherent j hj H) := by
  obtain ⟨e, he⟩ := h
  let P := Scheme.Modules.pullback j.left
  let d := P.mapIso e
  refine ⟨d, ?_⟩
  have hw := pullbackLinearization_map hj e.hom (isLinearizedMap_of_twist e he)
  unfold IsLinearizedMap at hw
  rw [pullbackLinearization_twist_hom, Category.assoc] at hw
  let P₀ := Scheme.Modules.pullback (snd T.X Y).left
  let P₁ := Scheme.Modules.pullback c.smul.left
  let r := (fst T.X Y).left.appTop (characterFunction χ)
  change (pullbackLinearization hj H.lin).iso.hom =
    P₀.map d.inv ≫ (pullbackLinearization hj F.lin).iso.hom ≫
      multiply (Pull c.smul (Pull j F.sheaf)) r ≫ P₁.map d.hom
  change (pullbackLinearization hj F.lin).iso.hom ≫
      multiply (Pull c.smul (Pull j F.sheaf)) r ≫ P₁.map d.hom =
    P₀.map d.hom ≫ (pullbackLinearization hj H.lin).iso.hom at hw
  rw [hw, ← P₀.map_comp_assoc, d.inv_hom_id, P₀.map_id, Category.id_comp]

end TwistRestriction

section OpenClassMap

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {c : ModObj T.X Y}

theorem classOf_twist {F H : EquivariantCoherent a} {χ : Character T}
    (h : IsTwist χ F H) : classOf H = eChar χ • classOf F := by
  have hm : Finsupp.single H 1 - eChar χ • Finsupp.single F 1 ∈ relationSubmodule a :=
    Submodule.subset_span (Or.inr ⟨χ, F, H, h, rfl⟩)
  have he := LinearMap.mem_ker.mp (show _ ∈ LinearMap.ker (relationSubmodule a).mkQ by
    rw [Submodule.ker_mkQ]
    exact hm)
  simpa only [classOf, LinearMap.map_sub, LinearMap.map_smul, sub_eq_zero] using he

/-- The character-linear map induced by open restriction. -/
def restrictClasses (j : Y ⟶ X) [IsOpenImmersion j.left]
    (hj : IsEquivariantMap a c j) : GZero a →ₗ[CharacterRing T] GZero c := by
  refine liftClassMap (fun F => classOf (restrictCoherent j hj F)) ?_ ?_
  · intro F H K f g w hf hg hE
    exact classOf_exact ((ShortComplex.mk f g w).map (Scheme.Modules.pullback j.left)).zero
      (pullbackLinearization_map hj f hf) (pullbackLinearization_map hj g hg)
      (openPullback_shortExact j.left _ hE)
  · intro χ F H h
    exact classOf_twist (restrictCoherent_isTwist j hj h)

@[simp]
theorem restrictClasses_classOf (j : Y ⟶ X) [IsOpenImmersion j.left]
    (hj : IsEquivariantMap a c j) (F : EquivariantCoherent a) :
    restrictClasses j hj (classOf F) = classOf (restrictCoherent j hj F) := by
  unfold restrictClasses
  rw [liftClassMap_classOf]

end OpenClassMap

section ClassExactness

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y Z : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Z} {c : ModObj T.X Y}

/-- Equivariant isomorphic coherent sheaves have equal classes. -/
theorem classOf_eq_of_linearizedIso (hT : IsSplitTorus T)
    {F H : EquivariantCoherent a}
    (e : F.sheaf ≅ H.sheaf) (he : EquivariantHom e.hom) :
    classOf H = classOf F := by
  have ht : IsTwist (1 : Character T) F H := by
    refine ⟨e, ?_⟩
    rw [characterFunction_one hT, map_one, multiply_one, Category.id_comp]
    unfold EquivariantHom at he
    rw [he, ← Functor.map_comp_assoc, e.inv_hom_id,
      (Scheme.Modules.pullback (snd T.X X).left).map_id, Category.id_comp]
  rw [classOf_twist ht, eChar, map_one, one_smul]

theorem supportedClasses_le_ker (j : Y ⟶ X) [IsOpenImmersion j.left]
    (hj : IsEquivariantMap a c j) :
    supportedClasses a j ≤ LinearMap.ker (restrictClasses j hj) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨F, hF, rfl⟩
  apply LinearMap.mem_ker.mpr
  rw [restrictClasses_classOf]
  exact classOf_isZero _ hF

/-- Presentations of the class modules reduce open restriction to the
existence of coherent extensions and their relations modulo supported classes. -/
theorem open_exact_of_class_lifts (j : Y ⟶ X) [IsOpenImmersion j.left]
    (hj : IsEquivariantMap a c j)
    (liftedClass : EquivariantCoherent c → GZero a ⧸ supportedClasses a j)
    (exactRelation : ∀ {F H K : EquivariantCoherent c} (f : F.sheaf ⟶ H.sheaf)
      (g : H.sheaf ⟶ K.sheaf) (w : f ≫ g = 0), EquivariantHom f → EquivariantHom g →
      (ShortComplex.mk f g w).ShortExact → liftedClass H = liftedClass F + liftedClass K)
    (twistRelation : ∀ {χ : Character T} {F H : EquivariantCoherent c},
      IsTwist χ F H → liftedClass H = eChar χ • liftedClass F)
    (hextend : ∀ H, ∃ F, classOf (restrictCoherent j hj F) = classOf H)
    (hchoice : ∀ F, liftedClass (restrictCoherent j hj F) =
      (supportedClasses a j).mkQ (classOf F)) :
    LinearMap.ker (restrictClasses j hj) = supportedClasses a j ∧
      Function.Surjective (restrictClasses j hj) := by
  let res := restrictClasses j hj
  let S := supportedClasses a j
  let L := liftClassMap liftedClass exactRelation twistRelation
  have hleft : L.comp res = S.mkQ := by
    apply classMap_ext
    intro F
    rw [LinearMap.comp_apply, restrictClasses_classOf, liftClassMap_classOf]
    exact hchoice F
  constructor
  · apply le_antisymm ?_ (supportedClasses_le_ker j hj)
    intro x hx
    have hz : S.mkQ x = 0 := by
      rw [← hleft, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]
    have hm : x ∈ LinearMap.ker S.mkQ := LinearMap.mem_ker.mpr hz
    simpa only [Submodule.ker_mkQ] using hm
  · have h : (LinearMap.range res).mkQ = 0 := by
      apply classMap_ext
      intro H
      obtain ⟨F, hF⟩ := hextend H
      rw [← hF, ← restrictClasses_classOf j hj, LinearMap.zero_apply]
      apply LinearMap.mem_ker.mp
      rw [Submodule.ker_mkQ]
      exact LinearMap.mem_range_self res (classOf F)
    apply LinearMap.range_eq_top.mp
    rw [← Submodule.ker_mkQ (LinearMap.range res), h, LinearMap.ker_zero]

/-- Once closed direct image spans the supported classes, open exactness
gives the localization sequence with the actual maps on classes. -/
theorem restrictionSequence_of_supportedClasses
    (i : Z ⟶ X) (j : Y ⟶ X) [IsOpenImmersion j.left]
    (hj : IsEquivariantMap a c j) (hd : Disjoint (Set.range i.left) (Set.range j.left))
    (push : GZero b →ₗ[CharacterRing T] GZero a)
    (hpush : ∀ H, ∃ (F : EquivariantCoherent a) (e : F.sheaf ≅
        (Scheme.Modules.pushforward i.left).obj H.sheaf),
      IsEquivariantPushforward i H F e ∧ push (classOf H) = classOf F)
    (hker : LinearMap.ker (restrictClasses j hj) = supportedClasses a j)
    (hsurj : Function.Surjective (restrictClasses j hj))
    (hsupp : supportedClasses a j ≤ LinearMap.range push) :
    HasRestrictionSequence (a := a) (b := b) (c := c) i j := by
  let res := restrictClasses j hj
  have hres (F : EquivariantCoherent a) :
      ∃ (H : EquivariantCoherent c) (e : Pull j F.sheaf ≅ H.sheaf),
        IsEquivariantPullback j F H e ∧ res (classOf F) = classOf H :=
    ⟨restrictCoherent j hj F, Iso.refl _, restrictCoherent_isEquivariantPullback j hj F,
      restrictClasses_classOf j hj F⟩
  have hzero : res.comp push = 0 := by
    apply restrict_comp_push_eq_zero i j hd push res
    · intro H
      obtain ⟨F, e, _, hF⟩ := hpush H
      exact ⟨F, ⟨e⟩, hF⟩
    · intro F
      obtain ⟨H, e, _, hH⟩ := hres F
      exact ⟨H, ⟨e⟩, hH⟩
  refine ⟨push, res, LinearMap.exact_of_comp_of_mem_range hzero ?_, hsurj, hpush, hres⟩
  intro x hx
  apply hsupp
  rw [← hker]
  exact LinearMap.mem_ker.mpr hx

end ClassExactness

section CoherentLiftComparison

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {c : ModObj T.X Y}

private theorem linearizedMap_comp {F H K : X.left.Modules}
    {L : Linearization a F} {J : Linearization a H} {N : Linearization a K}
    {f : F ⟶ H} {g : H ⟶ K}
    (hf : IsLinearizedMap L J f) (hg : IsLinearizedMap J N g) :
    IsLinearizedMap L N (f ≫ g) := by
  unfold IsLinearizedMap at *
  rw [(Scheme.Modules.pullback a.smul.left).map_comp,
    (Scheme.Modules.pullback (snd T.X X).left).map_comp, ← Category.assoc,
    hf, Category.assoc, hg, Category.assoc]

private theorem linearizedMap_inv {F H : X.left.Modules}
    {L : Linearization a F} {J : Linearization a H}
    (e : F ≅ H) (he : IsLinearizedMap L J e.hom) :
    IsLinearizedMap J L e.inv := by
  let A := (Scheme.Modules.pullback a.smul.left).mapIso e
  let B := (Scheme.Modules.pullback (snd T.X X).left).mapIso e
  change L.iso.hom ≫ A.hom = B.hom ≫ J.iso.hom at he
  change J.iso.hom ≫ A.inv = B.inv ≫ L.iso.hom
  apply (cancel_epi B.hom).mp
  rw [← Category.assoc, ← he, Category.assoc, A.hom_inv_id, Category.comp_id,
    B.hom_inv_id_assoc]

open private twistLinearizationIso twistLinearizationIso_hom
  from LinearAlgebraicGroups.Representation.EquivariantAffineModules

private theorem linearizedMap_twist {F H : X.left.Modules}
    {L : Linearization a F} {J : Linearization a H}
    {f : F ⟶ H} (hf : IsLinearizedMap L J f) (χ : Character T) :
    IsLinearizedMap (twistLinearization L χ) (twistLinearization J χ) f := by
  unfold IsLinearizedMap at hf ⊢
  change (twistLinearizationIso (a := a) χ L.iso).hom ≫ _ =
    _ ≫ (twistLinearizationIso (a := a) χ J.iso).hom
  rw [twistLinearizationIso_hom, twistLinearizationIso_hom,
    Category.assoc, multiply_natural, ← Category.assoc, hf, Category.assoc]

/-- An isomorphism of actual coherent sheaves that intertwines their
linearizations. -/
def IsLinearlyIsomorphic (F H : EquivariantCoherent a) : Prop :=
  ∃ e : F.sheaf ≅ H.sheaf, EquivariantHom e.hom

private theorem linearlyIsomorphic_trans {F H K : EquivariantCoherent a}
    (e : IsLinearlyIsomorphic F H) (d : IsLinearlyIsomorphic H K) :
    IsLinearlyIsomorphic F K := by
  obtain ⟨e, he⟩ := e
  obtain ⟨d, hd⟩ := d
  exact ⟨e ≪≫ d, linearizedMap_comp he hd⟩

private theorem linearlyIsomorphic_symm {F H : EquivariantCoherent a}
    (e : IsLinearlyIsomorphic F H) : IsLinearlyIsomorphic H F := by
  obtain ⟨e, he⟩ := e
  exact ⟨e.symm, linearizedMap_inv e he⟩

private theorem linearlyIsomorphic_refl (F : EquivariantCoherent a) :
    IsLinearlyIsomorphic F F := by
  refine ⟨Iso.refl _, ?_⟩
  unfold EquivariantHom
  rw [Iso.refl_hom, (Scheme.Modules.pullback a.smul.left).map_id,
    (Scheme.Modules.pullback (snd T.X X).left).map_id, Category.comp_id, Category.id_comp]

private theorem linearlyIsomorphic_of_twists
    {R S F H : EquivariantCoherent a} {χ : Character T}
    (e : IsLinearlyIsomorphic R F) (hS : IsTwist χ R S) (hH : IsTwist χ F H) :
    IsLinearlyIsomorphic S H := by
  obtain ⟨e₀, he₀⟩ := e
  obtain ⟨e₁, he₁⟩ := hS
  obtain ⟨e₂, he₂⟩ := hH
  refine ⟨e₁.symm ≪≫ e₀ ≪≫ e₂, ?_⟩
  have h₁ := linearizedMap_inv e₁ (isLinearizedMap_of_twist e₁ he₁)
  have h₀ := linearizedMap_twist he₀ χ
  have h₂ := isLinearizedMap_of_twist e₂ he₂
  exact linearizedMap_comp h₁ (linearizedMap_comp h₀ h₂)

/-- The open restriction map is onto and has the expected supported kernel
once coherent objects and exact sequences lift and extensions compare
modulo supported classes. -/
theorem open_exact_of_lift_comparisons (hT : IsSplitTorus T)
    (j : Y ⟶ X) [IsOpenImmersion j.left] (hj : IsEquivariantMap a c j)
    (extend : ∀ H, ∃ F, IsLinearlyIsomorphic (restrictCoherent j hj F) H)
    (compare : ∀ F H, IsLinearlyIsomorphic (restrictCoherent j hj F) (restrictCoherent j hj H) →
      (supportedClasses a j).mkQ (classOf F) = (supportedClasses a j).mkQ (classOf H))
    (extendExact : ∀ {F H K : EquivariantCoherent c} (f : F.sheaf ⟶ H.sheaf)
      (g : H.sheaf ⟶ K.sheaf) (w : f ≫ g = 0), EquivariantHom f → EquivariantHom g →
      (ShortComplex.mk f g w).ShortExact →
      ∃ (F' H' K' : EquivariantCoherent a) (f' : F'.sheaf ⟶ H'.sheaf)
        (g' : H'.sheaf ⟶ K'.sheaf) (w' : f' ≫ g' = 0),
        EquivariantHom f' ∧ EquivariantHom g' ∧ (ShortComplex.mk f' g' w').ShortExact ∧
        IsLinearlyIsomorphic (restrictCoherent j hj F') F ∧
        IsLinearlyIsomorphic (restrictCoherent j hj H') H ∧
        IsLinearlyIsomorphic (restrictCoherent j hj K') K) :
    LinearMap.ker (restrictClasses j hj) = supportedClasses a j ∧
      Function.Surjective (restrictClasses j hj) := by
  let R := restrictCoherent j hj
  let q := (supportedClasses a j).mkQ
  choose E hE using extend
  let cls (H : EquivariantCoherent c) := q (classOf (E H))
  have hcls {H : EquivariantCoherent c} (F : EquivariantCoherent a)
      (e : IsLinearlyIsomorphic (R F) H) : cls H = q (classOf F) :=
    compare (E H) F (linearlyIsomorphic_trans (hE H) (linearlyIsomorphic_symm e))
  apply open_exact_of_class_lifts j hj cls
  · intro F H K f g w hf hg hExact
    obtain ⟨F', H', K', f', g', w', hf', hg', hExact', hF, hH, hK⟩ :=
      extendExact f g w hf hg hExact
    rw [hcls F' hF, hcls H' hH, hcls K' hK, classOf_exact w' hf' hg' hExact', map_add]
  · intro χ F H hTwist
    let F' := twistCoherent (E F) χ
    have hF' := twistCoherent_isTwist (E F) χ
    have hR := restrictCoherent_isTwist j hj hF'
    have hH : IsLinearlyIsomorphic (R F') H :=
      linearlyIsomorphic_of_twists (hE F) hR hTwist
    rw [hcls F' hH, classOf_twist hF', LinearMap.map_smul]
  · intro H
    obtain ⟨e, he⟩ := hE H
    exact ⟨E H, (classOf_eq_of_linearizedIso hT e he).symm⟩
  · intro F
    exact hcls F (linearlyIsomorphic_refl (R F))

end CoherentLiftComparison

section Localization

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {c : ModObj T.X Y}

private theorem restrictCoherent_iso (j : Y ⟶ X) [IsOpenImmersion j.left]
    (hj : IsEquivariantMap a c j) {F : EquivariantCoherent a} {H : EquivariantCoherent c}
    (e : Pull j F.sheaf ≅ H.sheaf) (he : IsEquivariantPullback j F H e) :
    IsLinearlyIsomorphic (restrictCoherent j hj F) H :=
  ⟨e, linearized_of_pullbackLinearizationComparison hj F.lin H.lin e he⟩

private theorem open_exact (j : Y ⟶ X) [IsOpenImmersion j.left]
    (setting : Specs.EquivariantCoherentOpenExtension.IsExtensionSetting a c j) :
    LinearMap.ker (restrictClasses j setting.equivariant) = supportedClasses a j ∧
      Function.Surjective (restrictClasses j setting.equivariant) := by
  apply open_exact_of_lift_comparisons setting.split j setting.equivariant
  · intro H
    obtain ⟨F, e, he⟩ := EquivariantCoherentOpenExtension.coherentExtension j setting H
    exact ⟨F, restrictCoherent_iso j setting.equivariant e he⟩
  · intro F G h
    obtain ⟨d, hd⟩ := h
    let H := restrictCoherent j setting.equivariant F
    let K := restrictCoherent j setting.equivariant G
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hclasses⟩ :=
      EquivariantCoherentOpenExtension.graphComparison j setting F G H K
        (Iso.refl _) (Iso.refl _) d
        (restrictCoherent_isEquivariantPullback j setting.equivariant F)
        (restrictCoherent_isEquivariantPullback j setting.equivariant G) hd
    exact hclasses
  · intro F H K f g w hf hg hExact
    obtain ⟨F', H', K', f', g', w', eF, eH, eK, hf', hg', hex', hF, hH, hK, _, _⟩ :=
      EquivariantCoherentOpenExtension.shortExactExtension j setting F H K f g w hf hg hExact
    exact ⟨F', H', K', f', g', w', hf', hg', hex',
      restrictCoherent_iso j setting.equivariant eF hF,
      restrictCoherent_iso j setting.equivariant eH hH,
      restrictCoherent_iso j setting.equivariant eK hK⟩

/-- The equivariant coherent localization sequence for an invariant closed
immersion and its open complement. -/
theorem restrictionSequence : RestrictionSequence.{u} := by
  intro k _ T X Y Z a b c i j hT hfinite hseparated hcompact hcover hi hj heI heJ hrange
  let : IsOpenImmersion j.left := hj
  let setting : Specs.EquivariantCoherentOpenExtension.IsExtensionSetting a c j :=
    ⟨hT, hfinite, hseparated, hcompact, hcover, heJ⟩
  obtain ⟨hker, hsurj⟩ := open_exact j setting
  obtain ⟨D, _, hpush, hclass, hfiltration⟩ :=
    EquivariantCoherentSupportFiltration.supportFiltration a b c i j
      hT hfinite hseparated hcompact hcover hi hj heI heJ hrange
  have hd : Disjoint (Set.range i.left) (Set.range j.left) := by
    rw [hrange]
    exact disjoint_compl_right
  refine restrictionSequence_of_supportedClasses i j heJ hd D.pushClasses
    (fun H => ⟨D.push H, Iso.refl _, hpush H, hclass H⟩) hker hsurj ?_
  apply Submodule.span_le.mpr
  rintro _ ⟨F, hF, rfl⟩
  obtain ⟨_, _, _, _, _, hmem⟩ := hfiltration F hF
  exact hmem

end Localization

end

end LinearAlgebraicGroups.Representation.EquivariantCoherentRestriction
