import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantCoherentSubobjectExtension
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.EquivariantCoherentSubobjectExtension

open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.EquivariantAffineModules
open Specs.EquivariantCoherentSubobjectExtension
open Specs.CharacterDescent (Character)
open EquivariantAffineModules
open SheafOfModules Scheme.Modules

noncomputable section

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A finite local presentation restricts to a finite local presentation
along an open immersion. -/
theorem openPullback_finitePresentation {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (hM : M.IsFinitePresentation) :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf := { app U := (f.appIso U.unop).inv }
  let : IsIso α := NatIso.isIso_of_isIso_app _
  let G := f.opensFunctor
  let φ : Y.ringCatSheaf ⟶ (G.sheafPushforwardContinuous _ _ _).obj X.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  let : IsIso φ := by
    rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    dsimp [φ]
    infer_instance
  let hunitComparison : (SheafOfModules.pushforward φ).obj (unit X.ringCatSheaf) ≅ unit Y.ringCatSheaf :=
    Scheme.Modules.restrictUnitIso f
  have h (U : Y.Opens) (V : X.Opens) (i : G.obj U ⟶ V) :
      PreservesColimitsOfSize.{u, u} <|
        SheafOfModules.pushforward.{u} (R := X.ringCatSheaf.over V)
          (F := Over.post (X := U) G ⋙ Over.map i)
          (((Over.forget U).sheafPushforwardContinuous RingCat.{u}
            ((Opens.grothendieckTopology Y).over U) (Opens.grothendieckTopology Y)).map φ) := by
    let G' := Over.post (X := U) G ⋙ Over.map i
    let : G'.IsContinuous ((Opens.grothendieckTopology Y).over _) ((Opens.grothendieckTopology X).over _) :=
      Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology X).over _) _
    let : G'.IsCocontinuous ((Opens.grothendieckTopology Y).over _) ((Opens.grothendieckTopology X).over _) :=
      isCocontinuous_comp _ _ _ ((Opens.grothendieckTopology X).over _)
    let ψ : Y.ringCatSheaf.over U ⟶
        (G'.sheafPushforwardContinuous RingCat.{u}
          ((Opens.grothendieckTopology Y).over U) ((Opens.grothendieckTopology X).over V)).obj
          (X.ringCatSheaf.over V) :=
      ((Over.forget U).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology Y).over U) (Opens.grothendieckTopology Y)).map φ
    let : (SheafOfModules.pushforward.{u} ψ).IsLeftAdjoint :=
      SheafOfModules.isLeftAdjoint_pushforward_of_isIso ψ
    exact inferInstanceAs (PreservesColimitsOfSize (SheafOfModules.pushforward ψ))

  obtain ⟨P, hP⟩ := hM.exists_quasicoherentData
  let P' := P.pushforward G φ hunitComparison h
  have hpres : SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf)
      ((SheafOfModules.pushforward.{u} φ).obj M) := by
    have hP' : P'.IsFinitePresentation := by
      constructor
      intro i
      constructor
      · constructor
        change Finite (P.presentation i.2.1).generators.I
        let : (P.presentation i.2.1).IsFinite := hP.isFinite_presentation _
        infer_instance
      · constructor
        change Finite (P.presentation i.2.1).relations.I
        let : (P.presentation i.2.1).IsFinite := hP.isFinite_presentation _
        infer_instance
    exact SheafOfModules.IsFinitePresentation.mk (M := (SheafOfModules.pushforward.{u} φ).obj M)
      ⟨P', hP'⟩
  exact (isFinitePresentation Y.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M) hpres

section LinearizedRestriction

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y W : SchemeOver k}
  {a : ModObj T.X X} {c : ModObj T.X Y}

open private comparePull pullCongr_naturality evalPullIso equivariant_actOn transport_eq_evalPullIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

@[reassoc]
private theorem comparePull_naturality {V : SchemeOver k} {F H : X.left.Modules}
    (f : W ⟶ V) (g : V ⟶ X) {h : W ⟶ X} (e : f ≫ g = h)
    (m : F ⟶ H) :
    (comparePull F f g e).hom ≫ (Scheme.Modules.pullback h.left).map m =
      (Scheme.Modules.pullback f.left).map ((Scheme.Modules.pullback g.left).map m) ≫
        (comparePull H f g e).hom := by
  simp only [comparePull, Iso.trans_hom, Category.assoc, pullCongr_naturality]
  rw [← Category.assoc]
  exact congrArg (· ≫ (pullCongr H e).hom)
    (((Scheme.Modules.pullbackComp f.left g.left).hom.naturality m).symm)

@[reassoc]
private theorem comparePull_inv_naturality {V : SchemeOver k} {F H : X.left.Modules}
    (f : W ⟶ V) (g : V ⟶ X) {h : W ⟶ X} (e : f ≫ g = h)
    (m : F ⟶ H) :
    (comparePull F f g e).inv ≫
      (Scheme.Modules.pullback f.left).map ((Scheme.Modules.pullback g.left).map m) =
      (Scheme.Modules.pullback h.left).map m ≫ (comparePull H f g e).inv := by
  apply (cancel_mono (comparePull H f g e).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← comparePull_naturality, Iso.inv_hom_id_assoc]

@[reassoc]
private theorem pullComp_naturality {V : SchemeOver k} {F H : X.left.Modules}
    (f : W ⟶ V) (g : V ⟶ X) (m : F ⟶ H) :
    (pullComp F f g).hom ≫ (Scheme.Modules.pullback (f ≫ g).left).map m =
      (Scheme.Modules.pullback f.left).map ((Scheme.Modules.pullback g.left).map m) ≫
        (pullComp H f g).hom :=
  ((Scheme.Modules.pullbackComp f.left g.left).hom.naturality m).symm

@[reassoc]
private theorem pullComp_inv_naturality {V : SchemeOver k} {F H : X.left.Modules}
    (f : W ⟶ V) (g : V ⟶ X) (m : F ⟶ H) :
    (pullComp F f g).inv ≫
      (Scheme.Modules.pullback f.left).map ((Scheme.Modules.pullback g.left).map m) =
      (Scheme.Modules.pullback (f ≫ g).left).map m ≫ (pullComp H f g).inv :=
  ((Scheme.Modules.pullbackComp f.left g.left).inv.naturality m).symm

@[reassoc]
private theorem evaluateLinearizedMap {V : SchemeOver k} {F H : X.left.Modules}
    {p q : V ⟶ X} {x y : W ⟶ X}
    (L : Pull p F ≅ Pull q F) (K : Pull p H ≅ Pull q H)
    (m : F ⟶ H) (hm : L.hom ≫ (Scheme.Modules.pullback q.left).map m =
      (Scheme.Modules.pullback p.left).map m ≫ K.hom)
    (s : W ⟶ V) (hp : s ≫ p = x) (hq : s ≫ q = y) :
    (evalPullIso L s hp hq).hom ≫ (Scheme.Modules.pullback y.left).map m =
      (Scheme.Modules.pullback x.left).map m ≫ (evalPullIso K s hp hq).hom := by
  simp only [evalPullIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    comparePull_naturality, ← Functor.map_comp_assoc]
  rw [hm, Functor.map_comp, Category.assoc, comparePull_inv_naturality_assoc]

@[reassoc]
private theorem transport_map {Z : SchemeOver k} {F H : X.left.Modules}
    (L : Pull (snd T.X X) F ≅ Pull a.smul F)
    (K : Pull (snd T.X X) H ≅ Pull a.smul H) (m : F ⟶ H)
    (hm : L.hom ≫ (Scheme.Modules.pullback a.smul.left).map m =
      (Scheme.Modules.pullback (snd T.X X).left).map m ≫ K.hom)
    (t : Z ⟶ T.X) (x : Z ⟶ X) :
    (transport a L t x).hom ≫ (Scheme.Modules.pullback (actOn a t x).left).map m =
      (Scheme.Modules.pullback x.left).map m ≫ (transport a K t x).hom := by
  rw [transport_eq_evalPullIso, transport_eq_evalPullIso]
  exact evaluateLinearizedMap L K m hm _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem pullbackLinearization_map {f : Y ⟶ X}
    (hf : IsEquivariantMap a c f) {F H : X.left.Modules}
    {L : Linearization a F} {K : Linearization a H}
    (m : F ⟶ H) (hm : IsLinearizedMap L K m) :
    IsLinearizedMap (pullbackLinearization hf L) (pullbackLinearization hf K)
      ((Scheme.Modules.pullback f.left).map m) := by
  unfold IsLinearizedMap at hm ⊢
  simp only [pullbackLinearization, pullbackLinearizationIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, pullComp_inv_naturality]
  let q := 𝟙 T.X ⊗ₘ f
  have hp : q ≫ snd T.X X = snd T.X Y ≫ f := by simp [q]
  rw [evaluateLinearizedMap_assoc L.iso K.iso m hm q hp hf.symm, pullComp_naturality_assoc]

/-- Open restriction of an equivariant coherent sheaf via actual inverse image. -/

theorem pullbackLinearizationComparison_of_linearized {j : Y ⟶ X} (hj : IsEquivariantMap a c j)
    {F : X.left.Modules} {H : Y.left.Modules}
    (L : Linearization a F) (K : Linearization c H) (e : Pull j F ≅ H) :
    IsLinearizedMap (pullbackLinearization hj L) K e.hom →
      PullbackLinearizationComparison j L K e := by
  intro h S t y
  refine ⟨equivariant_actOn hj, ?_⟩
  have ht := pullbackLinearization_transport hj L.iso t y
  rw [← reassoc_of% ht, Iso.hom_inv_id_assoc]
  rw [transport_map (pullbackLinearizationIso hj L.iso) K.iso e.hom h t y,
    ← Functor.map_comp_assoc, e.inv_hom_id,
    (Scheme.Modules.pullback y.left).map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem linearized_of_evaluation {V Z : SchemeOver k} {F H : X.left.Modules}
    {p q : V ⟶ X} {x y : Z ⟶ X}
    (L : Pull p F ≅ Pull q F) (K : Pull p H ≅ Pull q H)
    (m : F ⟶ H) (l : Z ⟶ V) [Functor.Faithful (Scheme.Modules.pullback l.left)]
    (hp : l ≫ p = x) (hq : l ≫ q = y)
    (hm : (evalPullIso L l hp hq).hom ≫ (Scheme.Modules.pullback y.left).map m =
      (Scheme.Modules.pullback x.left).map m ≫ (evalPullIso K l hp hq).hom) :
    L.hom ≫ (Scheme.Modules.pullback q.left).map m =
      (Scheme.Modules.pullback p.left).map m ≫ K.hom := by
  simp only [evalPullIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    comparePull_naturality, ← comparePull_inv_naturality_assoc] at hm
  have hm' := (cancel_epi (comparePull F l p hp).inv).mp hm
  simp only [← Functor.map_comp_assoc] at hm'
  exact (Scheme.Modules.pullback l.left).map_injective
    ((cancel_mono (comparePull H l q hq).hom).mp hm')

set_option maxHeartbeats 450000 in
set_option backward.isDefEq.respectTransparency false in
theorem linearized_of_pullbackLinearizationComparison {j : Y ⟶ X} (hj : IsEquivariantMap a c j)
    {F : X.left.Modules} {H : Y.left.Modules}
    (L : Linearization a F) (K : Linearization c H) (e : Pull j F ≅ H)
    (h : PullbackLinearizationComparison j L K e) :
    IsLinearizedMap (pullbackLinearization hj L) K e.hom := by
  let Z := T.X ⊗ Y
  let p := snd T.X Y
  let t := fst T.X Y
  let l := lift t p
  have hl : l = 𝟙 Z := by simp [l, p, t, Z]
  let : Functor.Faithful (Scheme.Modules.pullback l.left) := by
    rw [hl, Over.id_left]
    exact Functor.Faithful.of_iso (Scheme.Modules.pullbackId Z.left).symm
  obtain ⟨h₀, he⟩ := h Z t p
  have hq : h₀ = equivariant_actOn hj := Subsingleton.elim _ _
  rw [hq] at he
  have ht := pullbackLinearization_transport hj L.iso t p
  rw [← reassoc_of% ht, Iso.hom_inv_id_assoc] at he
  have he' :
      (transport c (pullbackLinearizationIso hj L.iso) t p).hom ≫
        (Scheme.Modules.pullback (actOn c t p).left).map e.hom =
      (Scheme.Modules.pullback p.left).map e.hom ≫ (transport c K.iso t p).hom := by
    apply (cancel_epi ((Scheme.Modules.pullback p.left).mapIso e).inv).mp
    simp only [Functor.mapIso_inv, ← Functor.map_comp_assoc,
      e.inv_hom_id, (Scheme.Modules.pullback p.left).map_id, Category.id_comp]
    exact he
  rw [transport_eq_evalPullIso, transport_eq_evalPullIso] at he'
  exact linearized_of_evaluation _ _ _ l _ _ he'

end LinearizedRestriction

section LinearizedMaps

variable {k : Type u} [Field k] {T : GroupScheme k} {X : SchemeOver k}
  {a : ModObj T.X X}

private theorem linearizedMap_comp {F H K : X.left.Modules}
    {L : Linearization a F} {J : Linearization a H} {N : Linearization a K}
    {f : F ⟶ H} {g : H ⟶ K}
    (hf : IsLinearizedMap L J f) (hg : IsLinearizedMap J N g) :
    IsLinearizedMap L N (f ≫ g) := by
  unfold IsLinearizedMap at *
  rw [(Scheme.Modules.pullback a.smul.left).map_comp,
    (Scheme.Modules.pullback (snd T.X X).left).map_comp, ← Category.assoc,
    hf, Category.assoc, hg, Category.assoc]

end LinearizedMaps

section Coherence

open LinearAlgebraicGroups.ProjectiveFiniteness (finite_sections_of_isAffineOpen)
open private fromSpecSectionTopIso presentationRestrict_isFinite
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

set_option backward.isDefEq.respectTransparency false in
private theorem exists_finite_presentation_tilde {R : CommRingCat.{u}}
    [IsNoetherianRing R] (G : ModuleCat.{u} R) [Module.Finite R G] :
    ∃ P : (tilde G).Presentation, P.IsFinite := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R G).FG)
  let l := Finsupp.linearCombination R (fun a : (s : Set G) => a.val)
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (LinearMap.ker l)
  let P := presentationTilde G (s : Set G) hs (t : Set ((s : Set G) →₀ R)) ht
  refine ⟨P, ?_⟩
  constructor
  · constructor
    change Finite (↥(s : Set G))
    infer_instance
  · constructor
    change Finite (↥(t : Set ((s : Set G) →₀ R)))
    infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem exists_finite_presentation_spec {R : CommRingCat.{u}}
    [IsNoetherianRing R] (N : (Spec R).Modules) [N.IsQuasicoherent]
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj N)] :
    ∃ P : N.Presentation, P.IsFinite := by
  obtain ⟨P, hP⟩ := exists_finite_presentation_tilde ((moduleSpecΓFunctor (R := R)).obj N)
  have hIso : IsIso (Scheme.Modules.fromTildeΓ (R := R) N) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ (R := R) N).mp inferInstance
  exact ⟨P.ofIsIso (Scheme.Modules.fromTildeΓ (R := R) N), inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_finite_presentation_fromSpec
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (M : Y.Modules) {U : Y.Opens}
    (hU : IsAffineOpen U) [(M.restrict U.ι).IsQuasicoherent]
    [Module.Finite Γ(Y, U) Γ(M, U)] :
    ∃ P : (M.restrict hU.fromSpec).Presentation, P.IsFinite := by
  let R := Γ(Y, U)
  let i := hU.isoSpec.inv
  let N := M.restrict hU.fromSpec
  let G := (moduleSpecΓFunctor (R := R)).obj N
  have hN : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      ((restrictFunctorComp i U.ι).app M).symm
      (Scheme.Modules.isQuasicoherent_restrictFunctor i (M.restrict U.ι))
  have hR : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hG : Module.Finite R G := Module.Finite.equiv (fromSpecSectionTopIso hU M).symm
  exact @exists_finite_presentation_spec R hR N hN hG

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_on_affine_open
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (M : Y.Modules) {U : Y.Opens}
    (hU : IsAffineOpen U) [(M.restrict U.ι).IsQuasicoherent]
    [Module.Finite Γ(Y, U) Γ(M, U)] :
    ∃ P : (M.over U).Presentation, P.IsFinite := by
  let N := M.restrict hU.fromSpec
  obtain ⟨Q, hQ⟩ := exists_finite_presentation_fromSpec M hU
  let r := hU.isoSpec.hom
  let Q' := presentationRestrict r Q
  have hQ' : Q'.IsFinite := presentationRestrict_isFinite r N Q
  have hr : r ≫ hU.fromSpec = U.ι := hU.isoSpec_hom_fromSpec
  let e := ((restrictFunctorComp r hU.fromSpec).app M).symm ≪≫
    (restrictFunctorCongr hr).app M
  let D := overEquiv U
  let d : D.inverse.obj (N.restrict r) ≅ M.over U :=
    D.inverse.mapIso (e ≪≫ ((overFunctorEquiv U).app M).symm) ≪≫ (D.unitIso.app _).symm
  let unitComparison := (U.sheafOfModulesEquivOverInverseUnit Y.ringCatSheaf).symm
  let P' := Q'.map D.inverse unitComparison
  have hP' : P'.IsFinite := by
    constructor
    · constructor
      change Finite (Q'.map D.inverse unitComparison).generators.I
      rw [Presentation.map_generators_I]
      exact GeneratingSections.IsFiniteType.finite
    · constructor
      change Finite (Q'.map D.inverse unitComparison).relations.I
      rw [Presentation.map_relations_I]
      exact GeneratingSections.IsFiniteType.finite
  exact ⟨P'.ofIsIso d.hom, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_of_affineSections {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (h : ∀ (U : X.affineOpens), (M.restrict U.val.ι).IsQuasicoherent ∧
      Module.Finite Γ(X, U.val) Γ(M, U.val)) :
    M.IsFinitePresentation := by
  have hp (U : X.affineOpens) : ∃ P : (M.over U.val).Presentation, P.IsFinite := by
    let := (h U).1
    let := (h U).2
    exact finitePresentation_on_affine_open M U.property
  choose P hP using hp
  let D : M.QuasicoherentData :=
    { I := X.affineOpens
      X := Subtype.val
      coversTop := (Opens.coversTop_iff _ _).mpr (iSup_affineOpens_eq_top X)
      presentation := P }
  have hD : D.IsFinitePresentation := by
    constructor
    exact hP
  exact SheafOfModules.IsFinitePresentation.mk (M := M) ⟨D, hD⟩

end Coherence

section QuasicoherentDirectImage

open PrimeSpectrum

open private QuasicoherentTilde.Aux QuasicoherentTilde.Aux.mk QuasicoherentTilde.Aux.of_le
  QuasicoherentTilde.Aux.existence QuasicoherentTilde.Aux.uniqueness
  QuasicoherentTilde.isLocalizing_iff_aux QuasicoherentTilde.aux_basicOpen_of_aux_restrict
  from Mathlib.AlgebraicGeometry.Modules.Tilde

section OpenDirectImage

variable {X Y : Scheme.{u}} (j : Y ⟶ X) (H : Y.Modules)

private theorem openPushforward_section_ext {I : Type u} (U : I → X.Opens) (V : X.Opens)
    (h : ∀ i, U i ≤ V) (hcov : j ⁻¹ᵁ V ≤ ⨆ i, j ⁻¹ᵁ U i)
    (s t : Γ((Scheme.Modules.pushforward j).obj H, V))
    (e : ∀ i, ((Scheme.Modules.pushforward j).obj H).presheaf.map (homOfLE (h i)).op s =
      ((Scheme.Modules.pushforward j).obj H).presheaf.map (homOfLE (h i)).op t) :
    s = t := by
  let F : TopCat.Sheaf Ab Y := ⟨H.presheaf, H.isSheaf⟩
  exact TopCat.Sheaf.eq_of_locally_eq' F (fun i => j ⁻¹ᵁ U i) (j ⁻¹ᵁ V)
    (fun i => (Opens.map j.base).map (homOfLE (h i))) hcov s t e

set_option backward.isDefEq.respectTransparency false in
private theorem openPushforward_gluing {I : Type u} (U : I → X.Opens) (V : X.Opens)
    (h : ∀ i, U i ≤ V) (hcov : j ⁻¹ᵁ V ≤ ⨆ i, j ⁻¹ᵁ U i)
    (s : ∀ i, Γ((Scheme.Modules.pushforward j).obj H, U i))
    (hs : TopCat.Presheaf.IsCompatible ((Scheme.Modules.pushforward j).obj H).presheaf U s) :
    ∃ t : Γ((Scheme.Modules.pushforward j).obj H, V), ∀ i,
      ((Scheme.Modules.pushforward j).obj H).presheaf.map (homOfLE (h i)).op t = s i := by
  let F : TopCat.Sheaf Ab Y := ⟨H.presheaf, H.isSheaf⟩
  apply ExistsUnique.exists
  refine TopCat.Sheaf.existsUnique_gluing' F (fun i => j ⁻¹ᵁ U i) (j ⁻¹ᵁ V)
    (fun i => (Opens.map j.base).map (homOfLE (h i))) hcov s (fun i l => ?_)
  let e := H.presheaf.map (eqToHom (j.preimage_inf (U := U i) (V := U l))).op
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback e) 
  have hs' := hs i l
  change H.presheaf.map ((Opens.map j.base).map (Opens.infLELeft (U i) (U l))).op (s i) =
    H.presheaf.map ((Opens.map j.base).map (Opens.infLERight (U i) (U l))).op (s l) at hs'
  change H.presheaf.map (eqToHom (j.preimage_inf (U := U i) (V := U l))).op
      (H.presheaf.map (Opens.infLELeft (j ⁻¹ᵁ U i) (j ⁻¹ᵁ U l)).op (s i)) =
    H.presheaf.map (eqToHom (j.preimage_inf (U := U i) (V := U l))).op
      (H.presheaf.map (Opens.infLERight (j ⁻¹ᵁ U i) (j ⁻¹ᵁ U l)).op (s l))
  let s' (i : I) : Γ(H, j ⁻¹ᵁ U i) := s i
  have hc (l' : U i ⊓ U l ⟶ U i)
      (l'' : j ⁻¹ᵁ U i ⊓ j ⁻¹ᵁ U l ⟶ j ⁻¹ᵁ U i) :
      H.presheaf.map (eqToHom (j.preimage_inf (U := U i) (V := U l))).op
          (H.presheaf.map l''.op (s' i)) =
        H.presheaf.map ((Opens.map j.base).map l').op (s' i) := by
    rw [← H.presheaf.map_comp_apply]
    exact congrArg (fun m => H.presheaf.map m (s' i)) (Subsingleton.elim _ _)
  have hd (l' : U i ⊓ U l ⟶ U l)
      (l'' : j ⁻¹ᵁ U i ⊓ j ⁻¹ᵁ U l ⟶ j ⁻¹ᵁ U l) :
      H.presheaf.map (eqToHom (j.preimage_inf (U := U i) (V := U l))).op
          (H.presheaf.map l''.op (s' l)) =
        H.presheaf.map ((Opens.map j.base).map l').op (s' l) := by
    rw [← H.presheaf.map_comp_apply]
    exact congrArg (fun m => H.presheaf.map m (s' l)) (Subsingleton.elim _ _)
  exact (hc _ _).trans (hs'.trans (hd _ _).symm)

end OpenDirectImage

section AffineOpenDirectImage

variable {R : CommRingCat.{u}} {Y : Scheme.{u}} (j : Y ⟶ Spec R) (H : Y.Modules)

set_option backward.isDefEq.respectTransparency false in
private theorem aux_on_principal_open [IsOpenImmersion j] [H.IsQuasicoherent]
    (g : R) (hg : basicOpen g ≤ j.opensRange) :
    QuasicoherentTilde.Aux ((Scheme.Modules.pushforward j).obj H) (basicOpen g) := by
  apply QuasicoherentTilde.aux_basicOpen_of_aux_restrict
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))
  have h : Set.range f ⊆ Set.range j := by
    change (f.opensRange : Set (Spec R)) ⊆ j.opensRange
    rw [Scheme.Hom.opensRange_localizationAway]
    exact hg
  let q := IsOpenImmersion.lift j f h
  have hq : q ≫ j = f := IsOpenImmersion.lift_fac _ _ _
  let : IsOpenImmersion (q ≫ j) := hq ▸ inferInstanceAs (IsOpenImmersion f)
  let : IsOpenImmersion q := IsOpenImmersion.of_comp q j
  let N := (Scheme.Modules.pushforward j).obj H
  let e : N.restrict f ≅ H.restrict q :=
    ((restrictFunctorCongr hq).app N).symm ≪≫
      (restrictFunctorComp q j).app N ≪≫
      (restrictFunctor q).mapIso ((restrictFunctorAdjCounitIso j).app H)
  have hN : (N.restrict f).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of (Localization.Away g))).ringCatSheaf).prop_of_iso e.symm
      (Scheme.Modules.isQuasicoherent_restrictFunctor q H)
  let : (N.restrict f).IsQuasicoherent := hN
  apply (QuasicoherentTilde.isLocalizing_iff_aux _).mp
  exact (isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
-- Adapted from Mathlib/AlgebraicGeometry/Modules/Tilde.lean (QuasicoherentTilde.Aux.of_eq_iSup_basicOpen). Copyright (c) 2024 Weihong Xu. All rights reserved.
-- Released under Apache 2.0, see LICENSE. MathGenome adapts denominator clearing and gluing to the inverse-image cover.
private theorem aux_of_principal_cover [IsOpenImmersion j] [H.IsQuasicoherent]
    {I : Type u} [Finite I] (g : I → R) (hg : j.opensRange = ⨆ i, basicOpen (g i)) :
    QuasicoherentTilde.Aux ((Scheme.Modules.pushforward j).obj H) ⊤ := by
  let M := (Scheme.Modules.pushforward j).obj H
  have hc : j ⁻¹ᵁ (⊤ : (Spec R).Opens) ≤ ⨆ i, j ⁻¹ᵁ basicOpen (g i) := by
    rw [← j.preimage_iSup, ← hg, j.preimage_opensRange, j.preimage_top]
  have h₁ (i : I) : QuasicoherentTilde.Aux M (basicOpen (g i)) :=
    aux_on_principal_open j H (g i) (by rw [hg]; exact le_iSup (fun i => basicOpen (g i)) i)
  have h₂ (i j : I) : QuasicoherentTilde.Aux M (basicOpen (g i * g j)) :=
    QuasicoherentTilde.Aux.of_le _ (basicOpen_mul_le_left _ _) (h₁ i)
  have hgle (i : I) : basicOpen (g i) ≤ (⊤ : (Spec R).Opens) := le_top
  have hug (i : I) (m : ℕ) :
      IsUnit (algebraMap R (Module.End R Γ(M, basicOpen (g i))) (g i ^ m)) := by
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (g i) le_rfl).pow m
  -- We show existence and uniqueness separately.
  refine QuasicoherentTilde.Aux.mk (fun f hf s ↦ ?_) (fun f hf t hs ↦ ?_)
  · have hfgi (i : I) : basicOpen (f * g i) ≤ basicOpen (g i) := basicOpen_mul_le_right f (g i)
    let s' (i : I) : Γ(M, basicOpen (f * g i)) :=
      M.presheaf.map (homOfLE <| basicOpen_mul_le_left f (g i)).op s
    /- By `h₁`, up to a factor of `f ^ N`, the restrictions of `s` to `D(f) ∩ D(gᵢ)` lift
    to sections `tᵢ` over `D(gᵢ)`. -/
    obtain ⟨N, t, ht⟩ : ∃ (N : ℕ) (t : ∀ i, Γ(M, basicOpen (g i))),
        ∀ i, f ^ N • s' i = M.presheaf.map (homOfLE (basicOpen_mul_le_right f (g i))).op (t i) := by
      have (i : I) : ∃ (n : ℕ) (t : Γ(M, basicOpen (g i))),
          f ^ n • s' i = M.presheaf.map (homOfLE (hfgi i)).op t := by
        obtain ⟨n, t', ht'⟩ := QuasicoherentTilde.Aux.existence (h₁ i) (f * g i) (hfgi i) (s' i)
        rw [mul_pow, mul_smul, smul_comm] at ht'
        obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv (hug i n)
        use n, ψ t'
        apply (M.isSMulRegular_of_le_basicOpen (basicOpen_mul_le_right f (g i))).pow n
        dsimp
        rw [← ht', ← Scheme.Modules.map_smul_Spec]
        congr 1
        exact congr($hψ t').symm
      choose n t' ht' using this
      have (i : I) : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have hN (i : I) : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by grind
      refine ⟨⨆ i, n i, fun i ↦ f ^ ((⨆ i, n i) - n i) • t' i, fun i ↦ ?_⟩
      conv_lhs => rw [hN i]
      rw [pow_add, mul_smul, ht', M.map_smul_Spec]
    /- By `h₂`, up to a factor of `f ^ K`, the restrictions of `tᵢ` and `tⱼ` to
    to `D(gᵢ) ∩ D(gⱼ)` agree. -/
    obtain ⟨K, hK⟩ : ∃ (K : ℕ), ∀ (i j : I),
        M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ K • t i) =
          M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ K • t j) := by
      have (i j : I) : ∃ (m : ℕ),
          M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (f ^ m • t i) =
            M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (f ^ m • t j) := by
        have := QuasicoherentTilde.Aux.uniqueness (h₂ i j) (f * (g i * g j)) (basicOpen_mul_le_right _ _)
          (M.presheaf.map (homOfLE (basicOpen_mul_le_left (g i) (g j))).op (t i) -
            M.presheaf.map (homOfLE (basicOpen_mul_le_right (g i) (g j))).op (t j)) ?_
        · obtain ⟨m, hm⟩ := this
          use m
          apply (M.isSMulRegular_of_le_basicOpen le_rfl).pow m
          simpa [M.map_smul_Spec _ (f ^ m), ← mul_smul, ← mul_smul, ← mul_pow, ← mul_comm f,
            smul_sub, sub_eq_zero] using hm
        · have hfgigi : basicOpen (f * (g i * g j)) ≤ basicOpen (f * g i) := by
            rw [← mul_assoc]
            exact basicOpen_mul_le_left _ _
          have hfgigj : basicOpen (f * (g i * g j)) ≤ basicOpen (f * g j) := by
            rw [mul_comm (g i) (g j), ← mul_assoc]
            exact basicOpen_mul_le_left _ _
          rw [map_sub, ← M.presheaf.map_comp_apply, ← op_comp, ← M.presheaf.map_comp_apply,
            ← op_comp, homOfLE_comp, homOfLE_comp, ← homOfLE_comp hfgigi (hfgi i),
            ← homOfLE_comp hfgigj (hfgi j), op_comp, M.presheaf.map_comp_apply, ← ht i,
            M.map_smul_Spec, ← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, op_comp,
            M.presheaf.map_comp_apply, ← ht j, M.map_smul_Spec, ← M.presheaf.map_comp_apply,
            ← op_comp, homOfLE_comp]
          simp
      choose m hm using this
      let K := ⨆ i, ⨆ j, m i j
      refine ⟨K, fun i j ↦ ?_⟩
      have : m i j ≤ K :=
        le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) _)
      have : K = (K - m i j) + m i j := by lia
      rw [this, pow_add, mul_smul, mul_smul, M.map_smul_Spec, M.map_smul_Spec _ (f ^ (K - m i j)),
        hm i j]
    -- So up to a factor of `f ^ (N + K)`, the `tᵢ` glue.
    refine ⟨N + K, ?_⟩
    have := openPushforward_gluing j H (fun i ↦ basicOpen (g i)) ⊤ hgle hc
      (fun i ↦ f ^ K • t i) ?_
    · obtain ⟨a, ha⟩ := this
      use a
      refine openPushforward_section_ext j H (fun i ↦ basicOpen (f * g i)) _
          (fun i ↦ basicOpen_mul_le_left f (g i)) ?_ _ _ ?_
      · simp only [basicOpen_mul]
        simp_rw [j.preimage_inf, ← inf_iSup_eq]
        exact le_inf le_rfl (le_trans ((Opens.map j.base).monotone le_top) hc)
      · intro i
        rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp (basicOpen_mul_le_right _ _) (hgle i), op_comp, M.presheaf.map_comp_apply,
          M.map_smul_Spec, ha, M.map_smul_Spec, pow_add, mul_smul, smul_comm, ht i]
    · intro i j
      have : Function.Injective (M.presheaf.map (eqToHom (basicOpen_mul (g i) (g j))).op) :=
        ConcreteCategory.injective_of_mono_of_preservesPullback _
      change M.presheaf.map (Opens.infLELeft (basicOpen (g i)) (basicOpen (g j))).op _ =
        M.presheaf.map (Opens.infLERight (basicOpen (g i)) (basicOpen (g j))).op _
      apply this
      dsimp [Opens.infLELeft, Opens.infLERight]
      simp_rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
      exact hK i j
  · have (i : I) : ∃ (n : ℕ), M.presheaf.map (homOfLE (hgle i)).op (f ^ n • t) = 0 := by
      have := QuasicoherentTilde.Aux.uniqueness (h₁ i) (f * g i) (basicOpen_mul_le_right f (g i))
        (M.presheaf.map (homOfLE (hgle i)).op t) ?_
      · obtain ⟨n, hn⟩ := this
        use n
        rw [mul_pow, mul_comm, mul_smul, ← Scheme.Modules.map_smul_Spec] at hn
        exact ((M.isSMulRegular_of_le_basicOpen le_rfl).pow n).right_eq_zero_of_smul hn
      · rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp ((basicOpen_mul_le_left f (g i))) hf, op_comp, M.presheaf.map_comp_apply]
        have hv : M.presheaf.map (homOfLE hf).op t = (0 : Γ(M, basicOpen f)) := hs
        rw [hv, map_zero]
    choose n hn using this
    use ⨆ i, n i
    refine openPushforward_section_ext j H (fun i ↦ basicOpen (g i)) ⊤ hgle hc _ _ ?_
    intro i
    have : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
    have : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by lia
    change M.presheaf.map (homOfLE (hgle i)).op (f ^ _ • t) =
      M.presheaf.map (homOfLE (hgle i)).op (0 : Γ(M, ⊤))
    rw [this, pow_add, mul_smul, Scheme.Modules.map_smul_Spec, hn i, smul_zero, map_zero]

/-- Quasi-compact open direct image into an affine scheme preserves
quasi-coherence. -/
theorem openPushforward_isQuasicoherent_spec [IsOpenImmersion j] [H.IsQuasicoherent]
    (hj : IsCompact (Set.range j)) : ((Scheme.Modules.pushforward j).obj H).IsQuasicoherent := by
  let M := (Scheme.Modules.pushforward j).obj H
  obtain ⟨I, hι, g, hg⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact j.opensRange hj
  apply (isQuasicoherent_iff_isIso_fromTildeΓ M).mpr
  apply (isIso_fromTildeΓ_iff_isLocalizing M).mpr
  exact (QuasicoherentTilde.isLocalizing_iff_aux M).mpr (aux_of_principal_cover j H g hg)

end AffineOpenDirectImage

set_option backward.isDefEq.respectTransparency false in
/-- Restrict a sheaf direct image to an open by first restricting the sheaf
to the inverse image open and then taking the restricted direct image. -/
def restrictPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.pushforward f ⋙ restrictFunctor U.ι ≅
      restrictFunctor (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward (f ∣_ U) := by
  let V := f ⁻¹ᵁ U
  let F := U.ι.opensFunctor ⋙ (Opens.map f.base)
  let G := Opens.map (f ∣_ U).base ⋙ V.ι.opensFunctor
  let e : F ≅ G := NatIso.ofComponents
    (fun W => eqToIso (image_morphismRestrict_preimage f U W).symm)
    (fun _ => Subsingleton.elim _ _)
  let α : U.toScheme.presheaf ⟶ U.ι.opensFunctor.op ⋙ Y.presheaf :=
    { app W := (U.ι.appIso W.unop).inv }
  let β : V.toScheme.presheaf ⟶ V.ι.opensFunctor.op ⋙ X.presheaf :=
    { app W := (V.ι.appIso W.unop).inv }
  let φ : U.toScheme.ringCatSheaf ⟶
      (U.ι.opensFunctor.sheafPushforwardContinuous _ _ _).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  let ψ : V.toScheme.ringCatSheaf ⟶
      (V.ι.opensFunctor.sheafPushforwardContinuous _ _ _).obj X.ringCatSheaf :=
    ⟨Functor.whiskerRight β (forget₂ CommRingCat RingCat)⟩
  refine SheafOfModules.pushforwardComp φ f.toRingCatSheafHom ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp (f ∣_ U).toRingCatSheafHom ψ).symm
  refine SheafOfModules.pushforwardCongr₂ _ e.symm ?_
  ext W x
  change X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op
      (f.app (U.ι ''ᵁ W.unop) ((U.ι.appIso W.unop).inv x)) =
    (V.ι.appIso ((f ∣_ U) ⁻¹ᵁ W.unop)).inv ((f ∣_ U).app W.unop x)
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  rw [morphismRestrict_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Direct image along an isomorphism agrees with restriction along its inverse. -/
def pushforwardIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Scheme.Modules.pushforward f ≅ restrictFunctor (inv f) := by
  let P := Scheme.Modules.pushforward f
  let Q := Scheme.Modules.pushforward (inv f)
  let R := restrictFunctor (inv f)
  exact (Functor.rightUnitor P).symm ≪≫
    Functor.isoWhiskerLeft P (restrictFunctorAdjCounitIso (inv f)).symm ≪≫
    (Functor.associator P Q R).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pushforwardComp f (inv f) ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id f) ≪≫
      Scheme.Modules.pushforwardId X) R ≪≫ Functor.leftUnitor R

set_option backward.isDefEq.respectTransparency false in
private theorem pushforward_isQuasicoherent_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((pushforwardIsoRestrict f).app M).symm
    (Scheme.Modules.isQuasicoherent_restrictFunctor (inv f) M)

set_option backward.isDefEq.respectTransparency false in
private theorem openPushforward_isQuasicoherent_affine {X Y : Scheme.{u}} [IsAffine X]
    [IsLocallyNoetherian X] (j : Y ⟶ X) [IsOpenImmersion j] (H : Y.Modules)
    [H.IsQuasicoherent] : ((Scheme.Modules.pushforward j).obj H).IsQuasicoherent := by
  let e := X.isoSpec
  let f := j ≫ e.hom
  let R := CommRingCat.of Γ(X, ⊤)
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian
    ⟨⊤, isAffineOpen_top X⟩
  let A := (Scheme.Modules.pushforward f).obj H
  let : A.IsQuasicoherent :=
    openPushforward_isQuasicoherent_spec f H (NoetherianSpace.isCompact _)
  let e' : (Scheme.Modules.pushforward e.inv).obj A ≅ (Scheme.Modules.pushforward j).obj H :=
    (Scheme.Modules.pushforwardComp f e.inv).app H ≪≫
      (Scheme.Modules.pushforwardCongr (by simp [f, e])).app H
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e'
    (pushforward_isQuasicoherent_of_isIso e.inv A)

set_option backward.isDefEq.respectTransparency false in
private theorem affine_has_presentation {X : Scheme.{u}} [IsAffine X] (H : X.Modules)
    [H.IsQuasicoherent] : Nonempty H.Presentation := by
  let e := X.isoSpec
  let A := H.restrict e.inv
  let R := CommRingCat.of Γ(X, ⊤)
  let M := (moduleSpecΓFunctor (R := R)).obj A
  let l := Finsupp.linearCombination R (fun x : (Set.univ : Set M) => x.val)
  let B := presentationTilde M Set.univ (by simp) (LinearMap.ker l : Set _) (Submodule.span_eq _)
  let : A.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor e.inv H
  let : IsIso (Scheme.Modules.fromTildeΓ (R := R) A) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ (R := R) A).mp ‹_›
  let P := B.ofIsIso (Scheme.Modules.fromTildeΓ (R := R) A)
  let d : (A.restrict e.hom) ≅ H :=
    ((restrictFunctorComp e.hom e.inv).app H).symm ≪≫
      (restrictFunctorCongr e.hom_inv_id).app H ≪≫ restrictFunctorId.app H
  exact ⟨(presentationRestrict e.hom P).ofIsIso d.hom⟩

set_option backward.isDefEq.respectTransparency false in
private theorem quasicoherent_of_affineRestrictions {X : Scheme.{u}} (N : X.Modules)
    (h : ∀ U : X.affineOpens, (N.restrict U.val.ι).IsQuasicoherent) : N.IsQuasicoherent := by
  have hp (U : X.affineOpens) : Nonempty (N.over U.val).Presentation := by
    let : IsAffine U.val.toScheme := U.property
    let : (N.restrict U.val.ι).IsQuasicoherent := h U
    obtain ⟨P⟩ := affine_has_presentation (N.restrict U.val.ι)
    let E := overEquiv U.val
    let d : E.inverse.obj (N.restrict U.val.ι) ≅ N.over U.val :=
      E.inverse.mapIso ((overFunctorEquiv U.val).app N).symm ≪≫ (E.unitIso.app _).symm
    exact ⟨(P.map E.inverse (U.val.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofIsIso d.hom⟩
  let d : N.QuasicoherentData :=
    { I := X.affineOpens
      X := Subtype.val
      coversTop := (Opens.coversTop_iff _ _).mpr (iSup_affineOpens_eq_top X)
      presentation := fun U => (hp U).some }
  exact d.isQuasicoherent

set_option backward.isDefEq.respectTransparency false in
/-- Direct image under an open immersion into a locally Noetherian scheme
preserves quasi-coherence. -/
theorem openPushforward_isQuasicoherent {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (j : Y ⟶ X) [IsOpenImmersion j] (H : Y.Modules) [H.IsQuasicoherent] :
    ((Scheme.Modules.pushforward j).obj H).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward j).obj H
  apply quasicoherent_of_affineRestrictions N
  intro U
  let V := j ⁻¹ᵁ U.val
  let : IsAffine U.val.toScheme := U.property
  let : IsLocallyNoetherian U.val.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.val.ι
  exact (SheafOfModules.isQuasicoherent U.val.toScheme.ringCatSheaf).prop_of_iso
    ((restrictPushforwardIso j U.val).app H).symm
    (openPushforward_isQuasicoherent_affine (j ∣_ U.val) (H.restrict V.ι))

end QuasicoherentDirectImage

section GradedSubmodules

open scoped DirectSum

variable {k Λ A V : Type u} [Field k] [CommGroup Λ] [CommRing A] [Algebra k A]
  [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V]

section GradedSpan

variable (G : RingGrading k Λ A) (H : ModuleGrading G V)

private theorem homogeneous_span_components (S : Set V) (hS : ∀ s ∈ S, ∃ i, s ∈ H.piece i) :
    letI := Classical.decEq Λ
    letI := H.internal.chooseDecomposition
    ∀ v ∈ Submodule.span A S, ∀ i, (DirectSum.decompose H.piece v i : V) ∈ Submodule.span A S := by
  classical
  let := H.internal.chooseDecomposition
  let := G.internal.chooseDecomposition
  intro v hv i
  rw [Finsupp.span_eq_range_linearCombination] at hv
  obtain ⟨c, rfl⟩ := hv
  rw [Finsupp.linearCombination_apply, Finsupp.sum, DirectSum.decompose_sum,
    DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Submodule.sum_mem _ fun w _ => ?_
  obtain ⟨j, hj⟩ := hS w.val w.property
  rw [← DirectSum.sum_support_decompose G.piece (c w), Finset.sum_smul,
    DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Submodule.sum_mem _ fun l _ => ?_
  have h : (DirectSum.decompose G.piece (c w) l : A) • w.val ∈ H.piece (l * j) :=
    H.smul_mem (DirectSum.decompose G.piece (c w) l).property hj
  by_cases hi : l * j = i
  · rw [DirectSum.decompose_of_mem_same _ (hi ▸ h)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span w.property)
  · rw [DirectSum.decompose_of_mem_ne _ h hi]
    exact Submodule.zero_mem _

/-- A submodule closed under homogeneous components inherits the grading of
the ambient module. -/
private def submoduleGrading (P : Submodule A V)
    (hP : letI := Classical.decEq Λ
          letI := H.internal.chooseDecomposition
          ∀ v ∈ P, ∀ i, (DirectSum.decompose H.piece v i : V) ∈ P) :
    ModuleGrading G P := by
  classical
  letI := H.internal.chooseDecomposition
  let inc := P.subtype.restrictScalars k
  let C (i : Λ) : Submodule k P := (H.piece i).comap inc
  refine { piece := C, internal := ?_, smul_mem := fun hr hv => H.smul_mem hr hv }
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · intro i
    rw [Submodule.disjoint_def]
    intro x hxi hx
    apply Subtype.val_injective
    apply Submodule.disjoint_def.mp (H.internal.submodule_iSupIndep i) x.val hxi
    have hmap : (⨆ j, ⨆ (_ : j ≠ i), C j).map inc ≤ ⨆ j, ⨆ (_ : j ≠ i), H.piece j := by
      simp only [Submodule.map_iSup, iSup_le_iff]
      intro j h v hv
      rcases hv with ⟨w, hw, rfl⟩
      exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem h hw)
    exact hmap (Submodule.mem_map_of_mem hx)
  · apply top_unique
    intro v _
    let d := DirectSum.decompose H.piece (v : V)
    let p (i : Λ) : P := ⟨(d i : V), hP v v.property i⟩
    have he : ∑ i ∈ d.support, p i = v := by
      apply Subtype.val_injective
      change (P.subtype (∑ i ∈ d.support, p i)) = v.val
      rw [map_sum]
      exact DirectSum.sum_support_decompose H.piece v.val
    rw [← he]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (d i).property

set_option backward.isDefEq.respectTransparency false in
/-- Finitely many elements of a graded module lie in a finite graded
submodule, obtained by spanning their homogeneous components. -/
theorem exists_finite_graded_submodule (S : Finset V) :
    ∃ (P : Submodule A V) (J : ModuleGrading G P),
      Module.Finite A P ∧ (∀ s ∈ S, s ∈ P) ∧
      ∀ i (v : P), v ∈ J.piece i ↔ v.val ∈ H.piece i := by
  classical
  let := H.internal.chooseDecomposition
  let d := DirectSum.decompose H.piece
  let B := S.biUnion (fun v => (d v).support.image (fun i => (d v i : V)))
  let P := Submodule.span A (B : Set V)
  have hB : ∀ v ∈ (B : Set V), ∃ i, v ∈ H.piece i := by
    intro v hv
    obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨i, (d s i).property⟩
  let J := submoduleGrading G H P (homogeneous_span_components G H _ hB)
  refine ⟨P, J, Module.Finite.of_fg ⟨B, rfl⟩, ?_, fun _ _ => Iff.rfl⟩
  intro s hs
  rw [← DirectSum.sum_support_decompose H.piece s]
  exact Submodule.sum_mem _ fun i hi => Submodule.subset_span
    (Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)

end GradedSpan

end GradedSubmodules

section CoherentKernels

open PrimeSpectrum
open LinearAlgebraicGroups.ProjectiveFiniteness (finite_sections_of_isAffineOpen)

set_option backward.isDefEq.respectTransparency false in
private theorem section_kernel_exact {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) :
    Function.Injective ((kernel.ι f).val.app (op U)) ∧
      Function.Exact ((kernel.ι f).val.app (op U)) (f.val.app (op U)) := by
  let E := SheafOfModules.evaluation (R := X.ringCatSheaf) (op U)
  let : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let : PreservesFiniteLimits E := SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)
  let K := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  let h := KernelFork.mapIsLimit (KernelFork.ofι (kernel.ι f) (kernel.condition f)) (kernelIsKernel f) E
  let S := K.map E
  let hMono : Mono S.f := inferInstanceAs (Mono (E.map (kernel.ι f)))
  exact ⟨(ModuleCat.mono_iff_injective S.f).mp hMono,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp (S.exact_of_f_is_kernel h)⟩

private theorem section_kernel_exact_over_spec {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (f : M ⟶ N) (U : (Spec R).Opens) :
    Function.Injective ((modulesSpecToSheaf.map (kernel.ι f)).hom.app (op U)) ∧
      Function.Exact ((modulesSpecToSheaf.map (kernel.ι f)).hom.app (op U))
        ((modulesSpecToSheaf.map f).hom.app (op U)) :=
  section_kernel_exact f U

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_isLocalizing {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (f : M ⟶ N) (hM : IsLocalizing (modulesSpecToSheaf.obj M))
    (hN : IsLocalizing (modulesSpecToSheaf.obj N)) :
    IsLocalizing (modulesSpecToSheaf.obj (kernel f)) := by
  intro r
  let V := basicOpen r
  let S := modulesSpecToSheaf (R := R)
  let res (P : (Spec R).Modules) := ((S.obj P).obj.map V.leTop.op)
  let opTop : (Spec R).Opensᵒᵖ := op ⊤
  let j₀ := (S.map (kernel.ι f)).hom.app opTop
  let j₁ := (S.map (kernel.ι f)).hom.app (op V)
  let f₀ := (S.map f).hom.app opTop
  let f₁ := (S.map f).hom.app (op V)
  have hnatJ : ∀ y, j₁ (res (kernel f) y) = res M (j₀ y) := fun y =>
    congr($( (S.map (kernel.ι f)).hom.naturality V.leTop.op) y)
  have hnatF : ∀ y, f₁ (res M y) = res N (f₀ y) := fun y =>
    congr($( (S.map f).hom.naturality V.leTop.op) y)
  obtain ⟨h₀, e₀⟩ := section_kernel_exact_over_spec f ⊤
  obtain ⟨h₁, e₁⟩ := section_kernel_exact_over_spec f V
  change Function.Injective j₀ at h₀
  change Function.Injective j₁ at h₁
  change Function.Exact j₀ f₀ at e₀
  change Function.Exact j₁ f₁ at e₁
  have lM : IsLocalizedModule.Away r (res M).hom := hM r
  have lN : IsLocalizedModule.Away r (res N).hom := hN r
  change IsLocalizedModule.Away r (res (kernel f)).hom
  apply IsLocalizedModule.Away.mk_of_addCommGroup
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := kernel f) r le_rfl
  · intro x
    obtain ⟨⟨y, _, n, rfl⟩, hy⟩ := IsLocalizedModule.surj (.powers r) (res M).hom (j₁ x)
    change r ^ n • j₁ x = res M y at hy
    have hf₀ : res N (f₀ y) = 0 := by
      rw [← hnatF, ← hy, f₁.hom.map_smul, e₁.apply_apply_eq_zero, smul_zero]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalizedModule.eq_zero_iff (.powers r) (res N).hom).mp hf₀
    have hm₀ : f₀ ((r ^ m) • y) = 0 := by
      change f₀.hom ((r ^ m) • y) = 0
      rw [f₀.hom.map_smul]
      exact hm
    obtain ⟨z, hz⟩ := (e₀ _).mp hm₀
    refine ⟨m + n, z, ?_⟩
    symm
    change res (kernel f) z = r ^ (m + n) • x
    apply h₁
    rw [hnatJ, hz]
    change (res M).hom (r ^ m • y) = j₁.hom (r ^ (m + n) • x)
    rw [(res M).hom.map_smul, j₁.hom.map_smul, ← hy, pow_add, mul_smul]
  · intro x hx
    have hx₀ : res M (j₀ x) = 0 := by rw [← hnatJ, show res (kernel f) x = 0 from hx, map_zero]
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers r) (res M).hom).mp hx₀
    refine ⟨n, h₀ ?_⟩
    change j₀.hom (r ^ n • x) = j₀.hom 0
    rw [j₀.hom.map_smul, map_zero]
    exact hn

private theorem kernel_spec_quasicoherent {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) : (kernel f).IsQuasicoherent := by
  apply (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr
  apply (isIso_fromTildeΓ_iff_isLocalizing _).mpr
  exact kernel_isLocalizing f ((isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance)
    ((isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance)

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_restrict_quasicoherent {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) (U : X.affineOpens) :
    ((kernel f).restrict U.val.ι).IsQuasicoherent := by
  let G := restrictFunctor U.property.fromSpec
  let E := restrictFunctor U.property.isoSpec.hom
  let h := PreservesKernel.iso G f
  let : (G.obj (kernel f)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, U.val)).ringCatSheaf).prop_of_iso h.symm
      (kernel_spec_quasicoherent (G.map f))
  let e : E.obj (G.obj (kernel f)) ≅ (kernel f).restrict U.val.ι :=
    ((restrictFunctorComp U.property.isoSpec.hom U.property.fromSpec).app (kernel f)).symm ≪≫
      (restrictFunctorCongr U.property.isoSpec_hom_fromSpec).app (kernel f)
  exact (SheafOfModules.isQuasicoherent U.val.toScheme.ringCatSheaf).prop_of_iso e
    (Scheme.Modules.isQuasicoherent_restrictFunctor U.property.isoSpec.hom (G.obj (kernel f)))

/-- Kernels of maps of quasi-coherent module sheaves are quasi-coherent. -/
theorem kernel_isQuasicoherent {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) : (kernel f).IsQuasicoherent :=
  quasicoherent_of_affineRestrictions _ (kernel_restrict_quasicoherent f)

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-coherent submodule of a coherent sheaf over a locally Noetherian
scheme is coherent. In particular, this applies to the kernel of a map to an
arbitrary quasi-coherent module. -/
theorem finitePresentation_of_mono {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsFinitePresentation] (f : M ⟶ N) [Mono f] :
    M.IsFinitePresentation := by
  apply finitePresentation_of_affineSections M
  intro U
  refine ⟨inferInstance, ?_⟩
  let R := Γ(X, U.val)
  let P := SheafOfModules.evaluation (R := X.ringCatSheaf) (op U.val)
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  let : Module.Finite R Γ(N, U.val) := finite_sections_of_isAffineOpen N U.property
  have h : Function.Injective (P.map f) := (ModuleCat.mono_iff_injective _).mp inferInstance
  let t : Γ(M, U.val) →ₗ[R] Γ(N, U.val) := (P.map f).hom
  exact Module.Finite.of_injective t h

end CoherentKernels

section QuasicoherentOperations

private theorem cokernel_spec_quasicoherent {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) : (cokernel f).IsQuasicoherent := by
  let G := moduleSpecΓFunctor (R := R)
  let P := tilde.functor R
  let hM : IsIso (Scheme.Modules.fromTildeΓ (R := R) M) := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp inferInstance
  let hN : IsIso (Scheme.Modules.fromTildeΓ (R := R) N) := (isQuasicoherent_iff_isIso_fromTildeΓ N).mp inferInstance
  have he : P.map (G.map f) ≫ N.fromTildeΓ = M.fromTildeΓ ≫ f := fromTildeΓNatTrans.naturality f
  let e : tilde (cokernel (G.map f)) ≅ cokernel f :=
    PreservesCokernel.iso P (G.map f) ≪≫ cokernel.mapIso _ _ (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := R) M) hM) (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := R) N) hN) he
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem quasicoherent_restrict_of_fromSpec {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens) [(M.restrict U.property.fromSpec).IsQuasicoherent] :
    (M.restrict U.val.ι).IsQuasicoherent := by
  let V := U.property.isoSpec.hom
  let e : (M.restrict U.property.fromSpec).restrict V ≅ M.restrict U.val.ι :=
    ((restrictFunctorComp V U.property.fromSpec).app M).symm ≪≫
      (restrictFunctorCongr U.property.isoSpec_hom_fromSpec).app M
  exact (SheafOfModules.isQuasicoherent U.val.toScheme.ringCatSheaf).prop_of_iso e inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The binary direct sum of quasi-coherent modules is quasi-coherent. -/

theorem cokernel_isQuasicoherent {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) : (cokernel f).IsQuasicoherent := by
  apply quasicoherent_of_affineRestrictions
  intro U
  let P := restrictFunctor U.property.fromSpec
  let e := PreservesCokernel.iso P f
  let : (P.obj (cokernel f)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, U.val)).ringCatSheaf).prop_of_iso e.symm
      (cokernel_spec_quasicoherent (P.map f))
  exact quasicoherent_restrict_of_fromSpec (cokernel f) U

end QuasicoherentOperations

section LinearizedCokernel

variable {k : Type u} [Field k] {T : GroupScheme k} {X : SchemeOver k}
  {a : ModObj T.X X} {F G : X.left.Modules}

open private pullCongr_naturality from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

private abbrev projectionPull (T : GroupScheme k) (X : SchemeOver k) :=
  Scheme.Modules.pullback (snd T.X X).left

private abbrev actionPull (a : ModObj T.X X) := Scheme.Modules.pullback a.smul.left

private abbrev PullMap {S : SchemeOver k} (x : S ⟶ X) (f : F ⟶ G) :=
  (Scheme.Modules.pullback x.left).map f

private abbrev TransportHom {S : SchemeOver k} {H : X.left.Modules}
    (L : Pull (snd T.X X) H ≅ Pull a.smul H) (t : S ⟶ T.X) (x : S ⟶ X) :=
  (transport a L t x).hom

private theorem transportSquare {S : SchemeOver k}
    {L : Pull (snd T.X X) F ≅ Pull a.smul F} {K : Pull (snd T.X X) G ≅ Pull a.smul G}
    {f : F ⟶ G} (hf : CommSq L.hom ((projectionPull T X).map f) ((actionPull a).map f) K.hom)
    (t : S ⟶ T.X) (x : S ⟶ X) :
    CommSq (TransportHom L t x) (PullMap x f) (PullMap (actOn a t x) f) (TransportHom K t x) :=
  ⟨transport_map L K f hf.w t x⟩

private theorem pullCongrSquare {S : SchemeOver k} {x y : S ⟶ X} (h : x = y) (f : F ⟶ G) :
    CommSq (pullCongr F h).hom (PullMap x f) (PullMap y f) (pullCongr G h).hom :=
  ⟨pullCongr_naturality h f⟩

private theorem cancelUnitEpi {C : Type*} [Category C] {A B D E : C}
    {f : A ⟶ B} {g : D ⟶ E} {p : A ⟶ D} {q : B ⟶ E} {r : B ⟶ A} {s : E ⟶ D}
    [Epi p] (h : CommSq f p q g) (h' : CommSq r q p s) (hu : f ≫ r = 𝟙 _) :
    g ≫ s = 𝟙 _ := by
  have H := (h.horiz_comp h').w
  rw [hu, Category.id_comp] at H
  exact (cancel_epi p).mp (by rw [← H, Category.comp_id])

private theorem cancelCompositionEpi {C : Type*} [Category C]
    {A B D E A' B' D' E' : C} {p : A ⟶ A'} {q : B ⟶ B'} {r : D ⟶ D'} {s : E ⟶ E'}
    {f : A ⟶ B} {g : B ⟶ D} {h : D ⟶ E} {i : A ⟶ E}
    {f' : A' ⟶ B'} {g' : B' ⟶ D'} {h' : D' ⟶ E'} {i' : A' ⟶ E'} [Epi p]
    (hf : CommSq f p q f') (hg : CommSq g q r g') (hh : CommSq h r s h')
    (hi : CommSq i p s i') (hc : ComposesTo f g h i) : ComposesTo f' g' h' i' := by
  have H := (hf.horiz_comp (hg.horiz_comp hh)).w
  change f ≫ g ≫ h = i at hc
  rw [hc, hi.w] at H
  exact (cancel_epi p).mp H.symm

private theorem unitOfEpi (L : Linearization a F) (K : Pull (snd T.X X) G ≅ Pull a.smul G)
    (f : F ⟶ G) [Epi f]
    (hf : CommSq L.iso.hom ((projectionPull T X).map f) ((actionPull a).map f) K.hom)
    (S : SchemeOver k) (x : S ⟶ X) :
    ∃ h : actOn a (1 : S ⟶ T.X) x = x,
      (TransportHom K 1 x) ≫ (pullCongr G h).hom = 𝟙 _ := by
  obtain ⟨h, hu⟩ := L.unit S x
  exact ⟨h, cancelUnitEpi (transportSquare hf 1 x) (pullCongrSquare h f) hu⟩

set_option maxHeartbeats 700000 in
private theorem mulOfEpi (L : Linearization a F) (K : Pull (snd T.X X) G ≅ Pull a.smul G)
    (f : F ⟶ G) [Epi f]
    (hf : CommSq L.iso.hom ((projectionPull T X).map f) ((actionPull a).map f) K.hom)
    (S : SchemeOver k) (s t : S ⟶ T.X) (x : S ⟶ X) :
    ∃ h : actOn a s (actOn a t x) = actOn a (s * t) x, TransportComposition K s t x h := by
  obtain ⟨h, hm⟩ := L.mul S s t x
  have H₁ := transportSquare hf t x
  have H₂ := transportSquare hf s (actOn a t x)
  have H₃ := pullCongrSquare h f
  have H₄ := transportSquare hf (s * t) x
  change ComposesTo (TransportHom L.iso t x) (TransportHom L.iso s (actOn a t x))
    (pullCongr F h).hom (TransportHom L.iso (s * t) x) at hm
  refine ⟨h, ?_⟩
  change ComposesTo (TransportHom K t x) (TransportHom K s (actOn a t x))
    (pullCongr G h).hom (TransportHom K (s * t) x)
  exact cancelCompositionEpi H₁ H₂ H₃ H₄ hm

private def linearizationOfEpi (L : Linearization a F)
    (K : Pull (snd T.X X) G ≅ Pull a.smul G) (f : F ⟶ G) [Epi f]
    (hf : CommSq L.iso.hom ((projectionPull T X).map f) ((actionPull a).map f) K.hom) :
    Linearization a G where
  iso := K
  unit := unitOfEpi L K f hf
  mul := mulOfEpi L K f hf

private def cokernelLinearizationIso (L : Linearization a F) (K : Linearization a G) (f : F ⟶ G)
    (hf : IsLinearizedMap L K f) : Pull (snd T.X X) (cokernel f) ≅ Pull a.smul (cokernel f) :=
  let P := projectionPull T X
  let A := actionPull a
  PreservesCokernel.iso P f ≪≫ cokernel.mapIso (P.map f) (A.map f) L.iso K.iso hf.symm ≪≫
    (PreservesCokernel.iso A f).symm

private theorem cokernelLinearizationSquare (L : Linearization a F) (K : Linearization a G)
    (f : F ⟶ G) (hf : IsLinearizedMap L K f) :
    CommSq K.iso.hom ((projectionPull T X).map (cokernel.π f))
      ((actionPull a).map (cokernel.π f)) (cokernelLinearizationIso L K f hf).hom := by
  constructor
  let P := projectionPull T X
  let A := actionPull a
  let e := cokernel.mapIso (P.map f) (A.map f) L.iso K.iso hf.symm
  have he : cokernel.π (P.map f) ≫ e.hom = K.iso.hom ≫ cokernel.π (A.map f) :=
    cokernel.π_desc _ _ _
  change K.iso.hom ≫ A.map (cokernel.π f) =
    P.map (cokernel.π f) ≫ (PreservesCokernel.iso P f).hom ≫ e.hom ≫
      (PreservesCokernel.iso A f).inv
  have hA := (Iso.eq_comp_inv _).mpr (PreservesCokernel.π_iso_hom A f)
  rw [PreservesCokernel.π_iso_hom_assoc, reassoc_of% he, ← hA]

/-- Cokernels of linearized morphisms carry the induced quotient linearization. -/
theorem cokernelLinearization (L : Linearization a F) (K : Linearization a G) (f : F ⟶ G)
    (hf : IsLinearizedMap L K f) :
    ∃ J : Linearization a (cokernel f), IsLinearizedMap K J (cokernel.π f) :=
  let h := cokernelLinearizationSquare L K f hf
  ⟨linearizationOfEpi K (cokernelLinearizationIso L K f hf) (cokernel.π f) h, h.w⟩

end LinearizedCokernel

section TransportLaws

variable {k : Type u} [Field k] {T : GroupScheme k} {X S W : SchemeOver k}
  {a : ModObj T.X X} {F : X.left.Modules}

open private comparePull evalPullIso pullback_map_evalPullIso_to transport_eq_evalPullIso
  pullCongr_refl pullCongr_trans from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

private theorem cancelUnitMono {C : Type*} [Category C] {A B D E : C}
    {f : A ⟶ B} {g : D ⟶ E} {p : A ⟶ D} {q : B ⟶ E} {r : B ⟶ A} {s : E ⟶ D}
    [Mono p] (h : CommSq f p q g) (h' : CommSq r q p s) (hu : g ≫ s = 𝟙 _) :
    f ≫ r = 𝟙 _ := by
  have H := (h.horiz_comp h').w
  rw [hu, Category.comp_id] at H
  exact (cancel_mono p).mp (by rw [H, Category.id_comp])

private theorem cancelCompositionMono {C : Type*} [Category C]
    {A B D E A' B' D' E' : C} {p : A ⟶ A'} {q : B ⟶ B'} {r : D ⟶ D'} {s : E ⟶ E'}
    {f : A ⟶ B} {g : B ⟶ D} {h : D ⟶ E} {i : A ⟶ E}
    {f' : A' ⟶ B'} {g' : B' ⟶ D'} {h' : D' ⟶ E'} {i' : A' ⟶ E'} [Mono s]
    (hf : CommSq f p q f') (hg : CommSq g q r g') (hh : CommSq h r s h')
    (hi : CommSq i p s i') (hc : ComposesTo f' g' h' i') : ComposesTo f g h i := by
  have H := (hf.horiz_comp (hg.horiz_comp hh)).w
  change f' ≫ g' ≫ h' = i' at hc
  rw [hc, ← hi.w] at H
  exact (cancel_mono s).mp H

private theorem actOn_comp (r : W ⟶ S) (t : S ⟶ T.X) (x : S ⟶ X)
    {t' : W ⟶ T.X} {x' : W ⟶ X} (ht : r ≫ t = t') (hx : r ≫ x = x') :
    r ≫ actOn a t x = actOn a t' x' := by
  subst t' x'
  simp [actOn, ← Category.assoc]

private theorem transportReindexSquare
    (L : Pull (snd T.X X) F ≅ Pull a.smul F)
    (r : W ⟶ S) (t : S ⟶ T.X) (x : S ⟶ X)
    {t' : W ⟶ T.X} {x' : W ⟶ X} (ht : r ≫ t = t') (hx : r ≫ x = x') :
    CommSq ((Scheme.Modules.pullback r.left).map (TransportHom L t x))
      (comparePull F r x hx).hom (comparePull F r (actOn a t x) (actOn_comp (a := a) r t x ht hx)).hom
      (TransportHom L t' x') := by
  constructor
  change (Scheme.Modules.pullback r.left).map (transport a L t x).hom ≫ _ =
    _ ≫ (transport a L t' x').hom
  rw [transport_eq_evalPullIso, transport_eq_evalPullIso]
  exact pullback_map_evalPullIso_to L (lift t x) (lift_snd t x) rfl r
    (show r ≫ lift t x = lift t' x' by simp [← ht, ← hx]) hx
    (actOn_comp (a := a) r t x ht hx) (lift_snd t' x') rfl

private theorem pullCongrReindexSquare (r : W ⟶ S) {x y : S ⟶ X} {x' y' : W ⟶ X}
    (h : x = y) (h' : x' = y') (hx : r ≫ x = x') (hy : r ≫ y = y') :
    CommSq ((Scheme.Modules.pullback r.left).map (pullCongr F h).hom)
      (comparePull F r x hx).hom (comparePull F r y hy).hom (pullCongr F h').hom := by
  subst y y'
  refine ⟨?_⟩
  change (Scheme.Modules.pullback r.left).map (pullCongr F (rfl : x = x)).hom ≫
    (comparePull F r x hy).hom = (comparePull F r x hx).hom ≫ (pullCongr F (rfl : x' = x')).hom
  simp only [pullCongr_refl, (Scheme.Modules.pullback r.left).map_id, Category.id_comp, Category.comp_id]

private theorem unitAt_of_unitAt (L : Pull (snd T.X X) F ≅ Pull a.smul F)
    (r : W ⟶ S) (x : S ⟶ X) (h : actOn a (1 : S ⟶ T.X) x = x)
    (hu : TransportHom L 1 x ≫ (pullCongr F h).hom = 𝟙 _)
    {x' : W ⟶ X} (hx : r ≫ x = x') :
    ∃ h' : actOn a (1 : W ⟶ T.X) x' = x',
      TransportHom L 1 x' ≫ (pullCongr F h').hom = 𝟙 _ := by
  let := a
  let h' : actOn a (1 : W ⟶ T.X) x' = x' := one_smul (W ⟶ T.X) x'
  have sq₁ := transportReindexSquare L r 1 x (MonObj.comp_one r) hx
  have sq₂ := pullCongrReindexSquare (F := F) r h h' (actOn_comp r 1 x (MonObj.comp_one r) hx) hx
  have hs := (sq₁.horiz_comp sq₂).w
  rw [← (Scheme.Modules.pullback r.left).map_comp, hu,
    (Scheme.Modules.pullback r.left).map_id, Category.id_comp] at hs
  exact ⟨h', (cancel_epi (comparePull F r x hx).hom).mp (by rw [← hs, Category.comp_id])⟩

private theorem mapComposesTo {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {A B E J : C} {f : A ⟶ B} {g : B ⟶ E} {h : E ⟶ J} {i : A ⟶ J}
    (hc : ComposesTo f g h i) : ComposesTo (P.map f) (P.map g) (P.map h) (P.map i) := by
  unfold ComposesTo at *
  rw [← P.map_comp, ← P.map_comp, hc]

set_option maxHeartbeats 550000 in
private theorem mulAt_of_mulAt (L : Pull (snd T.X X) F ≅ Pull a.smul F)
    (r : W ⟶ S) (s t : S ⟶ T.X) (x : S ⟶ X)
    (h : actOn a s (actOn a t x) = actOn a (s * t) x)
    (hm : TransportComposition L s t x h)
    {s' t' : W ⟶ T.X} {x' : W ⟶ X} (hs : r ≫ s = s') (ht : r ≫ t = t') (hx : r ≫ x = x') :
    ∃ h' : actOn a s' (actOn a t' x') = actOn a (s' * t') x',
      TransportComposition L s' t' x' h' := by
  let := a
  let h' : actOn a s' (actOn a t' x') = actOn a (s' * t') x' := (mul_smul s' t' x').symm
  have hp : r ≫ (s * t) = s' * t' := (MonObj.comp_mul r s t).trans (by rw [hs, ht])
  have H₁ := transportReindexSquare L r t x ht hx
  have H₂ := transportReindexSquare L r s (actOn a t x) hs (actOn_comp r t x ht hx)
  have H₄ := transportReindexSquare L r (s * t) x hp hx
  have H₃ := pullCongrReindexSquare (F := F) r h h' (actOn_comp r s (actOn a t x) hs
    (actOn_comp r t x ht hx)) (actOn_comp r (s * t) x hp hx)
  change ComposesTo (TransportHom L t x) (TransportHom L s (actOn a t x))
    (pullCongr F h).hom (TransportHom L (s * t) x) at hm
  have H := mapComposesTo (Scheme.Modules.pullback r.left) hm
  refine ⟨h', ?_⟩
  change ComposesTo (TransportHom L t' x') (TransportHom L s' (actOn a t' x'))
    (pullCongr F h').hom (TransportHom L (s' * t') x')
  have sq := (H₁.horiz_comp (H₂.horiz_comp H₃)).w
  unfold ComposesTo at H ⊢
  rw [H, H₄.w] at sq
  exact (cancel_epi (comparePull F r x hx).hom).mp sq.symm

private abbrev triple (T : GroupScheme k) (X : SchemeOver k) := T.X ⊗ (T.X ⊗ X)

private abbrev tripleFirst (T : GroupScheme k) (X : SchemeOver k) : triple T X ⟶ T.X :=
  fst T.X (T.X ⊗ X)

private abbrev tripleSecond (T : GroupScheme k) (X : SchemeOver k) : triple T X ⟶ T.X :=
  snd T.X (T.X ⊗ X) ≫ fst T.X X

private abbrev tripleBase (T : GroupScheme k) (X : SchemeOver k) : triple T X ⟶ X :=
  snd T.X (T.X ⊗ X) ≫ snd T.X X

private theorem linearizationUnit_of_universal (L : Pull (snd T.X X) F ≅ Pull a.smul F)
    (hu : ∃ h : actOn a (1 : X ⟶ T.X) (𝟙 X) = 𝟙 X,
      TransportHom L 1 (𝟙 X) ≫ (pullCongr F h).hom = 𝟙 _) (S : SchemeOver k) (x : S ⟶ X) :
    ∃ h : actOn a (1 : S ⟶ T.X) x = x,
      TransportHom L 1 x ≫ (pullCongr F h).hom = 𝟙 _ := by
  obtain ⟨h, hu⟩ := hu
  exact unitAt_of_unitAt L x (𝟙 X) h hu (Category.comp_id x)

private theorem linearizationMul_of_universal (L : Pull (snd T.X X) F ≅ Pull a.smul F)
    (hm : ∃ h : actOn a (tripleFirst T X) (actOn a (tripleSecond T X) (tripleBase T X)) =
        actOn a (tripleFirst T X * tripleSecond T X) (tripleBase T X),
      TransportComposition L (tripleFirst T X) (tripleSecond T X) (tripleBase T X) h)
    (S : SchemeOver k) (s t : S ⟶ T.X) (x : S ⟶ X) :
    ∃ h : actOn a s (actOn a t x) = actOn a (s * t) x, TransportComposition L s t x h := by
  obtain ⟨h, hm⟩ := hm
  exact mulAt_of_mulAt L (lift s (lift t x)) _ _ _ h hm
    (by simp) (by simp) (by simp)

end TransportLaws

section ActionFlat

variable {k : Type u} [Field k] {T : GroupScheme k} {X : SchemeOver k} (a : ModObj T.X X)

private theorem projectionFlat (U V : SchemeOver k) : Flat (snd U V).left := by
  change Flat (pullback.snd U.hom V.hom)
  infer_instance

private def actionShear : T.X ⊗ X ≅ T.X ⊗ X where
  hom := lift (fst T.X X) a.smul
  inv := lift (fst T.X X) (actOn a ((fst T.X X)⁻¹) (snd T.X X))
  hom_inv_id := by
    let := a
    apply CartesianMonoidalCategory.hom_ext <;> simp only [Category.assoc, lift_fst, lift_snd, Category.id_comp]
    have H₁ := actOn_comp (a := a) (lift (fst T.X X) a.smul) ((fst T.X X)⁻¹) (snd T.X X)
      (show lift (fst T.X X) a.smul ≫ (fst T.X X)⁻¹ = (fst T.X X)⁻¹ by rw [GrpObj.comp_inv, lift_fst]) (lift_snd _ _)
    rw [H₁]
    have h : actOn a (fst T.X X) (snd T.X X) = a.smul := by simp [actOn]
    rw [← h]
    exact inv_smul_smul (fst T.X X) (snd T.X X)
  inv_hom_id := by
    let := a
    apply CartesianMonoidalCategory.hom_ext <;> simp only [Category.assoc, lift_fst, lift_snd, Category.id_comp]
    exact smul_inv_smul (fst T.X X) (snd T.X X)

private theorem actionFlat : Flat a.smul.left := by
  let e := actionShear a
  let : Flat (snd T.X X).left := projectionFlat _ _
  have h : e.hom ≫ snd T.X X = a.smul := lift_snd _ _
  rw [← h, Over.comp_left]
  let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  infer_instance

private theorem tensor_snd_isPullback (U : SchemeOver k) {Y : SchemeOver k} (j : Y ⟶ X) :
    IsPullback (𝟙 U ⊗ₘ j).left (snd U Y).left (snd U X).left j.left := by
  have h₁ : (𝟙 U ⊗ₘ j).left ≫ (fst U X).left = (fst U Y).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left
      (show (𝟙 U ⊗ₘ j) ≫ fst U X = fst U Y by simp)
  have h₂ : (𝟙 U ⊗ₘ j).left ≫ (snd U X).left = (snd U Y).left ≫ j.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left
      (show (𝟙 U ⊗ₘ j) ≫ snd U X = snd U Y ≫ j by simp)
  apply (IsPullback.of_right (h₁₂ := (fst U X).left) (h₂₂ := X.hom)
    (v₁₃ := U.hom) ?_ h₂ (IsPullback.of_hasPullback U.hom X.hom))
  rw [h₁, j.w]
  exact IsPullback.of_hasPullback U.hom Y.hom

private theorem tripleActionFlat :
    Flat (actOn a (tripleFirst T X * tripleSecond T X) (tripleBase T X)).left := by
  let p := snd T.X (T.X ⊗ X)
  let c : triple T X ⟶ T.X ⊗ X := 𝟙 T.X ⊗ₘ a.smul
  have h₁ : actOn a (tripleSecond T X) (tripleBase T X) = p ≫ a.smul := by
    change lift (p ≫ fst T.X X) (p ≫ snd T.X X) ≫ a.smul = _
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have h₂ : actOn a (tripleFirst T X * tripleSecond T X) (tripleBase T X) = c ≫ a.smul := by
    let := a
    change (tripleFirst T X * tripleSecond T X) • tripleBase T X = _
    rw [mul_smul]
    change actOn a (tripleFirst T X) (actOn a (tripleSecond T X) (tripleBase T X)) = _
    rw [h₁]
    have hc : lift (tripleFirst T X) (p ≫ a.smul) = c := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [c, p, tripleFirst]
    change lift (tripleFirst T X) (p ≫ a.smul) ≫ a.smul = _
    rw [hc]
  let : Flat a.smul.left := actionFlat a
  let : Flat c.left := MorphismProperty.of_isPullback (P := @Flat) (tensor_snd_isPullback T.X a.smul).flip
    ‹Flat a.smul.left›
  rw [h₂, Over.comp_left]
  infer_instance

end ActionFlat

section LinearizedKernel

variable {k : Type u} [Field k] {T : GroupScheme k} {X : SchemeOver k}
  {a : ModObj T.X X} {F G : X.left.Modules}

set_option maxHeartbeats 100000 in
private theorem kernelUnit (K : Linearization a G) (L : Pull (snd T.X X) F ≅ Pull a.smul F)
    (f : F ⟶ G) [Mono f]
    (hf : CommSq L.hom ((projectionPull T X).map f) ((actionPull a).map f) K.iso.hom) :
    ∃ h : actOn a (1 : X ⟶ T.X) (𝟙 X) = 𝟙 X,
      TransportHom L 1 (𝟙 X) ≫ (pullCongr F h).hom = 𝟙 _ := by
  obtain ⟨h, hu⟩ := K.unit X (𝟙 X)
  let xid : X ⟶ X := 𝟙 X
  let P := Scheme.Modules.pullback xid.left
  let : P.PreservesMonomorphisms := by
    change (Scheme.Modules.pullback ((𝟙 X : X ⟶ X).left)).PreservesMonomorphisms
    rw [Over.id_left]
    exact Functor.PreservesMonomorphisms.of_iso (Scheme.Modules.pullbackId X.left).symm
  let : Mono (PullMap (𝟙 X) f) := inferInstanceAs (Mono (P.map f))
  exact ⟨h, cancelUnitMono (transportSquare hf 1 (𝟙 X)) (pullCongrSquare h f) hu⟩

set_option maxHeartbeats 450000 in
private theorem mul_of_mono_at (K : Linearization a G) (L : Pull (snd T.X X) F ≅ Pull a.smul F)
    (f : F ⟶ G)
    (hf : CommSq L.hom ((projectionPull T X).map f) ((actionPull a).map f) K.iso.hom)
    (S : SchemeOver k) (s t : S ⟶ T.X) (x : S ⟶ X) [Mono (PullMap (actOn a (s * t) x) f)] :
    ∃ h : actOn a s (actOn a t x) = actOn a (s * t) x, TransportComposition L s t x h := by
  obtain ⟨h, hm⟩ := K.mul S s t x
  have H₁ := transportSquare hf t x
  have H₂ := transportSquare hf s (actOn a t x)
  have H₃ := pullCongrSquare h f
  have H₄ := transportSquare hf (s * t) x
  change ComposesTo (TransportHom K.iso t x) (TransportHom K.iso s (actOn a t x))
    (pullCongr G h).hom (TransportHom K.iso (s * t) x) at hm
  refine ⟨h, ?_⟩
  change ComposesTo (TransportHom L t x) (TransportHom L s (actOn a t x))
    (pullCongr F h).hom (TransportHom L (s * t) x)
  exact cancelCompositionMono H₁ H₂ H₃ H₄ hm

private theorem mono_pullMap_of_flat {S : SchemeOver k} (p : S ⟶ X) (f : F ⟶ G)
    [Flat p.left] [Mono f] : Mono (PullMap p f) := by
  let P := Scheme.Modules.pullback p.left
  let : P.PreservesHomology := FlatCohomology.flatPullbackExact p.left
  let : PreservesFiniteLimits P := Functor.preservesFiniteLimits_of_preservesHomology P
  exact inferInstanceAs (Mono (P.map f))

set_option backward.isDefEq.respectTransparency false in
private theorem kernelMul (K : Linearization a G) (L : Pull (snd T.X X) F ≅ Pull a.smul F)
    (f : F ⟶ G) [Mono f]
    (hf : CommSq L.hom ((projectionPull T X).map f) ((actionPull a).map f) K.iso.hom) :
    ∃ h : actOn a (tripleFirst T X) (actOn a (tripleSecond T X) (tripleBase T X)) =
        actOn a (tripleFirst T X * tripleSecond T X) (tripleBase T X),
      TransportComposition L (tripleFirst T X) (tripleSecond T X) (tripleBase T X) h := by
  let s := tripleFirst T X
  let t := tripleSecond T X
  let x := tripleBase T X
  let y := actOn a (s * t) x
  let : Flat y.left := tripleActionFlat a
  let h : Mono (PullMap y f) := mono_pullMap_of_flat y f
  exact @mul_of_mono_at k _ T X a F G K L f hf _ s t x h

private def linearizationOfMono (K : Linearization a G)
    (L : Pull (snd T.X X) F ≅ Pull a.smul F) (f : F ⟶ G) [Mono f]
    (hf : CommSq L.hom ((projectionPull T X).map f) ((actionPull a).map f) K.iso.hom) :
    Linearization a F where
  iso := L
  unit := linearizationUnit_of_universal L (kernelUnit K L f hf)
  mul := linearizationMul_of_universal L (kernelMul K L f hf)

set_option backward.isDefEq.respectTransparency false in
private def kernelLinearizationIso (L : Linearization a F) (K : Linearization a G) (f : F ⟶ G)
    (hf : IsLinearizedMap L K f) [Flat (snd T.X X).left] [Flat a.smul.left] :
    Pull (snd T.X X) (kernel f) ≅ Pull a.smul (kernel f) := by
  let P := projectionPull T X
  let A := actionPull a
  let : P.PreservesHomology := FlatCohomology.flatPullbackExact (snd T.X X).left
  let : A.PreservesHomology := FlatCohomology.flatPullbackExact a.smul.left
  let : PreservesFiniteLimits P := Functor.preservesFiniteLimits_of_preservesHomology P
  let : PreservesFiniteLimits A := Functor.preservesFiniteLimits_of_preservesHomology A
  exact PreservesKernel.iso P f ≪≫ kernel.mapIso (P.map f) (A.map f) L.iso K.iso hf.symm ≪≫
    (PreservesKernel.iso A f).symm

private theorem kernelLinearizationSquare (L : Linearization a F) (K : Linearization a G)
    (f : F ⟶ G) (hf : IsLinearizedMap L K f) [Flat (snd T.X X).left] [Flat a.smul.left] :
    CommSq (kernelLinearizationIso L K f hf).hom ((projectionPull T X).map (kernel.ι f))
      ((actionPull a).map (kernel.ι f)) L.iso.hom := by
  constructor
  let P := projectionPull T X
  let A := actionPull a
  let : P.PreservesHomology := FlatCohomology.flatPullbackExact (snd T.X X).left
  let : A.PreservesHomology := FlatCohomology.flatPullbackExact a.smul.left
  let : PreservesFiniteLimits P := Functor.preservesFiniteLimits_of_preservesHomology P
  let : PreservesFiniteLimits A := Functor.preservesFiniteLimits_of_preservesHomology A
  let e := kernel.mapIso (P.map f) (A.map f) L.iso K.iso hf.symm
  have he : e.hom ≫ kernel.ι (A.map f) = kernel.ι (P.map f) ≫ L.iso.hom :=
    kernel.lift_ι _ _ _
  change (PreservesKernel.iso P f).hom ≫ e.hom ≫ (PreservesKernel.iso A f).inv ≫
      A.map (kernel.ι f) = P.map (kernel.ι f) ≫ L.iso.hom
  rw [PreservesKernel.iso_inv_ι, he]
  have hp : (PreservesKernel.iso P f).hom ≫ kernel.ι (P.map f) = P.map (kernel.ι f) := by
    rw [← PreservesKernel.iso_inv_ι P f, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hp]

/-- Kernels of linearized morphisms carry the induced submodule linearization. -/
theorem kernelLinearization (L : Linearization a F) (K : Linearization a G) (f : F ⟶ G)
    (hf : IsLinearizedMap L K f) :
    ∃ J : Linearization a (kernel f), IsLinearizedMap J L (kernel.ι f) := by
  let : Flat (snd T.X X).left := projectionFlat _ _
  let : Flat a.smul.left := actionFlat a
  let h := kernelLinearizationSquare L K f hf
  exact ⟨linearizationOfMono L (kernelLinearizationIso L K f hf) (kernel.ι f) h, h.w⟩

end LinearizedKernel

section AffineSectionMorphisms

variable {R : CommRingCat.{u}} {F G : (Spec R).Modules}

set_option backward.isDefEq.respectTransparency false in
private theorem affine_hom_ext_of_sections [F.IsQuasicoherent] (f g : F ⟶ G)
    (h : (moduleSpecΓFunctor (R := R)).map f = (moduleSpecΓFunctor (R := R)).map g) : f = g := by
  let : IsIso F.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ F).mp inferInstance
  apply (cancel_epi F.fromTildeΓ).mp
  let P := moduleSpecΓFunctor (R := R)
  have hf : (tilde.functor R).map (P.map f) ≫ G.fromTildeΓ = F.fromTildeΓ ≫ f :=
    fromTildeΓNatTrans.naturality f
  have hg : (tilde.functor R).map (P.map g) ≫ G.fromTildeΓ = F.fromTildeΓ ≫ g :=
    fromTildeΓNatTrans.naturality g
  rw [← hf, ← hg, h]

set_option backward.isDefEq.respectTransparency false in
private theorem mono_of_affineSections_injective [F.IsQuasicoherent] [G.IsQuasicoherent]
    (f : F ⟶ G) (hf : Function.Injective ((moduleSpecΓFunctor (R := R)).map f)) : Mono f := by
  let P := moduleSpecΓFunctor (R := R)
  let : (kernel f).IsQuasicoherent := kernel_isQuasicoherent f
  apply Abelian.mono_of_kernel_ι_eq_zero
  apply affine_hom_ext_of_sections
  have h := congrArg P.map (kernel.condition f)
  let : P.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  rw [P.map_comp, P.map_zero] at h
  ext x
  apply hf
  have hx := congrArg (fun l : P.obj (kernel f) ⟶ P.obj G => l x) h
  change P.map f (P.map (kernel.ι f) x) = 0 at hx
  change P.map f (P.map (kernel.ι f) x) = P.map f (P.map 0 x)
  rw [P.map_zero]
  have hz : (0 : P.obj (kernel f) ⟶ P.obj F) x = 0 := rfl
  rwa [hz, map_zero]

end AffineSectionMorphisms

section AffineSubmodules

variable {k : Type u} [Field k] {T : GroupScheme k} (R : TestAlgebra k)
variable {a : ModObj T.X (affineScheme R)}

open private WeightGrading.mapLinearEquiv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

private def ModuleGrading.mapLinearEquiv {G : RingGrading k (Character T) R} {A B : ModuleCat.{u} R}
    (H : ModuleGrading G A) (e : A ≃ₗ[R] B) : ModuleGrading G B where
  toWeightGrading := WeightGrading.mapLinearEquiv H.toWeightGrading (e.restrictScalars k)
  smul_mem := by
    intro i j r v hr hv
    change ∃ w ∈ H.piece j, e w = v at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨r • w, H.smul_mem hr hw, e.map_smul r w⟩

private theorem ModuleGrading.mem_mapLinearEquiv {G : RingGrading k (Character T) R}
    {A B : ModuleCat.{u} R} (H : ModuleGrading G A) (e : A ≃ₗ[R] B) (s : B) (χ : Character T) :
    s ∈ (ModuleGrading.mapLinearEquiv R H e).piece χ ↔ e.symm s ∈ H.piece χ := by
  change (∃ w ∈ H.piece χ, e w = s) ↔ _
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [e.symm_apply_apply]
  · exact fun hs => ⟨e.symm s, hs, e.apply_symm_apply _⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
private theorem affine_submodule_inclusion (M : EquivariantQuasicoherent a)
    (P : Submodule R ((affineSections R).obj M.sheaf)) :
    ∃ i : tilde (R := affineRing R) (ModuleCat.of R P) ⟶ M.sheaf,
      Mono i ∧ ∀ s : ModuleCat.of R P, (affineSections R).map i
        ((tilde.isoTop (R := affineRing R) (ModuleCat.of R P)).hom s) = s.val := by
  let N : ModuleCat (affineRing R) := ModuleCat.of R P
  let H : (Spec (affineRing R)).Modules := M.sheaf
  let S := moduleSpecΓFunctor (R := affineRing R)
  let Z := S.obj H
  let p : N ⟶ Z := ModuleCat.ofHom (R := ↥(affineRing R)) (X := ↥N) (Y := ↥Z) P.subtype
  let i : tilde N ⟶ H := tilde.map p ≫ H.fromTildeΓ
  let A := tilde.adjunction (R := affineRing R)
  have hi₀ : (A.homEquiv N H).symm p = i := A.homEquiv_counit N H p
  have h : (tilde.isoTop N).hom ≫ S.map i = p := by
    change A.unit.app N ≫ S.map i = _
    exact (A.homEquiv_unit N H i).symm.trans (hi₀ ▸ (A.homEquiv N H).apply_symm_apply p)
  have he (s : N) : S.map i ((tilde.isoTop N).hom s) = s.val :=
    congrArg (fun m : N ⟶ Z => m s) h
  let : M.sheaf.IsQuasicoherent := M.quasicoherent
  have hi : Function.Injective (S.map i) := by
    have hbij : Function.Surjective (tilde.isoTop N).hom := (ConcreteCategory.bijective_of_isIso _).2
    intro s t hst
    obtain ⟨s, rfl⟩ := hbij s
    obtain ⟨t, rfl⟩ := hbij t
    rw [he, he] at hst
    exact congrArg (fun z : N => (tilde.isoTop N).hom z) (Subtype.ext hst)
  exact ⟨i, mono_of_affineSections_injective i hi, he⟩

set_option maxHeartbeats 500000 in
/-- On an invariant affine chart, finitely many prescribed sections lie in a
coherent equivariant subobject of the given quasi-coherent module. -/
theorem affine_coherentSubobject_contains (hT : IsSplitTorus T) [IsNoetherianRing R]
    (M : EquivariantQuasicoherent a) (S : Finset ((affineSections R).obj M.sheaf)) :
    ∃ (F : EquivariantCoherent a) (i : F.sheaf ⟶ M.sheaf),
      Mono i ∧ IsLinearizedMap F.lin M.lin i ∧ ∀ s ∈ S,
        ∃ t : (affineSections R).obj F.sheaf, (affineSections R).map i t = s := by
  obtain ⟨G, E, _, hmap, _⟩ := equivariantAffineComparison hT R a
  let H := E M.sheaf M.quasicoherent M.lin
  obtain ⟨P, J, hP, hS, hJ⟩ := exists_finite_graded_submodule G.val H S
  let A : ModuleCat (affineRing R) := ModuleCat.of R P
  let F := tilde A
  let e := (tilde.isoTop A).toLinearEquiv
  let V := ModuleGrading.mapLinearEquiv R J e
  let hF : F.IsQuasicoherent := inferInstance
  let L := (E F hF).symm V
  let : Module.Finite R A := hP
  obtain ⟨i, hi, hi'⟩ := affine_submodule_inclusion R M P
  have hlin : IsLinearizedMap L M.lin i := by
    apply (hmap F M.sheaf hF M.quasicoherent L M.lin i).mpr
    have hE : E F hF L = V := (E F hF).apply_symm_apply V
    intro χ v hv
    rw [hE] at hv
    have hq := (ModuleGrading.mem_mapLinearEquiv R J e v χ).mp hv
    have hw := (hJ χ (e.symm v)).mp hq
    have hei : (affineSections R).map i v = (e.symm v).val := by
      have h := hi' (e.symm v)
      change (affineSections R).map i (e (e.symm v)) = (e.symm v).val at h
      let ψ := (affineSections R).map i
      exact (congrArg (fun z : (affineSections R).obj F => ψ z) (e.apply_symm_apply v)).symm.trans h
    rw [hei]
    exact hw
  refine ⟨⟨F, finitePresentation_tilde A, L⟩, i, hi, hlin, fun s hs => ?_⟩
  let s' : A := ⟨s, hS s hs⟩
  exact ⟨(tilde.isoTop A).hom s', hi' s'⟩

end AffineSubmodules

section PrincipalSections

open PrimeSpectrum

set_option backward.isDefEq.respectTransparency false in
/-- For a quasi-coherent sheaf on an affine scheme, finitely many global
sections suffice to generate each of a finite family of principal restrictions
where the sections are finite over the corresponding local ring of sections. -/
theorem exists_finite_sections_generating_basicOpens {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] {I : Type u} [Finite I] (r : I → R)
    (hfin : ∀ i, Module.Finite Γ(Spec R, basicOpen (r i)) Γ(M, basicOpen (r i))) :
    ∃ S : Finset Γ(M, ⊤), ∀ (N : (Spec R).Modules) (f : N ⟶ M),
      (∀ s ∈ S, ∃ t : Γ(N, ⊤), f.val.app (op ⊤) t = s) →
      ∀ i, Function.Surjective (f.val.app (op (basicOpen (r i)))) := by
  classical
  let := Fintype.ofFinite I
  let V (i : I) := basicOpen (r i)
  let B (i : I) := Γ(Spec R, V i)
  let P := modulesSpecToSheaf (R := R)
  let res (N : (Spec R).Modules) (i : I) := (P.obj N).obj.map (V i).leTop.op
  have hfg (i : I) : (⊤ : Submodule (B i) Γ(M, V i)).FG := by
    let : Module.Finite (B i) Γ(M, V i) := hfin i
    exact Module.Finite.fg_top
  choose s hs using hfg
  have hM : IsLocalizing (P.obj M) := (isIso_fromTildeΓ_iff_isLocalizing M).mp
    ((isQuasicoherent_iff_isIso_fromTildeΓ M).mp inferInstance)
  have hn (i : I) (w : s i) : ∃ (v : Γ(M, ⊤)) (n : ℕ),
      (r i)^n • w.val = res M i v := by
    let : IsLocalizedModule.Away (r i) (res M i).hom := hM (r i)
    obtain ⟨⟨v, _, n, rfl⟩, hv⟩ := IsLocalizedModule.surj (.powers (r i)) (res M i).hom w.val
    exact ⟨v, n, hv⟩
  choose v n hv using hn
  let S := Finset.univ.biUnion (fun i => (s i).attach.image (v i))
  refine ⟨S, fun N f hf i => ?_⟩
  let g := (f.val.app (op (V i))).hom
  change Function.Surjective g
  apply LinearMap.range_eq_top.mp
  apply le_antisymm le_top
  rw [← hs i]
  apply Submodule.span_le.mpr
  intro w hw
  let w' : s i := ⟨w, hw⟩
  obtain ⟨t, ht⟩ := hf (v i w') (Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨w', Finset.mem_attach _ _, rfl⟩⟩)
  have hnat : g (res N i t) = res M i (f.val.app (op ⊤) t) := by
    exact congr($( (P.map f).hom.naturality (V i).leTop.op) t)
  have hu : IsUnit (algebraMap R (B i) ((r i)^(n i w'))) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (S := B i) (r i)).pow _
  apply (g.range.smul_mem_iff_of_isUnit hu).mp
  refine ⟨res N i t, ?_⟩
  rw [hnat, ht]
  exact (hv i w').symm.trans (IsScalarTower.algebraMap_smul (A := B i) (r i ^ n i w') w).symm

end PrincipalSections

section Preimage

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y} {j : Y ⟶ X}

private theorem openPullback_isQuasicoherent {V U : Scheme.{u}} (f : V ⟶ U)
    [IsOpenImmersion f] (M : U.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent V.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M) inferInstance

private theorem linearizedMap_id {F : X.left.Modules} (L : Linearization a F) :
    IsLinearizedMap L L (𝟙 F) := by
  unfold IsLinearizedMap
  rw [(Scheme.Modules.pullback a.smul.left).map_id,
    (Scheme.Modules.pullback (snd T.X X).left).map_id, Category.comp_id, Category.id_comp]

private theorem linearizedMap_of_mono_comp {F G H : X.left.Modules}
    (L : Linearization a F) (K : Linearization a G) (J : Linearization a H)
    (f : F ⟶ G) (g : G ⟶ H) [Mono g] (hg : IsLinearizedMap K J g)
    (h : IsLinearizedMap L J (f ≫ g)) : IsLinearizedMap L K f := by
  let P := Scheme.Modules.pullback (snd T.X X).left
  let A := Scheme.Modules.pullback a.smul.left
  let : Flat a.smul.left := actionFlat a
  let : Mono (A.map g) := mono_pullMap_of_flat a.smul g
  change K.iso.hom ≫ A.map g = P.map g ≫ J.iso.hom at hg
  change L.iso.hom ≫ A.map (f ≫ g) = P.map (f ≫ g) ≫ J.iso.hom at h
  change L.iso.hom ≫ A.map f = P.map f ≫ K.iso.hom
  apply (cancel_mono (A.map g)).mp
  simp only [Category.assoc, ← A.map_comp, h, P.map_comp, hg]

set_option backward.isDefEq.respectTransparency false in
private theorem compare_open_kernel [IsOpenImmersion j.left] {M V : X.left.Modules}
    {H N : Y.left.Modules} (f : M ⟶ V) (i : H ⟶ N) [Mono i]
    (e : Pull j M ≅ N) (c : Pull j V ≅ cokernel i)
    (h : PullMap j f ≫ c.hom = e.hom ≫ cokernel.π i) :
    ∃ d : Pull j (kernel f) ≅ H, d.hom ≫ i = PullMap j (kernel.ι f) ≫ e.hom := by
  let P := Scheme.Modules.pullback j.left
  let : P.PreservesHomology := FlatCohomology.flatPullbackExact j.left
  let : PreservesFiniteLimits P := Functor.preservesFiniteLimits_of_preservesHomology P
  let D := PreservesKernel.iso P f
  let E := kernel.mapIso (P.map f) (cokernel.π i) e c h
  let Hlim := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i)
  let K := (kernelIsKernel (cokernel.π i)).conePointUniqueUpToIso Hlim
  have hK : K.hom ≫ i = kernel.ι (cokernel.π i) :=
    IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel (cokernel.π i)) Hlim WalkingParallelPair.zero
  have hE : E.hom ≫ kernel.ι (cokernel.π i) = kernel.ι (P.map f) ≫ e.hom := kernel.lift_ι _ _ _
  have hD : D.hom ≫ kernel.ι (P.map f) = P.map (kernel.ι f) := by
    rw [← PreservesKernel.iso_inv_ι P f, Iso.hom_inv_id_assoc]
  refine ⟨D ≪≫ E ≪≫ K, ?_⟩
  change (D.hom ≫ E.hom ≫ K.hom) ≫ i = P.map (kernel.ι f) ≫ e.hom
  rw [Category.assoc, Category.assoc, hK, hE, reassoc_of% hD]

set_option backward.isDefEq.respectTransparency false in
/-- The preimage of a quasi-coherent equivariant subobject under open restriction. -/
private theorem equivariant_preimage_of_open_subobject [IsOpenImmersion j.left] [QuasiCompact j.left]
    [IsLocallyNoetherian X.left] (hadj : OpenDirectImageAdjunction.{u}) (hj : IsEquivariantMap a b j)
    (M : EquivariantQuasicoherent a) (N H : EquivariantQuasicoherent b)
    (e : Pull j M.sheaf ≅ N.sheaf) (he : IsLinearizedMap (pullbackLinearization hj M.lin) N.lin e.hom)
    (i : H.sheaf ⟶ N.sheaf) [Mono i] (hi : IsLinearizedMap H.lin N.lin i) :
    ∃ (V : EquivariantQuasicoherent a)
      (f : M.sheaf ⟶ V.sheaf) (K : Linearization a (kernel f))
      (_ : (kernel f).IsQuasicoherent) (d : Pull j (kernel f) ≅ H.sheaf),
      IsLinearizedMap K M.lin (kernel.ι f) ∧
      IsLinearizedMap (pullbackLinearization hj K) H.lin d.hom ∧
      PullMap j (kernel.ι f) ≫ e.hom = d.hom ≫ i ∧
      ∀ {Z : SchemeOver k} (l : Z ⟶ X),
        IsZero (Pull l ((Scheme.Modules.pushforward j.left).obj (cokernel i))) →
        IsZero (Pull l V.sheaf) := by
  let : M.sheaf.IsQuasicoherent := M.quasicoherent
  let : N.sheaf.IsQuasicoherent := N.quasicoherent
  let : H.sheaf.IsQuasicoherent := H.quasicoherent
  let Q := cokernel i
  let : Q.IsQuasicoherent := cokernel_isQuasicoherent i
  obtain ⟨L, hL⟩ := cokernelLinearization H.lin N.lin i hi
  obtain ⟨J, c, hc, _, hmate⟩ := hadj j hj ⟨Q, inferInstance, L⟩
  let W := (Scheme.Modules.pushforward j.left).obj Q
  let : W.IsQuasicoherent := openPushforward_isQuasicoherent j.left Q
  let V : EquivariantQuasicoherent a := ⟨W, inferInstance, J⟩
  let adj := Scheme.Modules.pullbackPushforwardAdjunction j.left
  let δ := e.hom ≫ cokernel.π i
  let f := adj.homEquiv M.sheaf Q δ
  have hδ : IsLinearizedMap (pullbackLinearization hj M.lin) L δ :=
    linearizedMap_comp he hL
  have hf : IsLinearizedMap M.lin J f :=
    hmate M.lin (pullbackLinearization hj M.lin)
      (pullbackLinearizationComparison_of_linearized hj _ _ (Iso.refl _) (linearizedMap_id _)) δ hδ
  obtain ⟨K, hK⟩ := kernelLinearization M.lin J f hf
  have hfc : PullMap j f ≫ c.hom = e.hom ≫ cokernel.π i := by
    rw [hc]
    have ha := (adj.homEquiv M.sheaf Q).symm_apply_apply δ
    rw [adj.homEquiv_counit] at ha
    exact ha
  obtain ⟨d, hd⟩ := compare_open_kernel f i e c hfc
  have hdi : IsLinearizedMap (pullbackLinearization hj K) N.lin (d.hom ≫ i) := by
    rw [hd]
    exact linearizedMap_comp (pullbackLinearization_map hj _ hK) he
  have hd' : IsLinearizedMap (pullbackLinearization hj K) H.lin d.hom :=
    linearizedMap_of_mono_comp _ _ _ _ i hi hdi
  exact ⟨V, f, K, kernel_isQuasicoherent f, d, hK, hd', hd.symm, fun _ h => h⟩

end Preimage

section LocalRestriction

open LinearAlgebraicGroups.ProjectiveFiniteness (finite_sections_of_isAffineOpen)
open private finite_sections_image_of_isOpenImmersion
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_of_open_cover {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G)
    {I : Type u} (U : I → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hf : ∀ i, IsIso ((Scheme.Modules.pullback (U i).ι).map f)) : IsIso f := by
  let B := {V : X.Opens // ∃ i, V ≤ U i}
  have hb : Opens.IsBasis (Set.range (Subtype.val : B → X.Opens)) := by
    apply Opens.isBasis_iff_nbhd.mpr
    intro V x hx
    have hx' : x ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
    exact ⟨V ⊓ U i, ⟨⟨_, i, inf_le_right⟩, rfl⟩, ⟨hx, hi⟩, inf_le_left⟩
  let Z := SheafOfModules.toSheaf X.ringCatSheaf
  have hZ : IsIso (Z.map f) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis hb
    intro V
    obtain ⟨i, hi⟩ := V.property
    let g := (U i).ι
    let W := g ⁻¹ᵁ V.val
    have hw : g ''ᵁ W = V.val := by
      apply le_antisymm (g.image_preimage_le _)
      intro x hx
      exact ⟨⟨x, hi hx⟩, hx, rfl⟩
    have h := (NatIso.isIso_map_iff (restrictFunctorIsoPullback g) f).mpr (hf i)
    have : IsIso ((restrictFunctor g).map f) := h
    have h' := (evaluation (R := (U i).toScheme.ringCatSheaf) (op W)).map_isIso
      ((restrictFunctor g).map f)
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hb' := ConcreteCategory.bijective_of_isIso
      ((evaluation (R := (U i).toScheme.ringCatSheaf) (op W)).map ((restrictFunctor g).map f))
    change Function.Bijective (f.val.app (op V.val))
    change Function.Bijective (f.val.app (op (g ''ᵁ W))) at hb'
    rwa [hw] at hb'
  let : Z.ReflectsIsomorphisms := inferInstanceAs ((SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms)
  exact isIso_of_reflects_iso f Z

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_of_affine_top_bijective {X : Scheme.{u}} [IsAffine X]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G)
    (hf : Function.Bijective (f.val.app (op ⊤))) : IsIso f := by
  let e := X.isoSpec
  let R := CommRingCat.of Γ(X, ⊤)
  let P := restrictFunctor e.inv
  let g := P.map f
  have himage : e.inv ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact Scheme.Hom.opensRange_of_isIso _
  have htop : IsIso (((modulesSpecToSheaf (R := R)).map g).hom.app (op ⊤)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (f.val.app (op (e.inv ''ᵁ (⊤ : (Spec R).Opens))))
    rw [himage]
    exact hf
  have hloc (M : (Spec R).Modules) [M.IsQuasicoherent] :
      IsLocalizing ((modulesSpecToSheaf (R := R)).obj M) :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  let : IsIso ((modulesSpecToSheaf (R := R)).map g) :=
    isLocalizing_of_isIso_app_top htop (hloc (P.obj F)) (hloc (P.obj G))
  have : IsIso g := isIso_of_reflects_iso g (modulesSpecToSheaf (R := R))
  let E := (restrictFunctorComp e.hom e.inv).symm ≪≫
    restrictFunctorCongr e.hom_inv_id ≪≫ restrictFunctorId
  exact (NatIso.isIso_map_iff E f).mp
    (show IsIso ((restrictFunctor e.hom).map g) by infer_instance)

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_pullback_of_affine_image_sections {X Y : Scheme.{u}} [IsAffine Y]
    (f : Y ⟶ X) [IsOpenImmersion f] {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (i : F ⟶ G) (hi : Function.Bijective (i.val.app (op f.opensRange))) :
    IsIso ((Scheme.Modules.pullback f).map i) := by
  apply (NatIso.isIso_map_iff (restrictFunctorIsoPullback f) i).mp
  apply isIso_of_affine_top_bijective
  change Function.Bijective (i.val.app (op (f ''ᵁ (⊤ : Y.Opens))))
  rwa [Scheme.Hom.image_top_eq_opensRange]

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_of_affineOpenCover {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] {I : Type u} (U : I → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (hM : ∀ i, ((Scheme.Modules.pullback (U i).ι).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  have hp (i : I) : ∃ P : (M.over (U i)).Presentation, P.IsFinite := by
    let Z := (U i).toScheme
    let r := (U i).ι
    let : IsAffine Z := hU i
    let : (M.restrict r).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation Z.ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback r).app M).symm (hM i)
    have hfin := finite_sections_image_of_isOpenImmersion r M ⊤
      (finite_sections_of_isAffineOpen (M.restrict r) (isAffineOpen_top Z))
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι] at hfin
    let := hfin
    exact finitePresentation_on_affine_open M (hU i)
  choose P hP using hp
  let D : M.QuasicoherentData :=
    { I := I
      X := U
      coversTop := (Opens.coversTop_iff _ _).mpr hcov
      presentation := P }
  have hD : D.IsFinitePresentation := by
    constructor
    exact hP
  exact SheafOfModules.IsFinitePresentation.mk (M := M) ⟨D, hD⟩

end LocalRestriction

section AffineChart

open LinearAlgebraicGroups.ProjectiveFiniteness (finite_sections_of_isAffineOpen)
open private finite_sections_image_of_isOpenImmersion
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

open PrimeSpectrum

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_on_intersection {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) (j : Y ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (U : Z.Opens) (hU : U ≤ i ⁻¹ᵁ j.opensRange) (M : X.Modules)
    (hM : ((Scheme.Modules.pullback j).obj M).IsFinitePresentation) :
    ((Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pullback i).obj M)).IsFinitePresentation := by
  let f := U.ι ≫ i
  have hr : Set.range f ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    exact hU x.property
  let g := IsOpenImmersion.lift j f hr
  have hg : g ≫ j = f := IsOpenImmersion.lift_fac _ _ _
  let : IsOpenImmersion (g ≫ j) := hg.symm ▸ (inferInstance : IsOpenImmersion f)
  let : IsOpenImmersion g := IsOpenImmersion.of_comp g j
  let e := (Scheme.Modules.pullbackComp g j).app M ≪≫
    (Scheme.Modules.pullbackCongr hg).app M ≪≫ ((Scheme.Modules.pullbackComp U.ι i).app M).symm
  exact (SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso e
    (openPullback_finitePresentation g _ hM)

set_option backward.isDefEq.respectTransparency false in
private theorem affine_coherentSubobject_on_open {k : Type u} [Field k] {T : GroupScheme k}
    (R : TestAlgebra k) [IsNoetherianRing R] {a : ModObj T.X (affineScheme R)}
    (hT : IsSplitTorus T) (M : EquivariantQuasicoherent a)
    (W : (Spec (affineRing R)).Opens)
    (hM : ∀ U : (Spec (affineRing R)).Opens, U ≤ W →
      ((Scheme.Modules.pullback U.ι).obj M.sheaf).IsFinitePresentation) :
    ∃ (F : EquivariantCoherent a) (i : F.sheaf ⟶ M.sheaf),
      Mono i ∧ IsLinearizedMap F.lin M.lin i ∧ IsIso ((Scheme.Modules.pullback W.ι).map i) := by
  let : M.sheaf.IsQuasicoherent := M.quasicoherent
  let : NoetherianSpace (Spec (affineRing R)) := inferInstance
  obtain ⟨I, hI, r, hr⟩ := isBasis_basic_opens.exists_iSup_eq_of_isCompact W
    (NoetherianSpace.isCompact _)
  let := hI
  let U (n : I) : (Spec (affineRing R)).Opens := basicOpen (r n)
  have hUw (n : I) : U n ≤ W := by
    rw [hr]
    exact le_iSup U n
  have hfin (n : I) : Module.Finite Γ(Spec (affineRing R), U n) Γ(M.sheaf, U n) := by
    let g := (U n).ι
    let : IsAffine (U n).toScheme := IsAffineOpen.Spec_basicOpen _
    let : (M.sheaf.restrict g).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation (U n).toScheme.ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback g).app M.sheaf).symm (hM (U n) (hUw n))
    have hfin' := finite_sections_image_of_isOpenImmersion g M.sheaf ⊤
      (finite_sections_of_isAffineOpen (M.sheaf.restrict g) (isAffineOpen_top _))
    rwa [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι] at hfin'
  obtain ⟨S, hS⟩ := exists_finite_sections_generating_basicOpens M.sheaf r hfin
  obtain ⟨F, i, hi, hlin, hcontains⟩ := affine_coherentSubobject_contains R hT M S
  let := hi
  let : F.sheaf.IsFinitePresentation := F.coherent
  have hsurj : ∀ n : I, Function.Surjective (i.val.app (op (U n))) :=
    hS F.sheaf i hcontains
  have hiso (n : I) : IsIso ((Scheme.Modules.pullback (U n).ι).map i) := by
    let : IsAffine (U n).toScheme := IsAffineOpen.Spec_basicOpen _
    have hi' : Function.Injective (i.val.app (op (U n))) :=
      (ModuleCat.mono_iff_injective _).mp
        ((evaluation (R := (Spec (affineRing R)).ringCatSheaf) (op (U n))).map_mono i)
    apply isIso_pullback_of_affine_image_sections (U n).ι i
    rw [Scheme.Opens.opensRange_ι]
    exact ⟨hi', hsurj n⟩
  refine ⟨F, i, hi, hlin, ?_⟩
  let U' (n : I) := W.ι ⁻¹ᵁ U n
  have hcov : ⨆ n, U' n = ⊤ := by
    calc
      (⨆ n, U' n) = W.ι ⁻¹ᵁ (⨆ n, U n) := (Scheme.Hom.preimage_iSup _ _).symm
      _ = W.ι ⁻¹ᵁ W := congrArg (fun V => W.ι ⁻¹ᵁ V) hr.symm
      _ = ⊤ := by
        ext x
        exact iff_of_true x.property trivial
  apply isIso_of_open_cover _ U' hcov
  intro n
  let p := (W.ι ∣_ U n)
  have hpw : p ≫ (U n).ι = (U' n).ι ≫ W.ι := morphismRestrict_ι _ _
  let E := Scheme.Modules.pullbackComp p (U n).ι ≪≫
    Scheme.Modules.pullbackCongr hpw ≪≫ (Scheme.Modules.pullbackComp (U' n).ι W.ι).symm
  let : IsIso ((Scheme.Modules.pullback (U n).ι).map i) := hiso n
  exact (NatIso.isIso_map_iff E i).mp
    (show IsIso ((Scheme.Modules.pullback p).map
      ((Scheme.Modules.pullback (U n).ι).map i)) by infer_instance)

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_pushforward_isZero_on_open {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) (j : Y ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (Q : Z.Modules)
    (hQ : IsZero ((Scheme.Modules.pullback (i ⁻¹ᵁ j.opensRange).ι).obj Q)) :
    IsZero ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pushforward i).obj Q)) := by
  let W := j.opensRange
  let r := (i ⁻¹ᵁ W).ι
  let G := Scheme.Modules.pushforward i
  let Z' := G.obj Q
  have h₁ : IsZero (Q.restrict r) := hQ.of_iso ((restrictFunctorIsoPullback r).app Q)
  have h₂ : IsZero (Z'.restrict W.ι) :=
    ((Scheme.Modules.pushforward (i ∣_ W)).map_isZero h₁).of_iso
      ((restrictPushforwardIso i W).app Q)
  have h₃ : IsZero ((Scheme.Modules.pullback W.ι).obj Z') :=
    h₂.of_iso ((restrictFunctorIsoPullback W.ι).app Z').symm
  let e := IsOpenImmersion.isoOfRangeEq j W.ι Subtype.range_coe.symm
  have he : e.hom ≫ W.ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let d := (Scheme.Modules.pullbackComp e.hom W.ι).app Z' ≪≫
    (Scheme.Modules.pullbackCongr he).app Z'
  exact ((Scheme.Modules.pullback e.hom).map_isZero h₃).of_iso d.symm

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_kernel_ι_isIso_of_isZero {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] {M V : X.Modules} (f : M ⟶ V)
    (h : IsZero ((Scheme.Modules.pullback j).obj V)) :
    IsIso ((Scheme.Modules.pullback j).map (kernel.ι f)) := by
  let P := Scheme.Modules.pullback j
  let : P.PreservesHomology := FlatCohomology.flatPullbackExact j
  let : PreservesFiniteLimits P := Functor.preservesFiniteLimits_of_preservesHomology P
  let : IsIso (kernel.ι (P.map f)) := kernel.ι_of_zero (h.eq_of_tgt _ _)
  have he : (PreservesKernel.iso P f).hom ≫ kernel.ι (P.map f) = P.map (kernel.ι f) := by
    rw [← PreservesKernel.iso_inv_ι P f, Iso.hom_inv_id_assoc]
  change IsIso (P.map (kernel.ι f))
  rw [← he]
  infer_instance

end AffineChart

section CoherentRefinement

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} (j : Y ⟶ X) [IsOpenImmersion j.left]
  [IsLocallyNoetherian X.left]

set_option backward.isDefEq.respectTransparency false in
private theorem refine_on_affine_chart (hadj : OpenDirectImageAdjunction.{u})
    (hT : IsSplitTorus T) (U : X.left.Opens) (hU : IsAffineOpen U)
    (hInv : a.smul.left ⁻¹ᵁ U = (snd T.X X).left ⁻¹ᵁ U)
    (M : EquivariantQuasicoherent a) (hM : (Pull j M.sheaf).IsFinitePresentation) :
    ∃ (F : EquivariantQuasicoherent a) (m : F.sheaf ⟶ M.sheaf),
      Mono m ∧ IsLinearizedMap F.lin M.lin m ∧ IsIso (PullMap j m) ∧
      ((Scheme.Modules.pullback U.ι).obj F.sheaf).IsFinitePresentation := by
  let Z := openSubscheme X U
  obtain ⟨Rop, ⟨e⟩⟩ := (essImage_algSpec (G := Z)).mpr hU
  let R : TestAlgebra k := Rop.unop
  let i : affineScheme R ⟶ X := e.hom ≫ openEmbedding X U
  let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  let : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  let : IsOpenImmersion i.left := by
    change IsOpenImmersion (e.hom.left ≫ U.ι)
    infer_instance
  have hrange : i.left.opensRange = U := by
    change (e.hom.left ≫ U.ι).opensRange = U
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
  obtain ⟨c, hc⟩ := invariantOpenImmersionAction a i (by rw [hrange]; exact hInv)
  let : M.sheaf.IsQuasicoherent := M.quasicoherent
  let N : EquivariantQuasicoherent c :=
    ⟨Pull i M.sheaf, openPullback_isQuasicoherent i.left M.sheaf, pullbackLinearization hc M.lin⟩
  have hnoeth : IsLocallyNoetherian (Spec (affineRing R)) :=
    LocallyOfFiniteType.isLocallyNoetherian i.left
  let : IsNoetherianRing R := isLocallyNoetherian_Spec.mp hnoeth
  let W := i.left ⁻¹ᵁ j.left.opensRange
  obtain ⟨D, n, hn, hlin, hiso⟩ := affine_coherentSubobject_on_open R hT N W
    (fun V hV => finitePresentation_on_intersection i.left j.left V hV M.sheaf hM)
  let : D.sheaf.IsFinitePresentation := D.coherent
  let := hn
  let D' : EquivariantQuasicoherent c := ⟨D.sheaf, inferInstance, D.lin⟩
  obtain ⟨V, f, K, hqc, d, hK, _, _, hzero⟩ := equivariant_preimage_of_open_subobject hadj hc M N D'
    (Iso.refl _) (linearizedMap_id _) n hlin
  let F : EquivariantQuasicoherent a := ⟨kernel f, hqc, K⟩
  have hQ : IsZero ((Scheme.Modules.pullback W.ι).obj (cokernel n)) := by
    let P := Scheme.Modules.pullback W.ι
    let : IsIso (P.map n) := hiso
    exact (isZero_cokernel_of_epi (P.map n)).of_iso (PreservesCokernel.iso P n)
  have hV := hzero j (pullback_pushforward_isZero_on_open i.left j.left (cokernel n) hQ)
  refine ⟨F, kernel.ι f, inferInstance, hK, pullback_kernel_ι_isIso_of_isZero j.left f hV, ?_⟩
  have hd := (SheafOfModules.isFinitePresentation (affineScheme R).left.ringCatSheaf).prop_of_iso
    d.symm D.coherent
  have he : e.inv.left ≫ i.left = U.ι := by
    change e.inv.left ≫ e.hom.left ≫ U.ι = _
    rw [← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  let d' := (Scheme.Modules.pullbackComp e.inv.left i.left).app F.sheaf ≪≫
    (Scheme.Modules.pullbackCongr he).app F.sheaf
  exact (SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso d'
    (openPullback_finitePresentation e.inv.left _ hd)

set_option backward.isDefEq.respectTransparency false in
private theorem finite_presentation_on_charts (hadj : OpenDirectImageAdjunction.{u})
    (hT : IsSplitTorus T) (M : EquivariantQuasicoherent a)
    (hM : (Pull j M.sheaf).IsFinitePresentation)
    {I : Type u} (U : I → X.left.Opens)
    (hU : ∀ n, IsAffineOpen (U n))
    (hInv : ∀ n, a.smul.left ⁻¹ᵁ U n = (snd T.X X).left ⁻¹ᵁ U n)
    (s : Finset I) :
    ∃ (F : EquivariantQuasicoherent a) (m : F.sheaf ⟶ M.sheaf),
      Mono m ∧ IsLinearizedMap F.lin M.lin m ∧ IsIso (PullMap j m) ∧
      ∀ n ∈ s, ((Scheme.Modules.pullback (U n).ι).obj F.sheaf).IsFinitePresentation := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hid : IsIso (PullMap j (𝟙 M.sheaf)) :=
      (Scheme.Modules.pullback j.left).map_isIso (𝟙 M.sheaf)
    exact ⟨M, 𝟙 _, inferInstance, linearizedMap_id _, hid, by simp⟩
  | @insert n s _ ih =>
    obtain ⟨F, m, hm, hlin, hiso, hF⟩ := ih
    let := hm
    let := hiso
    have hF' : (Pull j F.sheaf).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation Y.left.ringCatSheaf).prop_of_iso
        (asIso (PullMap j m)).symm hM
    obtain ⟨D, d, hd, hdl, hdi, hD⟩ :=
      refine_on_affine_chart j hadj hT (U n) (hU n) (hInv n) F hF'
    let := hd
    let := hdi
    have hd' : IsIso (PullMap j (d ≫ m)) := by
      change IsIso ((Scheme.Modules.pullback j.left).map (d ≫ m))
      rw [(Scheme.Modules.pullback j.left).map_comp]
      exact IsIso.comp_isIso' hdi hiso
    refine ⟨D, d ≫ m, inferInstance, linearizedMap_comp hdl hlin, hd', ?_⟩
    intro o ho
    rcases Finset.mem_insert.mp ho with rfl | ho
    · exact hD
    · let R := Scheme.Modules.pullback (U o).ι
      let : IsLocallyNoetherian (U o).toScheme :=
        LocallyOfFiniteType.isLocallyNoetherian (U o).ι
      let : (R.obj F.sheaf).IsFinitePresentation := hF o ho
      let : D.sheaf.IsQuasicoherent := D.quasicoherent
      let : (R.obj D.sheaf).IsQuasicoherent := openPullback_isQuasicoherent (U o).ι D.sheaf
      let : R.PreservesHomology := FlatCohomology.flatPullbackExact (U o).ι
      let : PreservesFiniteLimits R := Functor.preservesFiniteLimits_of_preservesHomology R
      exact finitePresentation_of_mono (R.map d)

set_option backward.isDefEq.respectTransparency false in
private theorem coherent_refinement (hadj : OpenDirectImageAdjunction.{u})
    {b : ModObj T.X Y} (setting : IsExtensionSetting a b j)
    (M : EquivariantQuasicoherent a) (hM : (Pull j M.sheaf).IsFinitePresentation) :
    ∃ (F : EquivariantCoherent a) (m : F.sheaf ⟶ M.sheaf),
      Mono m ∧ IsLinearizedMap F.lin M.lin m ∧ IsIso (PullMap j m) := by
  classical
  let := setting.compact
  let I := {U : X.left.Opens // IsAffineOpen U ∧
    a.smul.left ⁻¹ᵁ U = (snd T.X X).left ⁻¹ᵁ U}
  let U : I → X.left.Opens := Subtype.val
  have hcover : (Set.univ : Set X.left) ⊆ ⋃ i, (U i : Set X.left) := by
    intro x _
    obtain ⟨V, hx, hV, hi⟩ := setting.invariantAffines x
    exact Set.mem_iUnion.mpr ⟨⟨V, hV, hi⟩, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (U i : Set X.left)) (fun i => (U i).isOpen) hcover
  obtain ⟨F, m, hm, hlin, hiso, hfin⟩ :=
    finite_presentation_on_charts j hadj setting.split M hM U (fun i => i.property.1)
      (fun i => i.property.2) s
  have hcov : ⨆ i : s, U i.val = ⊤ := by
    apply top_unique
    intro x _
    have hx := hs (Set.mem_univ x)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi', hx'⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨⟨i, hi'⟩, hx'⟩
  let : F.sheaf.IsQuasicoherent := F.quasicoherent
  have hFp := finitePresentation_of_affineOpenCover F.sheaf (fun i : s => U i.val)
    (fun i => i.val.property.1) hcov (fun i => hfin i.val i.property)
  exact ⟨⟨F.sheaf, hFp, F.lin⟩, m, hm, hlin, hiso⟩

end CoherentRefinement

set_option backward.isDefEq.respectTransparency false in
/-- Given the equivariant open adjunction, a coherent subobject of the actual
open pullback extends equivariantly inside the specified ambient sheaf. -/
theorem subobjectExtensionFromAdjunction : SubobjectExtensionFromAdjunction.{u} := by
  intro hadj k _ T X Y a b j _ setting M N e he H incl hι hlin
  let := hι
  let := setting.finiteType
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : H.sheaf.IsFinitePresentation := H.coherent
  let H' : EquivariantQuasicoherent b := ⟨H.sheaf, inferInstance, H.lin⟩
  obtain ⟨V, f, K, hqc, d, hK, hdlin, hd, _⟩ := equivariant_preimage_of_open_subobject
    hadj setting.equivariant M N H' e
      (linearized_of_pullbackLinearizationComparison setting.equivariant _ _ e he) incl hlin
  let P : EquivariantQuasicoherent a := ⟨kernel f, hqc, K⟩
  have hP : (Pull j P.sheaf).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation Y.left.ringCatSheaf).prop_of_iso d.symm H.coherent
  obtain ⟨F, m, hm, hmlin, hmiso⟩ := coherent_refinement j hadj setting P hP
  let := hm
  let := hmiso
  let D := asIso (PullMap j m) ≪≫ d
  have hD : IsLinearizedMap (pullbackLinearization setting.equivariant F.lin) H.lin D.hom :=
    linearizedMap_comp (pullbackLinearization_map setting.equivariant m hmlin) hdlin
  refine ⟨F, m ≫ kernel.ι f, D, inferInstance, linearizedMap_comp hmlin hK,
    pullbackLinearizationComparison_of_linearized setting.equivariant _ _ D hD, ?_⟩
  change (Scheme.Modules.pullback j.left).map (m ≫ kernel.ι f) ≫ e.hom =
    (PullMap j m ≫ d.hom) ≫ incl
  rw [(Scheme.Modules.pullback j.left).map_comp, Category.assoc, hd, Category.assoc]

end

end LinearAlgebraicGroups.Representation.EquivariantCoherentSubobjectExtension
