import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantPointGlobalSections
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Sheaves.Stalks

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.EquivariantPointGlobalSections

open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.CharacterDescent (Character)
open Specs.EquivariantAffineModules
open Specs.FlagCohomology (sectionsFunctor structureModule pushforwardSectionsIso)
open Specs.EquivariantPointGlobalSections
open EquivariantAffineModules (pullSection_naturality pullSection_comp
  characterFunction_one)
open private comparePull comparePull_section_smul
  pullCongr_refl pullCongr_trans
  transport_eq_evalPullIso evalPullIso evalPullIso_comp_congr
  trivial_transport_hom trivial_actOn_eq
  pullSectionAdd moduleSectionsIso pullSection_bijective_of_isIso projectionSectionExpansion
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

open private sectionsSubsingleton_bot from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {T : GroupScheme k}
variable {X Y Z : SchemeOver k}

private abbrev Pt (k : Type u) [Field k] := (𝟙_ (SchemeOver k) : SchemeOver k)

private def pointSections : (sectionsFunctor (Pt k)).obj (structureModule (Pt k).left) ≅
    ModuleCat.of k k := by
  let R := CommRingCat.of k
  let e := Scheme.ΓSpecIso R
  let M := (sectionsFunctor (Pt k)).obj (structureModule (Pt k).left)
  let f : M →ₗ[k] k :=
    { toFun := e.hom
      map_add' := e.hom.hom.map_add
      map_smul' := by
        intro r s
        let z : Γ(Spec R, ⊤) := s
        change e.hom (e.inv r * z) = r * e.hom z
        rw [map_mul]
        congr 1
        exact ConcreteCategory.congr_hom e.inv_hom_id r }
  exact (LinearEquiv.ofBijective f (ConcreteCategory.bijective_of_isIso e.hom)).toModuleIso

private def directImageSections (x : Pt k ⟶ X) {H : (Pt k).left.Modules}
    (F : X.left.Modules) (e : F ≅ (Scheme.Modules.pushforward x.left).obj H)
    (h : H ≅ structureModule (Pt k).left) : (sectionsFunctor X).obj F ≅ ModuleCat.of k k := by
  have hx : x.left ≫ X.hom = (Pt k).hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    simp
  exact (sectionsFunctor X).mapIso e ≪≫ (pushforwardSectionsIso (RingHom.id k) x.left hx).app H ≪≫
    ModuleCat.restrictScalarsId'App (RingHom.id k) rfl _ ≪≫
    (sectionsFunctor (Pt k)).mapIso h ≪≫ pointSections

private abbrev prodMap (T : GroupScheme k) (x : Y ⟶ X) : T.X ⊗ Y ⟶ T.X ⊗ X :=
  𝟙 T.X ⊗ₘ x

private theorem prodMap_snd (T : GroupScheme k) (x : Y ⟶ X) :
    prodMap T x ≫ snd T.X X = snd T.X Y ≫ x := by simp [prodMap]

private theorem prodMap_fst (T : GroupScheme k) (x : Y ⟶ X) :
    prodMap T x ≫ fst T.X X = fst T.X Y := by simp [prodMap]

private theorem prodMap_eq_lift (T : GroupScheme k) (x : Y ⟶ X) :
    lift (fst T.X Y) (snd T.X Y ≫ x) = prodMap T x := by
  apply CartesianMonoidalCategory.hom_ext <;> simp

private def comparison {U V : SchemeOver k} (F : X.left.Modules)
    {p : V ⟶ X} {j : U ⟶ V} {y : U ⟶ Y} {x : Y ⟶ X} (w : j ≫ p = y ≫ x) :
    Pull j (Pull p F) ≅ Pull y (Pull x F) :=
  comparePull F j p w ≪≫ (pullComp F y x).symm

private theorem comparison_section {U V : SchemeOver k} (F : X.left.Modules)
    {p : V ⟶ X} {j : U ⟶ V} {y : U ⟶ Y} {x : Y ⟶ X} (w : j ≫ p = y ≫ x)
    (r : Γ(V.left, ⊤)) (s : Γ(F, ⊤)) :
    (comparison F w).hom.app ⊤ (pullSection j.left (Pull p F) (r • pullSection p.left F s)) =
      j.left.appTop r • pullSection y.left (Pull x F) (pullSection x.left F s) := by
  change (pullComp F y x).inv.app ⊤
      ((comparePull F j p w).hom.app ⊤
        (pullSection j.left (Pull p F) (r • pullSection p.left F s))) = _
  rw [comparePull_section_smul, Scheme.Modules.Hom.app_smul]
  have h : pullSection (y ≫ x).left F s =
      (pullComp F y x).hom.app ⊤
        (pullSection y.left (Pull x F) (pullSection x.left F s)) :=
    (pullSection_comp y.left x.left F s).symm
  rw [h]
  exact congrArg (j.left.appTop r • ·)
    (show (pullComp F y x).inv.app ⊤ ((pullComp F y x).hom.app ⊤ _) = _ from
      congrArg (fun m => m.app ⊤ (pullSection y.left (Pull x F) (pullSection x.left F s)))
        (pullComp F y x).hom_inv_id)

/-- Pull back a section along the square and apply the pulled-back coefficient map. -/
private def evaluate {U V : SchemeOver k} {F : X.left.Modules} {H : Y.left.Modules}
    {p : V ⟶ X} {j : U ⟶ V} {y : U ⟶ Y} {x : Y ⟶ X} (w : j ≫ p = y ≫ x)
    (c : Pull x F ⟶ H) :
    Γ(Pull p F, ⊤) →+ Γ(Pull y H, ⊤) :=
  (((Scheme.Modules.pullback y.left).map c).app ⊤).hom.comp
    ((((comparison F w).hom.app ⊤).hom).comp (pullSectionAdd j.left (Pull p F)))

private theorem evaluate_section {U V : SchemeOver k} {F : X.left.Modules} {H : Y.left.Modules}
    {p : V ⟶ X} {j : U ⟶ V} {y : U ⟶ Y} {x : Y ⟶ X} (w : j ≫ p = y ≫ x)
    (c : Pull x F ⟶ H) (r : Γ(V.left, ⊤)) (s : Γ(F, ⊤)) :
    evaluate w c (r • pullSection p.left F s) =
      j.left.appTop r • pullSection y.left H (c.app ⊤ (pullSection x.left F s)) := by
  change ((Scheme.Modules.pullback y.left).map c).app ⊤
      ((comparison F w).hom.app ⊤
        (pullSection j.left (Pull p F) (r • pullSection p.left F s))) = _
  rw [comparison_section, Scheme.Modules.Hom.app_smul]
  exact congrArg (j.left.appTop r • ·)
    (pullSection_naturality y.left c (pullSection x.left F s)).symm

private def pointCounit (x : Y ⟶ X) {F : X.left.Modules} {H : Y.left.Modules}
    (e : F ≅ (Scheme.Modules.pushforward x.left).obj H) : Pull x F ⟶ H :=
  ((Scheme.Modules.pullbackPushforwardAdjunction x.left).homEquiv F H).symm e.hom

private theorem pointCounit_section (x : Y ⟶ X) {F : X.left.Modules} {H : Y.left.Modules}
    (e : F ≅ (Scheme.Modules.pushforward x.left).obj H) (s : Γ(F, ⊤)) :
    (pointCounit x e).app ⊤ (pullSection x.left F s) = e.hom.app ⊤ s := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction x.left
  have h := (A.homEquiv F H).apply_symm_apply e.hom
  rw [A.homEquiv_unit] at h
  exact congrArg (fun m => m.app ⊤ s) h

private theorem pullSection_through {A B C : SchemeOver k} (g : A ⟶ B) (f : B ⟶ C)
    (F : C.left.Modules) (s t : Γ(F, ⊤))
    (h : pullSection f.left F s = pullSection f.left F t) :
    pullSection (g ≫ f).left F s = pullSection (g ≫ f).left F t := by
  change pullSection (g.left ≫ f.left) F s = pullSection (g.left ≫ f.left) F t
  rw [← pullSection_comp, ← pullSection_comp, h]

private theorem pullSection_open_top {A B : Scheme.{u}} (o : A ⟶ B) [IsOpenImmersion o]
    (F : B.Modules) :
    ∃ E : Γ(F, o.opensRange) ≃+ Γ((Scheme.Modules.pullback o).obj F, ⊤),
      ∀ s : Γ(F, ⊤), pullSection o F s = E (F.presheaf.map o.opensRange.leTop.op s) := by
  let J := Scheme.Modules.restrictAdjunction o
  let K := Scheme.Modules.pullbackPushforwardAdjunction o
  let i := Scheme.Modules.restrictFunctorIsoPullback o
  have hr : o ''ᵁ (⊤ : A.Opens) = o.opensRange := by ext z; simp [Scheme.Hom.opensRange]
  let m : Γ(F, o.opensRange) ≅ Γ((Scheme.Modules.pullback o).obj F, ⊤) :=
    (F.presheaf.mapIso (eqToIso hr).op) ≪≫
      (F.restrictAppIso o ⊤).symm ≪≫ asIso ((i.hom.app F).app ⊤)
  refine ⟨m.addCommGroupIsoToAddEquiv, fun s => ?_⟩
  have e := J.homEquiv_leftAdjointUniq_hom_app K F
  rw [J.homEquiv_unit] at e
  have h := congrArg (fun a => a.app ⊤ s) e
  have he : (ConcreteCategory.hom ((J.unit.app F).app ⊤)) s =
      ((F.presheaf.mapIso (eqToIso hr).op)).hom
        (F.presheaf.map o.opensRange.leTop.op s) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    have hcomp : o.opensRange.leTop.op ≫ (eqToHom hr).op =
        (homOfLE (o.image_preimage_le (⊤ : B.Opens))).op := Subsingleton.elim _ _
    change F.presheaf.map (homOfLE (o.image_preimage_le (⊤ : B.Opens))).op s =
      F.presheaf.map (eqToHom hr).op (F.presheaf.map o.opensRange.leTop.op s)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hcomp]
    rfl
  change (pullSection o F s) =
    (i.hom.app F).app ⊤ (((F.presheaf.mapIso (eqToIso hr).op)).hom
      (F.presheaf.map o.opensRange.leTop.op s))
  rw [← he]
  exact h.symm

private theorem pointSubsingleton (k : Type u) [Field k] : Subsingleton (Pt k).left := by
  change Subsingleton (PrimeSpectrum k)
  exact (PrimeSpectrum.subsingleton_iff_isField_of_isReduced (R := k)).mpr (Field.toIsField k)

private theorem restrictDirectImage_surjective (x : Pt k ⟶ X)
    {F : X.left.Modules} {H : (Pt k).left.Modules}
    (e : F ≅ (Scheme.Modules.pushforward x.left).obj H) {A : SchemeOver k}
    (o : A ⟶ X) [IsOpenImmersion o.left] :
    Function.Surjective (pullSection o.left F) := by
  let U := o.left.opensRange
  obtain ⟨E, hE⟩ := pullSection_open_top o.left F
  let S := (Scheme.Modules.pushforward x.left).obj H
  have hsurj : Function.Surjective (S.presheaf.map U.leTop.op) := by
    rw [Scheme.Modules.pushforward_obj_presheaf_map]
    let _ := pointSubsingleton k
    rcases Opens.eq_bot_or_top (x.left ⁻¹ᵁ U) with hv | hv
    · have hh : Subsingleton Γ(H, x.left ⁻¹ᵁ U) := by
        rw [hv]
        exact sectionsSubsingleton_bot H
      exact fun s => ⟨0, hh.elim _ _⟩
    · have h : IsIso (H.presheaf.map ((Opens.map x.left.base).map U.leTop).op) := by
        change IsIso (H.presheaf.map (eqToHom hv).op)
        infer_instance
      exact ConcreteCategory.bijective_of_isIso _ |>.2
  intro t
  obtain ⟨s, hs⟩ := hsurj (e.hom.app U (E.symm t))
  refine ⟨e.inv.app ⊤ s, ?_⟩
  rw [hE]
  rw [← E.apply_symm_apply t] at ⊢
  refine congrArg E ?_
  have h := e.inv.mapPresheaf.naturality_apply U.leTop.op s
  change e.inv.app U (S.presheaf.map U.leTop.op s) =
    F.presheaf.map U.leTop.op (e.inv.app ⊤ s) at h
  rw [← h, hs]
  exact ConcreteCategory.congr_hom (congrArg (fun m => m.app U) e.hom_inv_id) (E.symm t)

private theorem restrictDirectImage_zero_of_disjoint (x : Pt k ⟶ X)
    {F : X.left.Modules} {H : (Pt k).left.Modules}
    (e : F ≅ (Scheme.Modules.pushforward x.left).obj H) {A : SchemeOver k} (o : A ⟶ X)
    [IsOpenImmersion o.left] (h : ¬ Set.range x.left ⊆ Set.range o.left) :
    Subsingleton Γ(Pull o F, ⊤) := by
  obtain ⟨E, _⟩ := pullSection_open_top o.left F
  let _ := pointSubsingleton k
  have hbot : x.left ⁻¹ᵁ o.left.opensRange = ⊥ := by
    rcases Opens.eq_bot_or_top (x.left ⁻¹ᵁ o.left.opensRange) with h | h
    · exact h
    · exfalso
      apply ‹¬ Set.range x.left ⊆ Set.range o.left›
      rintro _ ⟨y, rfl⟩
      change y ∈ x.left ⁻¹ᵁ o.left.opensRange
      rw [h]
      trivial
  let S := (Scheme.Modules.pushforward x.left).obj H
  have hS : Subsingleton Γ(S, o.left.opensRange) := by
    change Subsingleton Γ(H, x.left ⁻¹ᵁ o.left.opensRange)
    rw [hbot]
    exact sectionsSubsingleton_bot H
  let _ := hS
  exact ⟨fun a b => E.symm.injective ((ConcreteCategory.bijective_of_isIso
    (e.hom.app o.left.opensRange)).1 (Subsingleton.elim _ _))⟩

private theorem prodMap_pullback (T : GroupScheme k) (o : Y ⟶ X) :
    IsPullback (prodMap T o).left (snd T.X Y).left (snd T.X X).left o.left := by
  have h : IsPullback (prodMap T o) (snd T.X Y) (snd T.X X) o := by
    refine ⟨⟨prodMap_snd T o⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
    · intro c
      exact lift (c.fst ≫ fst T.X X) c.snd
    · intro c
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · simpa [Category.assoc, prodMap_snd] using c.condition.symm
    · intro c
      simp
    · intro c m h₁ h₂
      apply CartesianMonoidalCategory.hom_ext
      · simpa [Category.assoc, prodMap_fst] using congrArg (· ≫ fst T.X X) h₁
      · simpa using h₂
  exact h.map (Over.forget _)

private theorem prodMap_covers (T : GroupScheme k) (o : Y ⟶ X) (z : (T.X ⊗ X).left)
    (h : (snd T.X X).left z ∈ Set.range o.left) :
    z ∈ Set.range (prodMap T o).left := by
  let p := snd T.X X
  let b := prodMap_pullback T o
  have h' : z ∈ Set.range (pullback.fst p.left o.left) := by
    rwa [Scheme.Pullback.range_fst]
  obtain ⟨w, rfl⟩ := h'
  exact ⟨b.isoPullback.inv w, by
    rw [← Scheme.Hom.comp_apply, b.isoPullback_inv_fst]⟩

private def characterOnProduct (Y : SchemeOver k) (χ : Character T) : Γ((T.X ⊗ Y).left, ⊤) :=
  (fst T.X Y).left.appTop (characterFunction χ)

private theorem prodMap_character (o : Y ⟶ X) (χ : Character T) :
    (prodMap T o).left.appTop (characterOnProduct X χ) = characterOnProduct Y χ := by
  change _ = (fst T.X Y).left.appTop (characterFunction χ)
  have h := congrArg (fun f => f.left.appTop (characterFunction χ)) (prodMap_fst T o)
  change ((prodMap T o).left ≫ (fst T.X X).left).appTop _ = _ at h
  rw [Scheme.Hom.comp_appTop] at h
  exact h

private def polynomials (Y : SchemeOver k) (H : Y.left.Modules) :
    (Character T →₀ Γ(H, ⊤)) →+ Γ(Pull (snd T.X Y) H, ⊤) :=
  Finsupp.liftAddHom (fun χ =>
    (DistribSMul.toAddMonoidHom _ (characterOnProduct Y χ)).comp (pullSectionAdd (snd T.X Y).left H))

private theorem polynomials_single (Y : SchemeOver k) (H : Y.left.Modules) (χ : Character T)
    (s : Γ(H, ⊤)) :
    polynomials Y H (Finsupp.single χ s) =
      characterOnProduct Y χ • pullSection (snd T.X Y).left H s :=
  Finsupp.liftAddHom_apply_single _ _ _

private def restrictProduct (T : GroupScheme k) (o : Y ⟶ X) (F : X.left.Modules) :
    Γ(Pull (snd T.X X) F, ⊤) →+ Γ(Pull (snd T.X Y) (Pull o F), ⊤) :=
  ((comparison F (prodMap_snd T o)).hom.app ⊤).hom.comp
    (pullSectionAdd (prodMap T o).left (Pull (snd T.X X) F))

private theorem restrictProduct_poly (o : Y ⟶ X) (F : X.left.Modules) :
    (restrictProduct T o F).comp (polynomials X F) =
      (polynomials Y (Pull o F)).comp (Finsupp.mapRange.addMonoidHom (pullSectionAdd o.left F)) := by
  apply Finsupp.addHom_ext
  intro χ s
  simp only [AddMonoidHom.comp_apply, polynomials_single, Finsupp.mapRange.addMonoidHom_apply,
    Finsupp.mapRange_single]
  change (comparison F (prodMap_snd T o)).hom.app ⊤
    (pullSection (prodMap T o).left (Pull (snd T.X X) F)
      (characterOnProduct X χ • pullSection (snd T.X X).left F s)) = _
  rw [comparison_section, prodMap_character]
  rfl

private theorem evaluate_poly (x : Y ⟶ X) {F : X.left.Modules} {H : Y.left.Modules}
    (e : F ≅ (Scheme.Modules.pushforward x.left).obj H) :
    (evaluate (prodMap_snd T x) (pointCounit x e)).comp (polynomials X F) =
      (polynomials Y H).comp (Finsupp.mapRange.addMonoidHom (e.hom.app ⊤).hom) := by
  apply Finsupp.addHom_ext
  intro χ s
  simp only [AddMonoidHom.comp_apply, polynomials_single, Finsupp.mapRange.addMonoidHom_apply,
    Finsupp.mapRange_single]
  rw [evaluate_section, prodMap_character, pointCounit_section]
  rfl

set_option maxHeartbeats 500000 in
private theorem affine_polynomials (hT : IsSplitTorus T) (R : TestAlgebra k)
    (F : (affineScheme R).left.Modules) [F.IsQuasicoherent] :
    Function.Bijective (polynomials (T := T) (affineScheme R) F) := by
  obtain ⟨E, hE⟩ := projectionSectionExpansion hT R F
  have h : (E : Γ(Pull (snd T.X (affineScheme R)) F, ⊤) →+
      (Character T →₀ Γ(F, ⊤))).comp (polynomials (affineScheme R) F) = AddMonoidHom.id _ := by
    apply Finsupp.addHom_ext
    intro χ s
    exact (congrArg E (polynomials_single (affineScheme R) F χ s)).trans (hE χ s)
  have hg (f : Character T →₀ Γ(F, ⊤)) : E (polynomials (affineScheme R) F f) = f :=
    DFunLike.congr_fun h f
  exact ⟨fun a b hab => (hg a).symm.trans ((congrArg E hab).trans (hg b)),
    fun s => ⟨E s, E.injective (hg (E s))⟩⟩

private theorem point_polynomials (hT : IsSplitTorus T) (H : (Pt k).left.Modules)
    [H.IsQuasicoherent] : Function.Bijective (polynomials (T := T) (Pt k) H) := by
  have hPt : IsAffine (Pt k).left := by change IsAffine (Spec (CommRingCat.of k)); infer_instance
  obtain ⟨S, ⟨j⟩⟩ := (essImage_algSpec (R := CommRingCat.of k) (G := Pt k)).mpr hPt
  let R : TestAlgebra k := S.unop
  let o : affineScheme R ⟶ Pt k := j.hom
  have ho : IsIso o := inferInstanceAs (IsIso j.hom)
  let v := prodMap T o
  have hv : IsIso v := inferInstanceAs (IsIso ((Iso.refl T.X ⊗ᵢ j).hom))
  have hol : IsIso o.left := Functor.map_isIso (Over.forget _) o
  have hvl : IsIso v.left := Functor.map_isIso (Over.forget _) v
  let H' := Pull o H
  let _ : H'.IsQuasicoherent := (SheafOfModules.isQuasicoherent (affineScheme R).left.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback o.left).app H) (Scheme.Modules.isQuasicoherent_restrictFunctor o.left H)
  have hr : Function.Bijective (restrictProduct T o H) :=
    (moduleSectionsIso (comparison H (prodMap_snd T o))).bijective.comp
      (pullSection_bijective_of_isIso v.left _)
  have hc :=
    Finsupp.mapRange_bijective (α := Character T) (pullSectionAdd o.left H) (map_zero _)
      (pullSection_bijective_of_isIso o.left H)
  have h := restrictProduct_poly (T := T) o H
  have hb : Function.Bijective ((restrictProduct T o H) ∘ (polynomials (Pt k) H)) := by
    change Function.Bijective ⇑((restrictProduct T o H).comp (polynomials (Pt k) H))
    rw [h]
    exact (affine_polynomials hT R H').comp hc
  exact hb.of_comp_left hr.1

private theorem restrictProduct_zero (hT : IsSplitTorus T) (x : Pt k ⟶ X)
    {F : X.left.Modules} [F.IsQuasicoherent] {H : (Pt k).left.Modules} [H.IsQuasicoherent]
    (e : F ≅ (Scheme.Modules.pushforward x.left).obj H) (R : TestAlgebra k)
    (o : affineScheme R ⟶ X) [IsOpenImmersion o.left]
    (d : Γ(Pull (snd T.X X) F, ⊤))
    (hd : evaluate (prodMap_snd T x) (pointCounit x e) d = 0) :
    restrictProduct T o F d = 0 := by
  classical
  let _ : (Pull o F).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (affineScheme R).left.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback o.left).app F)
      (Scheme.Modules.isQuasicoherent_restrictFunctor o.left F)
  obtain ⟨b, hb⟩ := (affine_polynomials hT R (Pull o F)).2 (restrictProduct T o F d)
  by_cases hx : Set.range x.left ⊆ Set.range o.left
  · let l : Pt k ⟶ affineScheme R := Over.homMk (IsOpenImmersion.lift o.left x.left hx) (by
      rw [← Over.w o, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w x])
    have hlo : l ≫ o = x := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    let r := pullSectionAdd o.left F
    obtain ⟨f, hf⟩ := Finsupp.mapRange_surjective r (map_zero r)
      (restrictDirectImage_surjective x e o) b
    have he : restrictProduct T o F (polynomials X F f) = restrictProduct T o F d := by
      have h := DFunLike.congr_fun (restrictProduct_poly o F) f
      change restrictProduct T o F (polynomials X F f) =
        polynomials (affineScheme R) (Pull o F) (Finsupp.mapRange r (map_zero r) f) at h
      exact h.trans ((congrArg _ hf).trans hb)
    have hprod : prodMap T l ≫ prodMap T o = prodMap T x := by
      change (𝟙 T.X ⊗ₘ l) ≫ (𝟙 T.X ⊗ₘ o) = (𝟙 T.X ⊗ₘ x)
      rw [tensorHom_comp_tensorHom, Category.id_comp, hlo]
    have hu : pullSection (prodMap T o).left (Pull (snd T.X X) F) (polynomials X F f) =
        pullSection (prodMap T o).left (Pull (snd T.X X) F) d := by
      exact ((moduleSectionsIso (comparison F (prodMap_snd T o))).injective he)
    have hj := pullSection_through (prodMap T l) (prodMap T o) (Pull (snd T.X X) F)
      (polynomials X F f) d hu
    rw [hprod] at hj
    have ev : evaluate (prodMap_snd T x) (pointCounit x e) (polynomials X F f) = 0 :=
      (congrArg (fun z => ((Scheme.Modules.pullback (snd T.X (Pt k)).left).map
        (pointCounit x e)).app ⊤ ((comparison F (prodMap_snd T x)).hom.app ⊤ z)) hj).trans hd
    have ev' := (DFunLike.congr_fun (evaluate_poly (T := T) x e) f).symm.trans ev
    change polynomials (Pt k) H (Finsupp.mapRange.addMonoidHom (e.hom.app ⊤).hom f) = 0 at ev'
    have f0 : f = 0 := by
      apply Finsupp.mapRange_injective (e.hom.app ⊤).hom (map_zero _)
        (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).1
      apply (point_polynomials hT H).1
      rw [Finsupp.mapRange_zero, map_zero]
      exact ev'
    rw [f0, map_zero, map_zero] at he
    exact he.symm
  · let _ := restrictDirectImage_zero_of_disjoint x e o hx
    have hb0 : b = 0 := by ext χ; exact Subsingleton.elim _ _
    simpa only [hb0, map_zero] using hb.symm

/-- A section of the projection pullback is detected by its image under
the adjunction counit on the product of the torus with the point. -/
private theorem evaluate_injective (hT : IsSplitTorus T) (x : Pt k ⟶ X)
    {F : X.left.Modules} [F.IsQuasicoherent] {H : (Pt k).left.Modules} [H.IsQuasicoherent]
    (e : F ≅ (Scheme.Modules.pushforward x.left).obj H) :
    Function.Injective (evaluate (prodMap_snd T x) (pointCounit x e)) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro d hd
  let M := Pull (snd T.X X) F
  let G := (SheafOfModules.toSheaf (T.X ⊗ X).left.ringCatSheaf).obj M
  refine TopCat.Presheaf.section_ext G ⊤ d 0 (fun z hz => ?_)
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, _⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show (snd T.X X).left z ∈ (Set.univ : Set X.left) from Set.mem_univ _) isOpen_univ
  let U₀ : X.left.Opens := U
  let Y : SchemeOver k := Over.mk (U₀.ι ≫ X.hom)
  let u : Y ⟶ X := Over.homMk U₀.ι rfl
  have aff : IsAffine Y.left := hU
  obtain ⟨S, ⟨j⟩⟩ := (essImage_algSpec (R := CommRingCat.of k) (G := Y)).mpr aff
  let R : TestAlgebra k := S.unop
  let o : affineScheme R ⟶ X := j.hom ≫ u
  let _ : IsOpenImmersion o.left := by
    change IsOpenImmersion (j.hom.left ≫ U₀.ι)
    have : IsIso j.hom.left := inferInstanceAs (IsIso ((Over.forget _).map j.hom))
    infer_instance
  have hyo : (snd T.X X).left z ∈ Set.range o.left := by
    obtain ⟨v, hv⟩ := (Scheme.homeoOfIso ((Over.forget _).mapIso j)).surjective ⟨_, hy⟩
    exact ⟨v, congrArg U₀.ι hv⟩
  let v := prodMap T o
  let _ : IsOpenImmersion v.left :=
    MorphismProperty.of_isPullback (prodMap_pullback T o).flip inferInstance
  have hzo : z ∈ v.left.opensRange := prodMap_covers T o z hyo
  have h₀ := restrictProduct_zero hT x e R o d hd
  have h₁ : pullSection v.left M d = 0 :=
    (moduleSectionsIso (comparison F (prodMap_snd T o))).injective (h₀.trans (map_zero _).symm)
  obtain ⟨E, hE⟩ := pullSection_open_top v.left M
  have hr : M.presheaf.map v.left.opensRange.leTop.op d = 0 := by
    apply E.injective
    rw [← hE, h₁, map_zero]
  change M.presheaf.germ ⊤ z hz d = M.presheaf.germ ⊤ z hz 0
  rw [← M.presheaf.germ_res_apply v.left.opensRange.leTop z hzo, hr, map_zero, map_zero]

private theorem changeCounitTarget {F : X.left.Modules} {H : Y.left.Modules}
    {x : Y ⟶ X} {r : Z ⟶ X} {y' y : Z ⟶ Y}
    (h : r = y' ≫ x) (hy : y' = y) (c : Pull x F ⟶ H) :
    (pullCongr F h).hom ≫ (pullComp F y' x).inv ≫
        (Scheme.Modules.pullback y'.left).map c ≫ (pullCongr H hy).hom =
      (pullCongr F (h.trans (congrArg (· ≫ x) hy))).hom ≫ (pullComp F y x).inv ≫
        (Scheme.Modules.pullback y.left).map c := by
  subst y'
  simp only [pullCongr_refl, Category.comp_id]

private theorem evalPullIso_congr_map {F : X.left.Modules} {f g : Y ⟶ X}
    (θ : Pull f F ≅ Pull g F) {l l' : Z ⟶ Y} (h : l = l')
    {r s : Z ⟶ X} (hr : l ≫ f = r) (hs : l ≫ g = s)
    (hr' : l' ≫ f = r) (hs' : l' ≫ g = s) :
    evalPullIso θ l hr hs = evalPullIso θ l' hr' hs' := by subst l'; rfl

private theorem comparison_commutes {S V : SchemeOver k} {F : X.left.Modules}
    {p a : V ⟶ X} (θ : Pull p F ≅ Pull a F) {j : S ⟶ V} {q : S ⟶ Y} {x : Y ⟶ X}
    (wp : j ≫ p = q ≫ x) (wa : j ≫ a = q ≫ x)
    {M : S.left.Modules} (c : Pull q (Pull x F) ⟶ M)
    (h : (pullComp F q x).hom ≫ (evalPullIso θ j wp wa).hom ≫
      (pullComp F q x).inv ≫ c = c) :
    (comparison F wp).hom ≫ c =
      (Scheme.Modules.pullback j.left).map θ.hom ≫ (comparison F wa).hom ≫ c := by
  let A := comparePull F j p wp
  let B := comparePull F j a wa
  let C := pullComp F q x
  let m := (Scheme.Modules.pullback j.left).map θ.hom
  change C.hom ≫ (A.inv ≫ m ≫ B.hom) ≫ C.inv ≫ c = c at h
  have h' := congrArg (fun f : Pull q (Pull x F) ⟶ M => A.hom ≫ C.inv ≫ f) h
  change (A.hom ≫ C.inv) ≫ c = m ≫ (B.hom ≫ C.inv) ≫ c
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc] using h'.symm

set_option maxHeartbeats 1000000 in
/-- Test the equivariant counit at the two projections from the product
of the torus with the fixed point. -/
private theorem universalCounit_commutes {a : ModObj T.X X} (x : Pt k ⟶ X)
    (H : EquivariantCoherent (ModObj.trivialAction T.X (Pt k)))
    (F : EquivariantCoherent a)
    (e : F.sheaf ≅ (Scheme.Modules.pushforward x.left).obj H.sheaf)
    (hH : H.lin.iso.hom = (pullCongr H.sheaf
      (rfl : snd T.X (Pt k) = (ModObj.trivialAction T.X (Pt k)).smul)).hom)
    (hF : IsEquivariantPushforward x H F e) :
    ∃ w : prodMap T x ≫ a.smul = snd T.X (Pt k) ≫ x,
      let c := (Scheme.Modules.pullback (snd T.X (Pt k)).left).map (pointCounit x e)
      (comparison F.sheaf (prodMap_snd T x)).hom ≫ c =
        (Scheme.Modules.pullback (prodMap T x).left).map F.lin.iso.hom ≫
          (comparison F.sheaf w).hom ≫ c := by
  let Y := Pt k
  let S := T.X ⊗ Y
  let b := ModObj.trivialAction T.X Y
  let q := snd T.X Y
  let t := fst T.X Y
  let j := prodMap T x
  let c := pointCounit x e
  let θ := F.lin.iso
  have hj : lift t (q ≫ x) = j := prodMap_eq_lift T x
  have hy : actOn b t q = q := trivial_actOn_eq
  obtain ⟨hf, hc⟩ := hF S t q
  let hfix : actOn a t (q ≫ x) = q ≫ x := hf.trans (congrArg (· ≫ x) hy)
  let w : j ≫ a.smul = q ≫ x := (congrArg (· ≫ a.smul) hj).symm.trans hfix
  refine ⟨w, ?_⟩
  have hθ : H.lin.iso = Iso.refl (Pull q H.sheaf) := Iso.ext hH
  have htriv : (transport b H.lin.iso t q).hom ≫ (pullCongr H.sheaf hy).hom = 𝟙 _ := by
    rw [hθ, trivial_transport_hom, pullCongr_trans, pullCongr_refl]
  let Q := Scheme.Modules.pullback q.left
  have hcomp := congrArg (· ≫ (pullCongr H.sheaf hy).hom) hc
  change ((pullComp F.sheaf q x).hom ≫ (transport a θ t (q ≫ x)).hom ≫
      (pullCongr F.sheaf hf).hom ≫ (pullComp F.sheaf (actOn b t q) x).inv ≫
      (Scheme.Modules.pullback (actOn b t q).left).map c) ≫ _ =
    (Q.map c ≫ (transport b H.lin.iso t q).hom) ≫ _ at hcomp
  simp only [Category.assoc, htriv, changeCounitTarget] at hcomp
  have hte : (transport a θ t (q ≫ x)).hom ≫ (pullCongr F.sheaf hfix).hom =
      (evalPullIso θ j (prodMap_snd T x) w).hom := by
    rw [transport_eq_evalPullIso, evalPullIso_comp_congr]
    exact congrArg Iso.hom (evalPullIso_congr_map θ hj _ _ _ _)
  have hcomp' : (pullComp F.sheaf q x).hom ≫ (evalPullIso θ j (prodMap_snd T x) w).hom ≫
      (pullComp F.sheaf q x).inv ≫ Q.map c = Q.map c := by
    rw [← hte, Category.assoc]
    exact hcomp
  exact comparison_commutes θ (prodMap_snd T x) w (Q.map c) hcomp'

private theorem evaluate_of_commutes {S V : SchemeOver k} {F : X.left.Modules}
    {H : Y.left.Modules} {p a : V ⟶ X} (θ : Pull p F ≅ Pull a F)
    {j : S ⟶ V} {q : S ⟶ Y} {x : Y ⟶ X}
    (wp : j ≫ p = q ≫ x) (wa : j ≫ a = q ≫ x) (c : Pull x F ⟶ H)
    (h : let C := (Scheme.Modules.pullback q.left).map c
      (comparison F wp).hom ≫ C =
        (Scheme.Modules.pullback j.left).map θ.hom ≫ (comparison F wa).hom ≫ C)
    (d : Γ(Pull p F, ⊤)) :
    evaluate wp c d = evaluate wa c (θ.hom.app ⊤ d) := by
  have hd := congrArg (fun m => m.app ⊤ (pullSection j.left (Pull p F) d)) h
  have hn := pullSection_naturality j.left θ.hom d
  change pullSection j.left (Pull a F) (θ.hom.app ⊤ d) =
    ((Scheme.Modules.pullback j.left).map θ.hom).app ⊤ (pullSection j.left (Pull p F) d) at hn
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, ← hn] at hd
  exact hd

private theorem prodCharacter_one (hT : IsSplitTorus T) (Y : SchemeOver k) :
    characterOnProduct Y (1 : Character T) = 1 := by
  simp only [characterOnProduct, characterFunction_one hT, map_one]

private theorem injective_of_agrees_with_equiv {A B C : Type*}
    (I : A ≃ B) {E : A → C} (hE : Function.Injective E) {D : B → C}
    (h : ∀ v, E v = D (I v)) : Function.Injective D := by
  intro v w hvw
  apply I.symm.injective
  apply hE
  simpa only [h, Equiv.apply_symm_apply] using hvw

set_option maxHeartbeats 500000 in
/-- The actual global sections of a trivial rational point direct image form
the one-dimensional trivial representation of the split torus. -/
theorem pointGlobalSections : PointGlobalSections.{u} := by
  intro k _ T hT X a x _ H hLine F e hH hF
  let _ : F.sheaf.IsQuasicoherent := F.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let _ : H.sheaf.IsQuasicoherent := H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  obtain ⟨w, commutes⟩ := universalCounit_commutes x H F e hH hF
  let p := snd T.X X
  let c := pointCounit x e
  have hw := evaluate_of_commutes F.lin.iso (prodMap_snd T x) w c commutes
  let E := evaluate (prodMap_snd T x) c
  let D := evaluate w c
  let I := moduleSectionsIso F.lin.iso
  have hinj : Function.Injective D :=
    injective_of_agrees_with_equiv I.toEquiv (evaluate_injective hT x e) hw
  have hmap (s : Γ(F.sheaf, ⊤)) (χ : Character T) :
      D (characterOnProduct X χ • pullSection a.smul.left F.sheaf s) =
        polynomials (Pt k) H.sheaf (Finsupp.single χ (e.hom.app ⊤ s)) := by
    rw [polynomials_single, evaluate_section, pointCounit_section, prodMap_character]
  have hmapP (s : Γ(F.sheaf, ⊤)) :
      E (pullSection p.left F.sheaf s) =
        polynomials (Pt k) H.sheaf (Finsupp.single (1 : Character T) (e.hom.app ⊤ s)) := by
    rw [polynomials_single, prodCharacter_one hT]
    have h := evaluate_section (prodMap_snd T x) c 1 s
    simpa only [map_one, one_smul, pointCounit_section, c] using h
  have ht (s : Γ(F.sheaf, ⊤)) : HasSectionWeight F.lin s 1 := by
    change I (pullSection p.left F.sheaf s) =
      characterOnProduct X (1 : Character T) • pullSection a.smul.left F.sheaf s
    exact hinj ((hw (pullSection p.left F.sheaf s)).symm.trans
      ((hmapP s).trans (hmap s 1).symm))

  refine ⟨⟨directImageSections x F.sheaf e hLine⟩, ?_⟩
  intro s χ
  constructor
  · intro hs
    have h := hw (pullSection p.left F.sheaf s)
    change E (pullSection p.left F.sheaf s) = D (I (pullSection p.left F.sheaf s)) at h
    change I (pullSection p.left F.sheaf s) =
      characterOnProduct X χ • pullSection a.smul.left F.sheaf s at hs
    rw [hs, hmapP, hmap] at h
    have heq := (point_polynomials hT H.sheaf).1 h
    by_cases hχ : χ = 1
    · exact Or.inl hχ
    · right
      have hzero := congrArg (fun f : Character T →₀ Γ(H.sheaf, ⊤) => f 1) heq
      rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm hχ)] at hzero
      exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).1 (hzero.trans (map_zero _).symm)
  · rintro (rfl | rfl)
    · exact ht s
    · unfold HasSectionWeight
      change I (pullSectionAdd p.left F.sheaf 0) =
        characterOnProduct X χ • pullSectionAdd a.smul.left F.sheaf 0
      rw [map_zero, map_zero, map_zero, smul_zero]

end

end LinearAlgebraicGroups.Representation.EquivariantPointGlobalSections
