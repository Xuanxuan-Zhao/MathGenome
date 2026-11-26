import Specs.LinearAlgebraicGroups.Representation.EquivariantCoherentOpenExtension
import LinearAlgebraicGroups.Representation.EquivariantAffineModules
import LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness
import LinearAlgebraicGroups.Representation.EquivariantCoherentSubobjectExtension
import LinearAlgebraicGroups.Representation.EquivariantOpenFlatBaseChange
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.EquivariantCoherentOpenExtension

open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.EquivariantAffineModules
open Specs.EquivariantCoherentOpenExtension
open EquivariantAffineModules
open Specs.EquivariantCoherentSubobjectExtension (OpenDirectImageAdjunction)
open Specs.EquivariantOpenFlatBaseChange (FlatOpenBaseChange openBaseChange)
open EquivariantOpenFlatBaseChange (flatOpenBaseChange)
open EquivariantCoherentSubobjectExtension
  (openPullback_finitePresentation pullbackLinearization_map
    pullbackLinearizationComparison_of_linearized linearized_of_pullbackLinearizationComparison
    openPushforward_isQuasicoherent kernel_isQuasicoherent finitePresentation_of_mono
    cokernelLinearization kernelLinearization subobjectExtensionFromAdjunction)

open private comparePull_naturality comparePull_inv_naturality_assoc pullComp_naturality
  pullComp_inv_naturality linearizedMap_comp finitePresentation_of_affineSections
  quasicoherent_of_affineRestrictions quasicoherent_restrict_of_fromSpec
  projectionPull actionPull PullMap TransportHom transportSquare pullCongrSquare
  cancelUnitEpi cancelUnitMono cancelCompositionMono actOn_comp
  transportReindexSquare pullCongrReindexSquare triple tripleFirst tripleSecond tripleBase
  linearizationUnit_of_universal linearizationMul_of_universal projectionFlat actionShear
  actionFlat tensor_snd_isPullback tripleActionFlat linearizationOfMono
  from LinearAlgebraicGroups.Representation.EquivariantCoherentSubobjectExtension

open SheafOfModules Scheme.Modules

noncomputable section
section LinearizedRestriction

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {c : ModObj T.X Y}

open private equivariant_actOn from LinearAlgebraicGroups.Representation.EquivariantAffineModules

/-- Open restriction of an equivariant coherent sheaf via actual inverse image. -/
def restrictCoherent (j : Y ⟶ X) [IsOpenImmersion j.left]
    (hj : IsEquivariantMap a c j) (F : EquivariantCoherent a) : EquivariantCoherent c :=
  ⟨Pull j F.sheaf, openPullback_finitePresentation j.left F.sheaf F.coherent,
    pullbackLinearization hj F.lin⟩

theorem restrictCoherent_isEquivariantPullback (j : Y ⟶ X) [IsOpenImmersion j.left]
    (hj : IsEquivariantMap a c j) (F : EquivariantCoherent a) :
    IsEquivariantPullback j F (restrictCoherent j hj F) (Iso.refl _) := by
  intro S t y
  refine ⟨equivariant_actOn hj, ?_⟩
  change (Scheme.Modules.pullback y.left).map (𝟙 (Pull j F.sheaf)) ≫
    (pullComp F.sheaf y j).hom ≫ (transport a F.lin.iso t (y ≫ j)).hom ≫ _ ≫ _ ≫
    (Scheme.Modules.pullback (actOn c t y).left).map (𝟙 (Pull j F.sheaf)) =
      (transport c (pullbackLinearizationIso hj F.lin.iso) t y).hom
  rw [(Scheme.Modules.pullback y.left).map_id, Category.id_comp,
    (Scheme.Modules.pullback (actOn c t y).left).map_id, Category.comp_id]
  apply (cancel_mono (pullComp F.sheaf (actOn c t y) j).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (pullbackLinearization_transport hj F.lin.iso t y).symm
end LinearizedRestriction

theorem openPullback_shortExact {V U : Scheme.{u}} (f : V ⟶ U) [IsOpenImmersion f]
    (S : ShortComplex U.Modules) (hS : S.ShortExact) :
    (S.map (Scheme.Modules.pullback f)).ShortExact := by
  let P := Scheme.Modules.pullback f
  have : P.PreservesHomology := FlatCohomology.flatPullbackExact f
  have : PreservesFiniteLimits P := Functor.preservesFiniteLimits_of_preservesHomology P
  exact hS.map_of_exact P

section Coherence

open LinearAlgebraicGroups.ProjectiveFiniteness (finite_sections_of_isAffineOpen)
open private fromSpecSectionTopIso from LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness
set_option backward.isDefEq.respectTransparency false in
private theorem cokernel_spec_finite {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj N)] (f : M ⟶ N) :
    (cokernel f).IsQuasicoherent ∧
      Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (cokernel f)) := by
  let G := moduleSpecΓFunctor (R := R)
  let P := tilde.functor R
  let a := asIso M.fromTildeΓ
  let b := asIso N.fromTildeΓ
  have he : P.map (G.map f) ≫ b.hom = a.hom ≫ f := fromTildeΓNatTrans.naturality f
  let e : tilde (cokernel (G.map f)) ≅ cokernel f :=
    PreservesCokernel.iso P (G.map f) ≪≫ cokernel.mapIso _ _ a b he
  constructor
  · exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e inferInstance
  · let C : ModuleCat R := cokernel (G.map f)
    let : Module.Finite R C :=
      Module.Finite.of_surjective (cokernel.π (G.map f)).hom (ModuleCat.epi_iff_surjective _ |>.mp
        inferInstance)
    exact Module.Finite.equiv ((tilde.isoTop C) ≪≫ G.mapIso e).toLinearEquiv

set_option maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
/-- The cokernel of a map of coherent module sheaves is coherent on a locally
Noetherian scheme. -/
theorem cokernel_finitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N) :
    (cokernel f).IsFinitePresentation := by
  let C := cokernel f
  apply finitePresentation_of_affineSections C
  intro U
  let G := restrictFunctor U.property.fromSpec
  let A := G.obj C
  let R := Γ(X, U.val)
  let E := restrictFunctor U.property.isoSpec.hom
  let : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (G.obj N)) :=
    let : Module.Finite R Γ(N, U.val) := finite_sections_of_isAffineOpen N U.property
    Module.Finite.equiv (fromSpecSectionTopIso U.property N).symm
  obtain ⟨hQC, hFin⟩ := cokernel_spec_finite (G.map f)
  let d := PreservesCokernel.iso G f
  have hA : A.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso d.symm hQC
  let : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (cokernel (G.map f))) := hFin
  let hAM : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (C.restrict U.property.fromSpec)) :=
    Module.Finite.equiv ((moduleSpecΓFunctor (R := R)).mapIso d.symm).toLinearEquiv
  let e : E.obj A ≅ C.restrict U.val.ι :=
    ((restrictFunctorComp U.property.isoSpec.hom U.property.fromSpec).app C).symm ≪≫
      (restrictFunctorCongr U.property.isoSpec_hom_fromSpec).app C
  exact ⟨(SheafOfModules.isQuasicoherent U.val.toScheme.ringCatSheaf).prop_of_iso e
      (Scheme.Modules.isQuasicoherent_restrictFunctor U.property.isoSpec.hom A),
    @Module.Finite.equiv R _ _ _ _ _ _ _ hAM (fromSpecSectionTopIso U.property C)⟩

end Coherence

section ExactLifting

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y}

private theorem linearizedMap_of_epi_comp {F H K : X.left.Modules}
    {L : Linearization a F} {J : Linearization a H} {N : Linearization a K}
    {f : F ⟶ H} {g : H ⟶ K} [Epi f]
    (hf : IsLinearizedMap L J f) (hg : IsLinearizedMap L N (f ≫ g)) :
    IsLinearizedMap J N g := by
  let P := Scheme.Modules.pullback (snd T.X X).left
  let A := Scheme.Modules.pullback a.smul.left
  change L.iso.hom ≫ A.map f = P.map f ≫ J.iso.hom at hf
  change L.iso.hom ≫ A.map (f ≫ g) = P.map (f ≫ g) ≫ N.iso.hom at hg
  change J.iso.hom ≫ A.map g = P.map g ≫ N.iso.hom
  apply (cancel_epi (P.map f)).mp
  rw [← Category.assoc, ← hf, Category.assoc, ← A.map_comp, hg, P.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem open_cokernel_comparison (j : Y ⟶ X)
    {F₁ F₂ : EquivariantCoherent a} {H₁ H₂ H₃ : EquivariantCoherent b}
    {i : F₁.sheaf ⟶ F₂.sheaf} (f : H₁.sheaf ⟶ H₂.sheaf) (g : H₂.sheaf ⟶ H₃.sheaf)
    (w : f ≫ g = 0) (h : (ShortComplex.mk f g w).ShortExact)
    (e₁ : Pull j F₁.sheaf ≅ H₁.sheaf) (e₂ : Pull j F₂.sheaf ≅ H₂.sheaf)
    (hi : (Scheme.Modules.pullback j.left).map i ≫ e₂.hom = e₁.hom ≫ f) :
    ∃ e₃ : Pull j (cokernel i) ≅ H₃.sheaf,
      (Scheme.Modules.pullback j.left).map (cokernel.π i) ≫ e₃.hom = e₂.hom ≫ g := by
  let W := Scheme.Modules.pullback j.left
  let d := cokernel.mapIso (W.map i) f e₁ e₂ hi
  let c := (cokernelIsCokernel f).coconePointUniqueUpToIso h.gIsCokernel
  refine ⟨PreservesCokernel.iso W i ≪≫ d ≪≫ c, ?_⟩
  have hd : cokernel.π (W.map i) ≫ d.hom = e₂.hom ≫ cokernel.π f := cokernel.π_desc _ _ _
  have hc : cokernel.π f ≫ c.hom = g :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel f) h.gIsCokernel
      WalkingParallelPair.one
  change W.map (cokernel.π i) ≫ (PreservesCokernel.iso W i).hom ≫ d.hom ≫ c.hom = _
  rw [PreservesCokernel.π_iso_hom_assoc, reassoc_of% hd, hc]

set_option backward.isDefEq.respectTransparency false in
/-- Once objects and coherent subobjects extend, the exact lift is obtained by
taking the equivariant cokernel of the lifted inclusion. -/
theorem shortExactExtension_of_extensions (hext : CoherentExtension.{u})
    (hsub : SubobjectExtension.{u})
    (hcoker : ∀ {k : Type u} [Field k] {T : GroupScheme k} {X : SchemeOver k}
      {a : ModObj T.X X} [IsLocallyNoetherian X.left] {F G : EquivariantCoherent a}
      (f : F.sheaf ⟶ G.sheaf), EquivariantHom f →
        ∃ L : Linearization a (cokernel f),
          IsLinearizedMap G.lin L (cokernel.π f)) : ShortExactExtension.{u} := by
  intro k _ T X Y a b j _ setting H₁ H₂ H₃ f g w hf hg hE
  obtain ⟨F₂, e₂, he₂⟩ := hext j setting H₂
  let : F₂.sheaf.IsFinitePresentation := F₂.coherent
  let : F₂.sheaf.IsQuasicoherent := F₂.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let : H₂.sheaf.IsQuasicoherent := H₂.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let M : EquivariantQuasicoherent a := ⟨F₂.sheaf, inferInstance, F₂.lin⟩
  let N : EquivariantQuasicoherent b := ⟨H₂.sheaf, inferInstance, H₂.lin⟩
  obtain ⟨F₁, i, e₁, mi, lin_i, he₁, hi⟩ :=
    hsub j setting M N e₂ he₂ H₁ f hE.mono_f hf
  let : IsLocallyNoetherian X.left := by
    let : LocallyOfFiniteType X.hom := setting.finiteType
    exact LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : F₁.sheaf.IsFinitePresentation := F₁.coherent
  let : Mono i := mi
  obtain ⟨L, hL⟩ := hcoker i lin_i
  let F₃ : EquivariantCoherent a := ⟨cokernel i, cokernel_finitePresentation i, L⟩
  have lin_p : EquivariantHom (F := F₂) (H := F₃) (cokernel.π i) := hL
  obtain ⟨e₃, he₃⟩ := open_cokernel_comparison j f g w hE e₁ e₂ hi
  let W := Scheme.Modules.pullback j.left
  have h₂ := linearized_of_pullbackLinearizationComparison setting.equivariant F₂.lin H₂.lin e₂ he₂
  have hp := pullbackLinearization_map setting.equivariant (cokernel.π i) lin_p
  have h₃ : IsLinearizedMap (pullbackLinearization setting.equivariant F₃.lin) H₃.lin e₃.hom := by
    apply linearizedMap_of_epi_comp (f := W.map (cokernel.π i)) hp
    rw [he₃]
    exact linearizedMap_comp h₂ hg
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := ⟨S.exact_of_g_is_cokernel (cokernelIsCokernel i)⟩
  exact ⟨F₁, F₂, F₃, i, cokernel.π i, cokernel.condition i, e₁, e₂, e₃,
    lin_i, lin_p, hS, he₁, he₂,
    pullbackLinearizationComparison_of_linearized setting.equivariant F₃.lin H₃.lin e₃ h₃,
    hi, he₃⟩

end ExactLifting

section ExtensionOfObjects

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y}

/-- The counit for the actual inverse image and direct image of an open
immersion is an isomorphism. -/
def openCounitIso (j : Y ⟶ X) [IsOpenImmersion j.left] (H : Y.left.Modules) :
    Pull j ((Scheme.Modules.pushforward j.left).obj H) ≅ H :=
  asIso ((Scheme.Modules.pullbackPushforwardAdjunction j.left).counit.app H)

/-- Coherent subobject extension applied to the direct image lifts coherent
objects as soon as the open direct image has its compatible linearization. -/
theorem coherentExtension_of_subobjectExtension (hsub : SubobjectExtension.{u})
    (hlin : ∀ {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
      {a : ModObj T.X X} {b : ModObj T.X Y} (j : Y ⟶ X) [IsOpenImmersion j.left],
      IsExtensionSetting a b j → ∀ H : EquivariantCoherent b,
      ∃ L : Linearization a ((Scheme.Modules.pushforward j.left).obj H.sheaf),
        PullbackLinearizationComparison j L H.lin (openCounitIso j H.sheaf)) :
    CoherentExtension.{u} := by
  intro k _ T X Y a b j _ setting H
  let : LocallyOfFiniteType X.hom := setting.finiteType
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : H.sheaf.IsQuasicoherent := H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  obtain ⟨L, hL⟩ := hlin j setting H
  let M : EquivariantQuasicoherent a :=
    ⟨(Scheme.Modules.pushforward j.left).obj H.sheaf,
      openPushforward_isQuasicoherent j.left H.sheaf, L⟩
  let N : EquivariantQuasicoherent b := ⟨H.sheaf, inferInstance, H.lin⟩
  have hid : IsLinearizedMap H.lin N.lin (𝟙 H.sheaf) := by
    unfold IsLinearizedMap
    rw [(Scheme.Modules.pullback b.smul.left).map_id, (Scheme.Modules.pullback (snd T.X Y).left).map_id,
      Category.id_comp, Category.comp_id]
  obtain ⟨F, _, e, _, _, he, _⟩ :=
    hsub j setting M N (openCounitIso j H.sheaf) hL H (𝟙 _) inferInstance hid
  exact ⟨F, e, he⟩

end ExtensionOfObjects

/-- The kernel of a map from a coherent sheaf to a quasi-coherent sheaf is
coherent on a locally Noetherian scheme. -/
theorem kernel_finitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsFinitePresentation] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsFinitePresentation := by
  let : M.IsQuasicoherent := (inferInstance : M.IsFinitePresentation).exists_quasicoherentData.choose.isQuasicoherent
  let : (kernel f).IsQuasicoherent := kernel_isQuasicoherent f
  exact finitePresentation_of_mono (kernel.ι f)
private theorem biprod_spec_quasicoherent {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (M ⊞ N).IsQuasicoherent := by
  let S := moduleSpecΓFunctor (R := R)
  let D := tilde.functor R
  let : PreservesBinaryBiproducts D := preservesBinaryBiproducts_of_preservesBinaryCoproducts D
  let hM : IsIso (Scheme.Modules.fromTildeΓ (R := R) M) := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp inferInstance
  let hN : IsIso (Scheme.Modules.fromTildeΓ (R := R) N) := (isQuasicoherent_iff_isIso_fromTildeΓ N).mp inferInstance
  let e : tilde (S.obj M ⊞ S.obj N) ≅ M ⊞ N :=
    D.mapBiprod (S.obj M) (S.obj N) ≪≫ biprod.mapIso (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := R) M) hM) (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := R) N) hN)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The binary direct sum of quasi-coherent modules is quasi-coherent. -/
theorem biprod_isQuasicoherent {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (M ⊞ N).IsQuasicoherent := by
  apply quasicoherent_of_affineRestrictions
  intro U
  let P := restrictFunctor U.property.fromSpec
  let : PreservesBinaryBiproducts P := preservesBinaryBiproducts_of_preservesBinaryProducts P
  let e := P.mapBiprod M N
  let : (P.obj (M ⊞ N)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, U.val)).ringCatSheaf).prop_of_iso e.symm
      (biprod_spec_quasicoherent (M := P.obj M) (N := P.obj N))
  exact quasicoherent_restrict_of_fromSpec (M ⊞ N) U

section DirectSumLinearization

variable {k : Type u} [Field k] {T : GroupScheme k} {X : SchemeOver k} {a : ModObj T.X X}
  {F G : X.left.Modules}


private def pullBiprod {W : SchemeOver k} (x : W ⟶ X) (F G : X.left.Modules) :
    Pull x (F ⊞ G) ≅ Pull x F ⊞ Pull x G := by
  let P := Scheme.Modules.pullback x.left
  let : PreservesBinaryBiproducts P := preservesBinaryBiproducts_of_preservesBinaryCoproducts P
  exact P.mapBiprod F G

@[reassoc (attr := simp)]
private theorem pullBiprod_fst {W : SchemeOver k} (x : W ⟶ X) :
    (pullBiprod x F G).hom ≫ biprod.fst = PullMap x biprod.fst := by
  rw [pullBiprod, Functor.mapBiprod_hom, biprod.lift_fst]

@[reassoc (attr := simp)]
private theorem pullBiprod_snd {W : SchemeOver k} (x : W ⟶ X) :
    (pullBiprod x F G).hom ≫ biprod.snd = PullMap x biprod.snd := by
  rw [pullBiprod, Functor.mapBiprod_hom, biprod.lift_snd]

private theorem pullBiprod_hom_ext {W : SchemeOver k} (x : W ⟶ X) {C : W.left.Modules}
    {i j : C ⟶ Pull x (F ⊞ G)}
    (hf : i ≫ PullMap x biprod.fst = j ≫ PullMap x biprod.fst)
    (hg : i ≫ PullMap x biprod.snd = j ≫ PullMap x biprod.snd) : i = j := by
  apply (cancel_mono (pullBiprod x F G).hom).mp
  apply biprod.hom_ext
  · simpa only [Category.assoc, pullBiprod_fst] using hf
  · simpa only [Category.assoc, pullBiprod_snd] using hg

private def biprodLinearizationIso (L : Linearization a F) (K : Linearization a G) :
    Pull (snd T.X X) (F ⊞ G) ≅ Pull a.smul (F ⊞ G) :=
  pullBiprod (snd T.X X) F G ≪≫ biprod.mapIso L.iso K.iso ≪≫ (pullBiprod a.smul F G).symm

private theorem biprodSquare_fst (L : Linearization a F) (K : Linearization a G) :
    CommSq (biprodLinearizationIso L K).hom (PullMap (snd T.X X) biprod.fst)
      (PullMap a.smul biprod.fst) L.iso.hom := by
  refine ⟨?_⟩
  rw [← pullBiprod_fst a.smul]
  simp only [biprodLinearizationIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, biprod.mapIso_hom, biprod.map_fst, pullBiprod_fst_assoc]

private theorem biprodSquare_snd (L : Linearization a F) (K : Linearization a G) :
    CommSq (biprodLinearizationIso L K).hom (PullMap (snd T.X X) biprod.snd)
      (PullMap a.smul biprod.snd) K.iso.hom := by
  refine ⟨?_⟩
  rw [← pullBiprod_snd a.smul]
  simp only [biprodLinearizationIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, biprod.mapIso_hom, biprod.map_snd, pullBiprod_snd_assoc]

private theorem unitSquare {C : Type*} [Category C] {A B D E : C}
    {f : A ⟶ B} {g : D ⟶ E} {p : A ⟶ D} {q : B ⟶ E} {r : B ⟶ A} {s : E ⟶ D}
    (h : CommSq f p q g) (h' : CommSq r q p s) (hu : g ≫ s = 𝟙 _) :
    (f ≫ r) ≫ p = (𝟙 _) ≫ p := by
  have H := (h.horiz_comp h').w
  rw [hu, Category.comp_id] at H
  rwa [Category.id_comp]

private theorem compositionSquare {C : Type*} [Category C]
    {A B D E A' B' D' E' : C} {p : A ⟶ A'} {q : B ⟶ B'} {r : D ⟶ D'} {s : E ⟶ E'}
    {f : A ⟶ B} {g : B ⟶ D} {h : D ⟶ E} {i : A ⟶ E}
    {f' : A' ⟶ B'} {g' : B' ⟶ D'} {h' : D' ⟶ E'} {i' : A' ⟶ E'}
    (hf : CommSq f p q f') (hg : CommSq g q r g') (hh : CommSq h r s h')
    (hi : CommSq i p s i') (hc : ComposesTo f' g' h' i') : (f ≫ g ≫ h) ≫ s = i ≫ s := by
  have H := (hf.horiz_comp (hg.horiz_comp hh)).w
  change f' ≫ g' ≫ h' = i' at hc
  rwa [hc, ← hi.w] at H

private theorem biprodUnit (L : Linearization a F) (K : Linearization a G)
    (S : SchemeOver k) (x : S ⟶ X) :
    ∃ h : actOn a (1 : S ⟶ T.X) x = x,
      TransportHom (biprodLinearizationIso L K) 1 x ≫ (pullCongr (F ⊞ G) h).hom = 𝟙 _ := by
  obtain ⟨h, h₁⟩ := L.unit S x
  obtain ⟨_, h₂⟩ := K.unit S x
  refine ⟨h, pullBiprod_hom_ext x ?_ ?_⟩
  · exact unitSquare (transportSquare (biprodSquare_fst L K) 1 x) (pullCongrSquare h biprod.fst) h₁
  · exact unitSquare (transportSquare (biprodSquare_snd L K) 1 x) (pullCongrSquare h biprod.snd) h₂

set_option maxHeartbeats 520000 in
private theorem biprodMul_projection {D : X.left.Modules} (L : Linearization a D)
    (E : Pull (snd T.X X) (F ⊞ G) ≅ Pull a.smul (F ⊞ G)) (i : F ⊞ G ⟶ D)
    (e : CommSq E.hom (PullMap (snd T.X X) i) (PullMap a.smul i) L.iso.hom)
    {S : SchemeOver k} (s t : S ⟶ T.X) (x : S ⟶ X)
    (h : actOn a s (actOn a t x) = actOn a (s * t) x) :
    (TransportHom E t x ≫ TransportHom E s (actOn a t x) ≫ (pullCongr (F ⊞ G) h).hom) ≫
      PullMap (actOn a (s * t) x) i = TransportHom E (s * t) x ≫ PullMap (actOn a (s * t) x) i := by
  obtain ⟨_, hm⟩ := L.mul S s t x
  have H₁ := transportSquare e t x
  have H₂ := transportSquare e s (actOn a t x)
  have H₃ := pullCongrSquare h i
  have H₄ := transportSquare e (s * t) x
  change ComposesTo (TransportHom L.iso t x) (TransportHom L.iso s (actOn a t x))
    (pullCongr D h).hom (TransportHom L.iso (s * t) x) at hm
  exact compositionSquare H₁ H₂ H₃ H₄ hm

private theorem biprodMul (L : Linearization a F) (K : Linearization a G)
    (S : SchemeOver k) (s t : S ⟶ T.X) (x : S ⟶ X) :
    ∃ h : actOn a s (actOn a t x) = actOn a (s * t) x,
      TransportComposition (biprodLinearizationIso L K) s t x h := by
  let := a
  let h : actOn a s (actOn a t x) = actOn a (s * t) x := (mul_smul s t x).symm
  refine ⟨h, ?_⟩
  apply pullBiprod_hom_ext (actOn a (s * t) x)
  · exact biprodMul_projection L _ biprod.fst (biprodSquare_fst L K) s t x h
  · exact biprodMul_projection K _ biprod.snd (biprodSquare_snd L K) s t x h

/-- The direct-sum linearization on the binary biproduct of two linearized modules. -/
def biprodLinearization (L : Linearization a F) (K : Linearization a G) :
    Linearization a (F ⊞ G) where
  iso := biprodLinearizationIso L K
  unit := biprodUnit L K
  mul := biprodMul L K

theorem biprodLinearization_fst (L : Linearization a F) (K : Linearization a G) :
    IsLinearizedMap (biprodLinearization L K) L biprod.fst := (biprodSquare_fst L K).w

theorem biprodLinearization_snd (L : Linearization a F) (K : Linearization a G) :
    IsLinearizedMap (biprodLinearization L K) K biprod.snd := (biprodSquare_snd L K).w

private theorem linearizedMap_to_biprod {D : X.left.Modules}
    (J : Linearization a D) (L : Linearization a F) (K : Linearization a G) (f : D ⟶ F ⊞ G)
    (hf : IsLinearizedMap J L (f ≫ biprod.fst)) (hg : IsLinearizedMap J K (f ≫ biprod.snd)) :
    IsLinearizedMap J (biprodLinearization L K) f := by
  let P := projectionPull T X
  let A := actionPull a
  change J.iso.hom ≫ A.map f = P.map f ≫ (biprodLinearizationIso L K).hom
  apply pullBiprod_hom_ext a.smul
  · change (J.iso.hom ≫ A.map f) ≫ A.map biprod.fst =
      (P.map f ≫ (biprodLinearizationIso L K).hom) ≫ A.map biprod.fst
    rw [Category.assoc, Category.assoc, (biprodSquare_fst L K).w, ← A.map_comp, ← P.map_comp_assoc]
    exact hf
  · change (J.iso.hom ≫ A.map f) ≫ A.map biprod.snd =
      (P.map f ≫ (biprodLinearizationIso L K).hom) ≫ A.map biprod.snd
    rw [Category.assoc, Category.assoc, (biprodSquare_snd L K).w, ← A.map_comp, ← P.map_comp_assoc]
    exact hg

end DirectSumLinearization

section GraphAndClasses

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y}

private theorem supportedClass_vanishes (j : Y ⟶ X) (F : EquivariantCoherent a)
    (hF : IsZero (Pull j F.sheaf)) : (supportedClasses a j).mkQ (classOf F) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨F, hF, rfl⟩)

private theorem openPullback_kernel_cokernel_zero (j : Y ⟶ X) [IsOpenImmersion j.left]
    {F G : X.left.Modules} (f : F ⟶ G) [IsIso ((Scheme.Modules.pullback j.left).map f)] :
    IsZero (Pull j (kernel f)) ∧ IsZero (Pull j (cokernel f)) := by
  let P := Scheme.Modules.pullback j.left
  let : P.PreservesHomology := FlatCohomology.flatPullbackExact j.left
  let : PreservesFiniteLimits P := Functor.preservesFiniteLimits_of_preservesHomology P
  exact ⟨(isZero_kernel_of_mono (P.map f)).of_iso (PreservesKernel.iso P f),
    (isZero_cokernel_of_epi (P.map f)).of_iso (PreservesCokernel.iso P f)⟩

private theorem coimage_shortExact {C : Type*} [Category C] [Abelian C]
    {F G : C} (f : F ⟶ G) (h : Abelian.factorThruCoimage f ≫ cokernel.π f = 0) :
    (ShortComplex.mk (Abelian.factorThruCoimage f) (cokernel.π f) h).ShortExact := by
  let L := ShortComplex.mk (Abelian.factorThruCoimage f) (cokernel.π f) h
  let e : Abelian.coimage f ≅ kernel (cokernel.π f) := Abelian.coimageIsoImage f
  have he : e.hom ≫ kernel.ι (cokernel.π f) = L.f := by
    apply (cancel_epi (Abelian.coimage.π f)).mp
    change Abelian.coimage.π f ≫ Abelian.coimageImageComparison f ≫ Abelian.image.ι f =
      Abelian.coimage.π f ≫ Abelian.factorThruCoimage f
    rw [Abelian.coimage_image_factorisation, Abelian.coimage.fac]
  let e' : KernelFork.ofι L.f h ≅ KernelFork.ofι _ (kernel.condition (cokernel.π f)) :=
    Fork.ext e he
  let H : IsLimit (KernelFork.ofι L.f h) := IsLimit.ofIsoLimit (kernelIsKernel (cokernel.π f)) e'.symm
  exact ⟨L.exact_of_f_is_kernel H⟩

private theorem equivariant_coimage_class {F G : EquivariantCoherent a}
    [IsLocallyNoetherian X.left] (j : Y ⟶ X) (f : F.sheaf ⟶ G.sheaf) (hf : EquivariantHom f)
    (Kcoh : (kernel f).IsFinitePresentation) (Qcoh : (cokernel f).IsFinitePresentation)
    (Klim : Linearization a (kernel f)) (Qlim : Linearization a (cokernel f))
    (hi : IsLinearizedMap Klim F.lin (kernel.ι f))
    (hp : IsLinearizedMap G.lin Qlim (cokernel.π f))
    (hk : IsZero (Pull j (kernel f))) (hq : IsZero (Pull j (cokernel f))) :
    (supportedClasses a j).mkQ (classOf F) = (supportedClasses a j).mkQ (classOf G) := by
  let : F.sheaf.IsFinitePresentation := F.coherent
  let : (kernel f).IsFinitePresentation := Kcoh
  obtain ⟨L, hL⟩ := cokernelLinearization Klim F.lin (kernel.ι f) hi
  let I : EquivariantCoherent a := ⟨Abelian.coimage f, cokernel_finitePresentation (kernel.ι f), L⟩
  have h₁ : (ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f)
      (cokernel.condition (kernel.ι f))).ShortExact := ⟨ShortComplex.exact_cokernel _⟩
  let i := Abelian.factorThruCoimage f
  have hi' : IsLinearizedMap L G.lin i := by
    apply linearizedMap_of_epi_comp (f := Abelian.coimage.π f) hL
    rw [Abelian.coimage.fac]
    exact hf
  have e : i ≫ cokernel.π f = 0 := by
    apply (cancel_epi (Abelian.coimage.π f)).mp
    rw [← Category.assoc, Abelian.coimage.fac, cokernel.condition, comp_zero]
  have h₂ := coimage_shortExact f e
  let K : EquivariantCoherent a := ⟨kernel f, Kcoh, Klim⟩
  let Q : EquivariantCoherent a := ⟨cokernel f, Qcoh, Qlim⟩
  have eq₁ : classOf F = classOf K + classOf I := classOf_exact _ hi hL h₁
  have eq₂ : classOf G = classOf I + classOf Q := classOf_exact _ hi' hp h₂
  rw [eq₁, eq₂, map_add, map_add, supportedClass_vanishes j K hk,
    supportedClass_vanishes j Q hq, zero_add, add_zero]

set_option backward.isDefEq.respectTransparency false in
/-- A linearized map which is an isomorphism on the open has supported kernel
and cokernel and induces equality of the two coherent classes there. -/
theorem comparison_of_open_isIso (j : Y ⟶ X) [IsOpenImmersion j.left] [IsLocallyNoetherian X.left]
    {F G : EquivariantCoherent a} (f : F.sheaf ⟶ G.sheaf) (hf : EquivariantHom f)
    [IsIso ((Scheme.Modules.pullback j.left).map f)] :
    HasSupportedKernelCokernel j (F := F) (G := G) f ∧
      (supportedClasses a j).mkQ (classOf F) = (supportedClasses a j).mkQ (classOf G) := by
  let : F.sheaf.IsFinitePresentation := F.coherent
  let : G.sheaf.IsFinitePresentation := G.coherent
  let : G.sheaf.IsQuasicoherent := G.coherent.exists_quasicoherentData.choose.isQuasicoherent
  obtain ⟨L, hL⟩ := kernelLinearization F.lin G.lin f hf
  obtain ⟨J, hJ⟩ := cokernelLinearization F.lin G.lin f hf
  let K : EquivariantCoherent a := ⟨kernel f, kernel_finitePresentation f, L⟩
  let Q : EquivariantCoherent a := ⟨cokernel f, cokernel_finitePresentation f, J⟩
  obtain ⟨hK, hQ⟩ := openPullback_kernel_cokernel_zero j f
  refine ⟨⟨K, Q, kernel.ι f, cokernel.π f, kernel.condition f, cokernel.condition f, hL, hJ,
    ⟨kernelIsKernel f⟩, ⟨cokernelIsCokernel f⟩, hK, hQ⟩, ?_⟩
  exact equivariant_coimage_class j f hf K.coherent Q.coherent L J hL hJ hK hQ

set_option backward.isDefEq.respectTransparency false in
private theorem biprod_comparison (j : Y ⟶ X) (hj : IsEquivariantMap a b j)
    {F G : EquivariantCoherent a} {H K : EquivariantCoherent b}
    (eF : Pull j F.sheaf ≅ H.sheaf) (eG : Pull j G.sheaf ≅ K.sheaf)
    (hF : IsEquivariantPullback j F H eF) (hG : IsEquivariantPullback j G K eG) :
    ∃ e : Pull j (F.sheaf ⊞ G.sheaf) ≅ H.sheaf ⊞ K.sheaf,
      PullbackLinearizationComparison j (biprodLinearization F.lin G.lin)
        (biprodLinearization H.lin K.lin) e ∧
      e.hom ≫ biprod.fst = (Scheme.Modules.pullback j.left).map biprod.fst ≫ eF.hom ∧
      e.hom ≫ biprod.snd = (Scheme.Modules.pullback j.left).map biprod.snd ≫ eG.hom := by
  let e := pullBiprod j F.sheaf G.sheaf ≪≫ biprod.mapIso eF eG
  let P := Scheme.Modules.pullback j.left
  have ef : e.hom ≫ biprod.fst = P.map biprod.fst ≫ eF.hom := by
    simp only [e, Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_fst, pullBiprod_fst_assoc]
    rfl
  have eg : e.hom ≫ biprod.snd = P.map biprod.snd ≫ eG.hom := by
    simp only [e, Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_snd, pullBiprod_snd_assoc]
    rfl
  refine ⟨e, pullbackLinearizationComparison_of_linearized hj _ _ e ?_, ef, eg⟩
  apply linearizedMap_to_biprod
  · rw [ef]
    exact linearizedMap_comp (pullbackLinearization_map hj _ (biprodLinearization_fst F.lin G.lin))
      (linearized_of_pullbackLinearizationComparison hj F.lin H.lin eF hF)
  · rw [eg]
    exact linearizedMap_comp (pullbackLinearization_map hj _ (biprodLinearization_snd F.lin G.lin))
      (linearized_of_pullbackLinearizationComparison hj G.lin K.lin eG hG)

set_option backward.isDefEq.respectTransparency false in
/-- The coherent graph extension and equality of classes follow from the
extension of subobjects inside a specified quasi-coherent module. -/
theorem graphComparison_of_subobjectExtension (hsub : SubobjectExtension.{u}) : GraphComparison.{u} := by
  intro k _ T X Y a b j _ setting F G H K eF eG d heF heG hd
  obtain ⟨e, he, ef, eg⟩ := biprod_comparison j setting.equivariant eF eG heF heG
  let : F.sheaf.IsQuasicoherent := F.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let : G.sheaf.IsQuasicoherent := G.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let : H.sheaf.IsQuasicoherent := H.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let : K.sheaf.IsQuasicoherent := K.coherent.exists_quasicoherentData.choose.isQuasicoherent
  let M : EquivariantQuasicoherent a := ⟨F.sheaf ⊞ G.sheaf,
    biprod_isQuasicoherent, biprodLinearization F.lin G.lin⟩
  let N : EquivariantQuasicoherent b := ⟨H.sheaf ⊞ K.sheaf,
    biprod_isQuasicoherent, biprodLinearization H.lin K.lin⟩
  let g : H.sheaf ⟶ H.sheaf ⊞ K.sheaf := biprod.lift (𝟙 _) d.hom
  have mg : Mono g := mono_of_mono_fac (biprod.lift_fst (𝟙 H.sheaf) d.hom)
  have hg : IsLinearizedMap H.lin N.lin g := by
    apply linearizedMap_to_biprod
    · rw [biprod.lift_fst]
      unfold IsLinearizedMap
      rw [(Scheme.Modules.pullback b.smul.left).map_id,
        (Scheme.Modules.pullback (snd T.X Y).left).map_id, Category.comp_id, Category.id_comp]
    · rw [biprod.lift_snd]
      exact hd
  obtain ⟨D, m, eD, mm, hm, heD, hcomp⟩ := hsub j setting M N e he H g mg hg
  let P := Scheme.Modules.pullback j.left
  let p : D.sheaf ⟶ F.sheaf := m ≫ biprod.fst
  let q : D.sheaf ⟶ G.sheaf := m ≫ biprod.snd
  have hp : EquivariantHom p := linearizedMap_comp hm (biprodLinearization_fst F.lin G.lin)
  have hq : EquivariantHom q := linearizedMap_comp hm (biprodLinearization_snd F.lin G.lin)
  have h₁ : P.map p ≫ eF.hom = eD.hom := by
    rw [P.map_comp, Category.assoc, ← ef, ← Category.assoc, hcomp, Category.assoc, biprod.lift_fst,
      Category.comp_id]
  have h₂ : P.map q ≫ eG.hom = eD.hom ≫ d.hom := by
    rw [P.map_comp, Category.assoc, ← eg, ← Category.assoc, hcomp, Category.assoc, biprod.lift_snd]
  let : IsIso (P.map p) := IsIso.of_isIso_fac_right h₁
  let : IsIso (P.map q) := IsIso.of_isIso_fac_right h₂
  let : LocallyOfFiniteType X.hom := setting.finiteType
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  obtain ⟨hP, eqP⟩ := comparison_of_open_isIso j p hp
  obtain ⟨hQ, eqQ⟩ := comparison_of_open_isIso j q hq
  exact ⟨M.lin, D, m, eD, biprodLinearization_fst F.lin G.lin, biprodLinearization_snd F.lin G.lin,
    mm, hm, heD, h₁, h₂, hP, hQ, eqP.symm.trans eqQ⟩

end GraphAndClasses

section OpenBaseChange

variable {k : Type u} [Field k] {X Y U V : SchemeOver k}
  (j : Y ⟶ X) (l : V ⟶ U) (g : U ⟶ X) (r : V ⟶ Y)

open private comparePull from LinearAlgebraicGroups.Representation.EquivariantAffineModules

/-- Under inverse image, the restriction comparison for a commutative square
is the pullback of the original adjunction counit. -/
def openBaseChangeCounit (h : l ≫ g = r ≫ j) (H : Y.left.Modules) :
    Pull l (Pull g ((Scheme.Modules.pushforward j.left).obj H)) ⟶ Pull r H :=
  let F := (Scheme.Modules.pushforward j.left).obj H
  let c := (Scheme.Modules.pullbackPushforwardAdjunction j.left).counit.app H
  (comparePull F l g h).hom ≫ (pullComp F r j).inv ≫ PullMap r c

@[reassoc]
theorem openBaseChange_counit (h : l ≫ g = r ≫ j) (H : Y.left.Modules) :
    PullMap l (openBaseChange j l g r h H) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction l.left).counit.app (Pull r H) =
      openBaseChangeCounit j l g r h H := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction l.left
  have he := (A.homEquiv _ _).symm_apply_apply (openBaseChangeCounit j l g r h H)
  rw [A.homEquiv_counit] at he
  exact he

/-- When the base-change map is an isomorphism, restriction detects equality
of maps into the pulled-back direct image. -/
theorem openBaseChange_hom_ext (h : l ≫ g = r ≫ j) (H : Y.left.Modules)
    [IsIso (openBaseChange j l g r h H)] {N : U.left.Modules}
    (f f' : N ⟶ Pull g ((Scheme.Modules.pushforward j.left).obj H))
    (e : PullMap l f = PullMap l f') : f = f' := by
  let L := Scheme.Modules.pullback l.left
  let A := Scheme.Modules.pullbackPushforwardAdjunction l.left
  let b := openBaseChange j l g r h H
  apply (cancel_mono b).mp
  apply (A.homEquiv N (Pull r H)).symm.injective
  rw [A.homEquiv_counit, A.homEquiv_counit, L.map_comp, L.map_comp]
  exact congrArg (fun t : L.obj N ⟶ L.obj (Pull g ((Scheme.Modules.pushforward j.left).obj H)) =>
    (t ≫ L.map b) ≫ A.counit.app (Pull r H)) e

end OpenBaseChange

section ActionSquare

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y} {j : Y ⟶ X}


private theorem actionShear_comm (hj : IsEquivariantMap a b j) :
    (actionShear b).hom ≫ (𝟙 T.X ⊗ₘ j) = (𝟙 T.X ⊗ₘ j) ≫ (actionShear a).hom := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [actionShear]
  · simpa [actionShear, Category.assoc, IsEquivariantMap] using hj

/-- An equivariant morphism gives a cartesian square on the action maps.
The shear isomorphisms identify it with the projection square. -/
theorem actionSquare_isPullback (hj : IsEquivariantMap a b j) :
    IsPullback (𝟙 T.X ⊗ₘ j).left b.smul.left a.smul.left j.left := by
  let Q := Over.forget (Spec (CommRingCat.of k))
  let eq := Q.mapIso (actionShear b)
  let ep := Q.mapIso (actionShear a)
  apply (tensor_snd_isPullback T.X j).of_iso' eq ep (Iso.refl _) (Iso.refl _)
  · exact congrArg Over.Hom.left (actionShear_comm hj)
  · change (actionShear b).hom.left ≫ (snd T.X Y).left = b.smul.left ≫ 𝟙 _
    rw [Category.comp_id]
    exact congrArg Over.Hom.left (lift_snd _ _)
  · change (actionShear a).hom.left ≫ (snd T.X X).left = a.smul.left ≫ 𝟙 _
    rw [Category.comp_id]
    exact congrArg Over.Hom.left (lift_snd _ _)
  · simp

end ActionSquare

section TripleSquare

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y} {j : Y ⟶ X}


private abbrev tripleAction (a : ModObj T.X X) : triple T X ⟶ X :=
  actOn a (tripleFirst T X * tripleSecond T X) (tripleBase T X)

private theorem tripleAction_factor (a : ModObj T.X X) :
    tripleAction a = (𝟙 T.X ⊗ₘ a.smul) ≫ a.smul := by
  let p := snd T.X (T.X ⊗ X)
  have h₁ : actOn a (tripleSecond T X) (tripleBase T X) = p ≫ a.smul := by
    change lift (p ≫ fst T.X X) (p ≫ snd T.X X) ≫ a.smul = _
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  let := a
  change (tripleFirst T X * tripleSecond T X) • tripleBase T X = _
  rw [mul_smul]
  change actOn a (tripleFirst T X) (actOn a (tripleSecond T X) (tripleBase T X)) = _
  rw [h₁]
  have hc : lift (tripleFirst T X) (p ≫ a.smul) = 𝟙 T.X ⊗ₘ a.smul := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [p, tripleFirst]
  change lift (tripleFirst T X) (p ≫ a.smul) ≫ a.smul = _
  rw [hc]

private theorem tensor_lift_comm {P S U V W : SchemeOver k} {f : P ⟶ U} {g : P ⟶ V}
    {i : U ⟶ W} {j : V ⟶ W} (h : f ≫ i = g ≫ j) :
    (𝟙 S ⊗ₘ f).left ≫ (𝟙 S ⊗ₘ i).left = (𝟙 S ⊗ₘ g).left ≫ (𝟙 S ⊗ₘ j).left := by
  have hc : (𝟙 S ⊗ₘ f) ≫ (𝟙 S ⊗ₘ i) = (𝟙 S ⊗ₘ g) ≫ (𝟙 S ⊗ₘ j) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, h]
  exact congrArg (fun v : S ⊗ P ⟶ S ⊗ W => v.left) hc

private theorem tensor_lift_snd_left (S : SchemeOver k) {V W : SchemeOver k} (f : V ⟶ W) :
    (snd S V).left ≫ f.left = (𝟙 S ⊗ₘ f).left ≫ (snd S W).left := by
  exact congrArg Over.Hom.left (show snd S V ≫ f = (𝟙 S ⊗ₘ f) ≫ snd S W by simp)

private theorem tensor_isPullback (S : SchemeOver k) {P U V W : SchemeOver k}
    {f : P ⟶ U} {g : P ⟶ V} {i : U ⟶ W} {j : V ⟶ W}
    (h : IsPullback f.left g.left i.left j.left) :
    IsPullback (𝟙 S ⊗ₘ f).left (𝟙 S ⊗ₘ g).left (𝟙 S ⊗ₘ i).left (𝟙 S ⊗ₘ j).left := by
  have h' := (tensor_snd_isPullback S f).paste_vert h
  rw [tensor_lift_snd_left S g, tensor_lift_snd_left S i] at h'
  exact h'.of_bot (tensor_lift_comm (S := S) (Over.OverMorphism.ext h.w)) (tensor_snd_isPullback S j)

private abbrev tripleInclusion (j : Y ⟶ X) : triple T Y ⟶ triple T X :=
  𝟙 T.X ⊗ₘ (𝟙 T.X ⊗ₘ j)

/-- The composite group transport on the universal two-element test scheme
has the corresponding cartesian square over any equivariant map. -/
theorem tripleAction_isPullback (hj : IsEquivariantMap a b j) :
    IsPullback (tripleInclusion j : triple T Y ⟶ triple T X).left
      (tripleAction b).left (tripleAction a).left j.left := by
  rw [tripleAction_factor a, tripleAction_factor b, Over.comp_left, Over.comp_left]
  let H := actionSquare_isPullback hj
  exact (tensor_isPullback T.X H).paste_vert H

end TripleSquare

section OpenPushforwardIso

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y} {j : Y ⟶ X}

open private comparePull evalPullIso from LinearAlgebraicGroups.Representation.EquivariantAffineModules

private abbrev actionGraphMap (j : Y ⟶ X) : T.X ⊗ Y ⟶ T.X ⊗ X := 𝟙 T.X ⊗ₘ j

private theorem actionGraphMap_snd (j : Y ⟶ X) :
    (actionGraphMap j : T.X ⊗ Y ⟶ T.X ⊗ X) ≫ snd T.X X = snd T.X Y ≫ j := by
  simp [actionGraphMap]

set_option backward.isDefEq.respectTransparency false in
private theorem combine_baseChange_counits (hj : IsEquivariantMap a b j) (H : Y.left.Modules)
    (θ : Pull (snd T.X Y) H ≅ Pull b.smul H)
    (p : IsIso (openBaseChange j (actionGraphMap j) (snd T.X X) (snd T.X Y) (actionGraphMap_snd j) H))
    (q : IsIso (openBaseChange j (actionGraphMap j) a.smul b.smul hj.symm H)) :
    let F := (Scheme.Modules.pushforward j.left).obj H
    ∃ e : Pull (snd T.X X) F ≅ Pull a.smul F,
      PullMap (actionGraphMap j) e.hom ≫ openBaseChangeCounit j (actionGraphMap j) a.smul b.smul
          hj.symm H =
        openBaseChangeCounit j (actionGraphMap j) (snd T.X X) (snd T.X Y) (actionGraphMap_snd j) H ≫
          θ.hom := by
  let m := (actionGraphMap j : T.X ⊗ Y ⟶ T.X ⊗ X)
  let B := Scheme.Modules.pushforward m.left
  let L := Scheme.Modules.pullback m.left
  let D := Scheme.Modules.pullbackPushforwardAdjunction m.left
  let ρ := openBaseChange j m (snd T.X X) (snd T.X Y) (actionGraphMap_snd j) H
  let α := openBaseChange j m a.smul b.smul hj.symm H
  let ei := @asIso _ _ _ _ α q
  let di := @asIso _ _ _ _ ρ p
  let e := di ≪≫ B.mapIso θ ≪≫ ei.symm
  have he : e.hom ≫ α = ρ ≫ B.map θ.hom := by
    change (ρ ≫ B.map θ.hom ≫ ei.inv) ≫ α = _
    have h : ei.inv ≫ α = 𝟙 _ := ei.inv_hom_id
    simp only [Category.assoc, h]
    exact congrArg (ρ ≫ ·) (Category.comp_id (B.map θ.hom))
  have ha : L.map α ≫ D.counit.app (Pull b.smul H) = openBaseChangeCounit j m a.smul b.smul hj.symm H :=
    openBaseChange_counit j m a.smul b.smul hj.symm H
  have hp : L.map ρ ≫ D.counit.app (Pull (snd T.X Y) H) =
      openBaseChangeCounit j m (snd T.X X) (snd T.X Y) (actionGraphMap_snd j) H :=
    openBaseChange_counit j m (snd T.X X) (snd T.X Y) (actionGraphMap_snd j) H
  refine ⟨e, ?_⟩
  change L.map e.hom ≫ _ = _ ≫ θ.hom
  have hnat : L.map (B.map θ.hom) ≫ D.counit.app (Pull b.smul H) =
      D.counit.app (Pull (snd T.X Y) H) ≫ θ.hom := D.counit.naturality θ.hom
  rw [← ha, ← hp, ← L.map_comp_assoc, he, L.map_comp]
  simp only [Category.assoc, hnat]

set_option backward.isDefEq.respectTransparency false in
/-- The two instances of base change for the projection and action give a
linearization isomorphism on the direct image. Its pullback commutes with the
actual open-immersion counit. -/
theorem openPushforward_iso_of_baseChange (hj : IsEquivariantMap a b j) (H : Y.left.Modules)
    (K : Linearization b H)
    (p : IsIso (openBaseChange j (actionGraphMap j) (snd T.X X) (snd T.X Y) (actionGraphMap_snd j) H))
    (q : IsIso (openBaseChange j (actionGraphMap j) a.smul b.smul hj.symm H)) :
    let F := (Scheme.Modules.pushforward j.left).obj H
    let c := (Scheme.Modules.pullbackPushforwardAdjunction j.left).counit.app H
    ∃ e : Pull (snd T.X X) F ≅ Pull a.smul F,
      CommSq (pullbackLinearizationIso hj e).hom (PullMap (snd T.X Y) c) (PullMap b.smul c) K.iso.hom := by
  let F := (Scheme.Modules.pushforward j.left).obj H
  let c := (Scheme.Modules.pullbackPushforwardAdjunction j.left).counit.app H
  let m := (actionGraphMap j : T.X ⊗ Y ⟶ T.X ⊗ X)
  obtain ⟨e, he⟩ := combine_baseChange_counits hj H K.iso p q
  refine ⟨e, ⟨?_⟩⟩
  change (pullbackLinearizationIso hj e).hom ≫ PullMap b.smul c = PullMap (snd T.X Y) c ≫ K.iso.hom
  let s := comparePull F m (snd T.X X) (actionGraphMap_snd j)
  change (pullComp F (snd T.X Y) j).hom ≫ s.inv ≫ PullMap m e.hom ≫
      openBaseChangeCounit j m a.smul b.smul hj.symm H = PullMap (snd T.X Y) c ≫ K.iso.hom
  rw [he]
  change (pullComp F (snd T.X Y) j).hom ≫ s.inv ≫ s.hom ≫
      (pullComp F (snd T.X Y) j).inv ≫ PullMap (snd T.X Y) c ≫ K.iso.hom = _
  rw [s.inv_hom_id_assoc, (pullComp F (snd T.X Y) j).hom_inv_id_assoc]

end OpenPushforwardIso

section DetectTransportOnRestriction

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y S W : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y} {F : X.left.Modules} {j : Y ⟶ X}

open private comparePull comparePull_congr pullback_transport_compare pullback_transport_two_compare
  equivariant_actOn equivariant_iterated_actOn pullCongr_refl
  from LinearAlgebraicGroups.Representation.EquivariantAffineModules

private theorem comparePull_refl_hom (r : W ⟶ S) (g : S ⟶ X) :
    (comparePull F r g rfl).hom = (pullComp F r g).hom := by
  simp only [comparePull, Iso.trans_hom, pullCongr_refl, Category.comp_id]

private theorem unit_on_image (hj : IsEquivariantMap a b j)
    (L : Pull (snd T.X X) F ≅ Pull a.smul F) (y : S ⟶ Y)
    (h : actOn a (1 : S ⟶ T.X) (y ≫ j) = y ≫ j)
    (hy : actOn b (1 : S ⟶ T.X) y = y)
    (hu : TransportHom (pullbackLinearizationIso hj L) 1 y ≫ (pullCongr (Pull j F) hy).hom = 𝟙 _) :
    TransportHom L 1 (y ≫ j) ≫ (pullCongr F h).hom = 𝟙 _ := by
  let e₀ := pullComp F y j
  let e₁ := comparePull F (actOn b 1 y) j (equivariant_actOn hj).symm
  have H₁ : CommSq (TransportHom (pullbackLinearizationIso hj L) 1 y) e₀.hom e₁.hom
      (TransportHom L 1 (y ≫ j)) := ⟨pullback_transport_compare hj L 1 y⟩
  have sq : (pullCongr (Pull j F) hy).hom ≫ e₀.hom = e₁.hom ≫ (pullCongr F h).hom := by
    rw [← comparePull_refl_hom]
    exact comparePull_congr F j hy h (equivariant_actOn hj).symm rfl
  exact cancelUnitEpi H₁ ⟨sq⟩ hu

private theorem composition_conjugacy {C : Type*} [Category C]
    {A B E A' B' E' : C} {p : A ⟶ A'} {q : B ⟶ B'} {r : E ⟶ E'}
    {u : A ⟶ B} {v : B ⟶ E} {w : A ⟶ E}
    {u' : A' ⟶ B'} {v' : B' ⟶ E'} {w' : A' ⟶ E'} [Epi p]
    (h₁ : CommSq u p q u') (h₂ : CommSq v q r v') (h₃ : CommSq w p r w') (h : u ≫ v = w) :
    u' ≫ v' = w' := by
  have hSq := (h₁.horiz_comp h₂).w
  rw [h, h₃.w] at hSq
  exact (cancel_epi p).mp hSq.symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
private theorem mul_on_image (hj : IsEquivariantMap a b j)
    (L : Pull (snd T.X X) F ≅ Pull a.smul F) (s t : S ⟶ T.X) (y : S ⟶ Y)
    (h : actOn a s (actOn a t (y ≫ j)) = actOn a (s * t) (y ≫ j))
    (hy : actOn b s (actOn b t y) = actOn b (s * t) y)
    (hm : TransportComposition (pullbackLinearizationIso hj L) s t y hy) :
    TransportComposition L s t (y ≫ j) h := by
  let Ly := pullbackLinearizationIso hj L
  let e₀ := pullComp F y j
  let e₁ := comparePull F (actOn b s (actOn b t y)) j (equivariant_iterated_actOn hj s t y).symm
  let e₂ := comparePull F (actOn b (s * t) y) j (equivariant_actOn hj).symm
  have h₁ : CommSq (TransportHom Ly t y ≫ TransportHom Ly s (actOn b t y)) e₀.hom e₁.hom
      (TransportHom L t (y ≫ j) ≫ TransportHom L s (actOn a t (y ≫ j))) :=
    ⟨by simpa only [Category.assoc] using pullback_transport_two_compare hj L s t y⟩
  have h₂ : CommSq (pullCongr (Pull j F) hy).hom e₁.hom e₂.hom (pullCongr F h).hom :=
    ⟨comparePull_congr F j hy h _ _⟩
  have h₃ : CommSq (TransportHom Ly (s * t) y) e₀.hom e₂.hom (TransportHom L (s * t) (y ≫ j)) :=
    ⟨pullback_transport_compare hj L (s * t) y⟩
  change TransportHom Ly t y ≫ TransportHom Ly s (actOn b t y) ≫
    (pullCongr (Pull j F) hy).hom = TransportHom Ly (s * t) y at hm
  have hm' : (TransportHom Ly t y ≫ TransportHom Ly s (actOn b t y)) ≫
      (pullCongr (Pull j F) hy).hom = TransportHom Ly (s * t) y := by
    simpa only [Category.assoc] using hm
  have H := composition_conjugacy h₁ h₂ h₃ hm'
  change TransportHom L t (y ≫ j) ≫ TransportHom L s (actOn a t (y ≫ j)) ≫ (pullCongr F h).hom = _
  simpa only [Category.assoc] using H

private theorem unit_map_eq_of_unit_restriction (L : Pull (snd T.X X) F ≅ Pull a.smul F)
    (r : W ⟶ S) (x : S ⟶ X) (h : actOn a (1 : S ⟶ T.X) x = x)
    {x' : W ⟶ X} (hx : r ≫ x = x') (h' : actOn a (1 : W ⟶ T.X) x' = x')
    (hu : TransportHom L 1 x' ≫ (pullCongr F h').hom = 𝟙 _) :
    PullMap r (TransportHom L 1 x ≫ (pullCongr F h).hom) = PullMap r (𝟙 _) := by
  let P := Scheme.Modules.pullback r.left
  let h₁ := transportReindexSquare L r 1 x (MonObj.comp_one r) hx
  let h₂ := pullCongrReindexSquare (F := F) r h h' (actOn_comp r 1 x (MonObj.comp_one r) hx) hx
  have e := cancelUnitMono h₁ h₂ hu
  change P.map _ = P.map _
  rwa [P.map_comp, P.map_id]

set_option maxHeartbeats 550000 in
private theorem mul_map_eq_of_mul_restriction (L : Pull (snd T.X X) F ≅ Pull a.smul F)
    (r : W ⟶ S) (s t : S ⟶ T.X) (x : S ⟶ X)
    (h : actOn a s (actOn a t x) = actOn a (s * t) x)
    {s' t' : W ⟶ T.X} {x' : W ⟶ X} (hs : r ≫ s = s') (ht : r ≫ t = t') (hx : r ≫ x = x')
    (h' : actOn a s' (actOn a t' x') = actOn a (s' * t') x')
    (hm : TransportComposition L s' t' x' h') :
    PullMap r (TransportHom L t x ≫ TransportHom L s (actOn a t x) ≫ (pullCongr F h).hom) =
      PullMap r (TransportHom L (s * t) x) := by
  have hp : r ≫ (s * t) = s' * t' := (MonObj.comp_mul r s t).trans (by rw [hs, ht])
  have H₁ := transportReindexSquare L r t x ht hx
  have H₂ := transportReindexSquare L r s (actOn a t x) hs (actOn_comp r t x ht hx)
  have H₄ := transportReindexSquare L r (s * t) x hp hx
  have H₃ := pullCongrReindexSquare (F := F) r h h' (actOn_comp r s (actOn a t x) hs
    (actOn_comp r t x ht hx)) (actOn_comp r (s * t) x hp hx)
  change ComposesTo (TransportHom L t' x') (TransportHom L s' (actOn a t' x'))
    (pullCongr F h').hom (TransportHom L (s' * t') x') at hm
  have H := cancelCompositionMono H₁ H₂ H₃ H₄ hm
  let P := Scheme.Modules.pullback r.left
  change P.map _ = P.map _
  rw [P.map_comp, P.map_comp]
  exact H

end DetectTransportOnRestriction

section EquivariantOpenDirectImage

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y} {j : Y ⟶ X}
  [IsOpenImmersion j.left] [QuasiCompact j.left] (hbc : FlatOpenBaseChange.{u})
  (H : Y.left.Modules) (hH : H.IsQuasicoherent)

private abbrev pushOpen (j : Y ⟶ X) (H : Y.left.Modules) := (Scheme.Modules.pushforward j.left).obj H


include hbc hH

set_option backward.isDefEq.respectTransparency false in
private theorem openPushforward_unit (hj : IsEquivariantMap a b j)
    (θ : Pull (snd T.X X) (pushOpen j H) ≅ Pull a.smul (pushOpen j H))
    (K : Linearization b (Pull j (pushOpen j H)))
    (hK : K.iso = pullbackLinearizationIso hj θ) :
    ∃ h : actOn a (1 : X ⟶ T.X) (𝟙 X) = 𝟙 X,
      TransportHom θ 1 (𝟙 X) ≫ (pullCongr (pushOpen j H) h).hom = 𝟙 _ := by
  let x : X ⟶ X := 𝟙 X
  let y : Y ⟶ Y := 𝟙 Y
  have hx : j ≫ x = y ≫ j := by simp [x, y]
  have hpb : IsPullback j.left y.left x.left j.left := by
    rw [show x.left = 𝟙 X.left from rfl, show y.left = 𝟙 Y.left from rfl]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  have flat : Flat x.left := inferInstanceAs (Flat (𝟙 X.left))
  let : IsIso (openBaseChange j j x y hx H) := hbc j j x y hx hpb inferInstance inferInstance flat H hH
  let := a
  let h : actOn a (1 : X ⟶ T.X) x = x := one_smul (X ⟶ T.X) x
  let h' : actOn a (1 : Y ⟶ T.X) (y ≫ j) = y ≫ j := one_smul (Y ⟶ T.X) (y ≫ j)
  obtain ⟨hy, hu⟩ := K.unit Y y
  rw [hK] at hu
  have he := unit_on_image hj θ y h' hy hu
  refine ⟨h, ?_⟩
  exact openBaseChange_hom_ext j j x y hx H _ _ (unit_map_eq_of_unit_restriction θ j x h hx h' he)

omit hbc hH [IsOpenImmersion j.left] [QuasiCompact j.left] in
set_option maxHeartbeats 380000 in
private theorem openPushforward_mul_detected (hj : IsEquivariantMap a b j)
    (θ : Pull (snd T.X X) (pushOpen j H) ≅ Pull a.smul (pushOpen j H))
    (K : Linearization b (Pull j (pushOpen j H)))
    (hK : K.iso = pullbackLinearizationIso hj θ)
    {S V : SchemeOver k} (l : V ⟶ S) (r : V ⟶ Y)
    (s t : S ⟶ T.X) (x : S ⟶ X) (s' t' : V ⟶ T.X) (y : V ⟶ Y)
    (hs : l ≫ s = s') (ht : l ≫ t = t') (hx : l ≫ x = y ≫ j)
    (hc : l ≫ actOn a (s * t) x = r ≫ j)
    [IsIso (openBaseChange j l (actOn a (s * t) x) r hc H)] :
    ∃ h : actOn a s (actOn a t x) = actOn a (s * t) x, TransportComposition θ s t x h := by
  let := a
  let h : actOn a s (actOn a t x) = actOn a (s * t) x := (mul_smul s t x).symm
  let h' : actOn a s' (actOn a t' (y ≫ j)) = actOn a (s' * t') (y ≫ j) := (mul_smul s' t' (y ≫ j)).symm
  obtain ⟨hy, hm⟩ := K.mul V s' t' y
  rw [hK] at hm
  have he := mul_on_image hj θ s' t' y h' hy hm
  refine ⟨h, ?_⟩
  change TransportHom θ t x ≫ TransportHom θ s (actOn a t x) ≫ (pullCongr (pushOpen j H) h).hom =
    TransportHom θ (s * t) x
  exact openBaseChange_hom_ext j l (actOn a (s * t) x) r hc H _ _
    (mul_map_eq_of_mul_restriction θ l s t x h hs ht hx h' he)

set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency false in
private theorem openPushforward_mul (hj : IsEquivariantMap a b j)
    (θ : Pull (snd T.X X) (pushOpen j H) ≅ Pull a.smul (pushOpen j H))
    (K : Linearization b (Pull j (pushOpen j H)))
    (hK : K.iso = pullbackLinearizationIso hj θ) :
    ∃ h : actOn a (tripleFirst T X) (actOn a (tripleSecond T X) (tripleBase T X)) = tripleAction a,
      TransportComposition θ (tripleFirst T X) (tripleSecond T X) (tripleBase T X) h := by
  let s := tripleFirst T X
  let t := tripleSecond T X
  let x := tripleBase T X
  let s' := tripleFirst T Y
  let t' := tripleSecond T Y
  let y := tripleBase T Y
  let l := (tripleInclusion j : triple T Y ⟶ triple T X)
  let r := tripleAction b
  let g := tripleAction a
  have hs : l ≫ s = s' := by simp [l, s, s']
  have ht : l ≫ t = t' := by simp [l, t, t']
  have hx : l ≫ x = y ≫ j := by simp [l, x, y, Category.assoc]
  have hpb := tripleAction_isPullback hj
  have hc : l ≫ g = r ≫ j := Over.OverMorphism.ext hpb.w
  have flat : Flat g.left := tripleActionFlat a
  let : IsIso (openBaseChange j l g r hc H) := hbc j l g r hc hpb inferInstance inferInstance flat H hH
  exact openPushforward_mul_detected H hj θ K hK l r s t x s' t' y hs ht hx hc

private def openPushforwardLinearization (hj : IsEquivariantMap a b j)
    (θ : Pull (snd T.X X) (pushOpen j H) ≅ Pull a.smul (pushOpen j H))
    (J : Linearization b (Pull j (pushOpen j H))) (hJ : J.iso = pullbackLinearizationIso hj θ) :
    Linearization a (pushOpen j H) where
  iso := θ
  unit := linearizationUnit_of_universal θ (openPushforward_unit hbc H hH hj θ J hJ)
  mul := linearizationMul_of_universal θ (openPushforward_mul hbc H hH hj θ J hJ)

set_option maxHeartbeats 450000 in
set_option backward.isDefEq.respectTransparency false in
private theorem openPushforward_linearization_of_iso (hj : IsEquivariantMap a b j)
    (θ : Pull (snd T.X X) (pushOpen j H) ≅ Pull a.smul (pushOpen j H)) (K : Linearization b H)
    (hθ : CommSq (pullbackLinearizationIso hj θ).hom (PullMap (snd T.X Y) (openCounitIso j H).hom)
      (PullMap b.smul (openCounitIso j H).hom) K.iso.hom) :
    ∃ L : Linearization a (pushOpen j H),
      PullbackLinearizationComparison j L K (openCounitIso j H) := by
  let c := (openCounitIso j H).hom
  let θY := pullbackLinearizationIso hj θ
  let J := linearizationOfMono K θY c hθ
  have hJ : J.iso = θY := rfl
  let L := openPushforwardLinearization hbc H hH hj θ J hJ
  have hh : IsLinearizedMap (pullbackLinearization hj L) K c := hθ.w
  exact ⟨L, pullbackLinearizationComparison_of_linearized hj L K (openCounitIso j H) hh⟩

set_option backward.isDefEq.respectTransparency false in
/-- Flat base change equips the actual open direct image with a linearization
whose pullback comparison is the actual adjunction counit. -/
theorem openPushforward_linearization_of_flatBaseChange (hj : IsEquivariantMap a b j)
    (K : Linearization b H) :
    ∃ L : Linearization a (pushOpen j H),
      PullbackLinearizationComparison j L K (openCounitIso j H) := by
  let l := (actionGraphMap j : T.X ⊗ Y ⟶ T.X ⊗ X)
  have hp := hbc j l (snd T.X X) (snd T.X Y) (actionGraphMap_snd j)
    (tensor_snd_isPullback T.X j) inferInstance inferInstance (projectionFlat _ _) H hH
  have ha := hbc j l a.smul b.smul hj.symm (actionSquare_isPullback hj)
    inferInstance inferInstance (actionFlat a) H hH
  obtain ⟨θ, hθ⟩ := openPushforward_iso_of_baseChange hj H K hp ha
  exact openPushforward_linearization_of_iso hbc H hH hj θ K hθ

end EquivariantOpenDirectImage

section EquivariantAdjunction

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Y} {j : Y ⟶ X}

open private comparePull evalPullIso from LinearAlgebraicGroups.Representation.EquivariantAffineModules

set_option backward.isDefEq.respectTransparency false in
private theorem evaluated_equivariance {V W : SchemeOver k} {F G : X.left.Modules}
    {p q : V ⟶ X} {x y : W ⟶ X}
    (L : Pull p F ≅ Pull q F) (K : Pull p G ≅ Pull q G) (m : F ⟶ G)
    (l : W ⟶ V) (hp : l ≫ p = x) (hq : l ≫ q = y)
    (hm : (evalPullIso L l hp hq).hom ≫ PullMap y m = PullMap x m ≫ (evalPullIso K l hp hq).hom) :
    PullMap l (L.hom ≫ PullMap q m) = PullMap l (PullMap p m ≫ K.hom) := by
  simp only [evalPullIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    comparePull_naturality, ← comparePull_inv_naturality_assoc] at hm
  have hm' := (cancel_epi (comparePull F l p hp).inv).mp hm
  simp only [← Functor.map_comp_assoc] at hm'
  exact (cancel_mono (comparePull G l q hq).hom).mp hm'

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
private theorem restricted_equivariance {F G : X.left.Modules}
    (hj : IsEquivariantMap a b j) (L : Linearization a F) (K : Linearization a G) (u : F ⟶ G)
    (hu : IsLinearizedMap (pullbackLinearization hj L) (pullbackLinearization hj K) (PullMap j u)) :
    PullMap (actionGraphMap j) (L.iso.hom ≫ PullMap a.smul u) =
      PullMap (actionGraphMap j) (PullMap (snd T.X X) u ≫ K.iso.hom) := by
  let w := (actionGraphMap j : T.X ⊗ Y ⟶ T.X ⊗ X)
  let hp := actionGraphMap_snd j (T := T)
  let hq := hj.symm
  let θ := evalPullIso L.iso w hp hq
  let κ := evalPullIso K.iso w hp hq
  let p := snd T.X Y
  let q := b.smul
  change (pullComp F p j).hom ≫ θ.hom ≫ (pullComp F q j).inv ≫ PullMap q (PullMap j u) =
    PullMap p (PullMap j u) ≫ (pullComp G p j).hom ≫ κ.hom ≫ (pullComp G q j).inv at hu
  have hinv := pullComp_inv_naturality q j u
  have hhom := pullComp_naturality p j u
  rw [hinv, ← reassoc_of% hhom] at hu
  have h := (cancel_epi (pullComp F p j).hom).mp hu
  have he : θ.hom ≫ PullMap (q ≫ j) u = PullMap (p ≫ j) u ≫ κ.hom := by
    apply (cancel_mono (pullComp G q j).inv).mp
    simpa only [Category.assoc] using h
  exact evaluated_equivariance L.iso K.iso u w hp hq he

set_option backward.isDefEq.respectTransparency false in
/-- The adjoint of an equivariant map into the open sheaf is equivariant for
the direct-image linearization compatible with the counit. -/
theorem linearized_adjoint_of_flatBaseChange [IsOpenImmersion j.left] [QuasiCompact j.left]
    (hbc : FlatOpenBaseChange.{u}) (hj : IsEquivariantMap a b j) {F : X.left.Modules} {H : Y.left.Modules}
    (hH : H.IsQuasicoherent) (L : Linearization a F) (K : Linearization b H)
    (J : Linearization a (pushOpen j H))
    (hJ : PullbackLinearizationComparison j J K (openCounitIso j H))
    (u : Pull j F ⟶ H) (hu : IsLinearizedMap (pullbackLinearization hj L) K u) :
    IsLinearizedMap L J ((Scheme.Modules.pullbackPushforwardAdjunction j.left).homEquiv F H u) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction j.left
  let m := adj.homEquiv F H u
  let c := (openCounitIso j H).hom
  let L' := pullbackLinearization hj L
  let J' := pullbackLinearization hj J
  let P := Scheme.Modules.pullback (snd T.X Y).left
  let A := Scheme.Modules.pullback b.smul.left
  have hc : IsLinearizedMap J' K c := linearized_of_pullbackLinearizationComparison hj J K _ hJ
  have hmc : PullMap j m ≫ c = u := by
    have h := (adj.homEquiv F H).symm_apply_apply u
    rw [adj.homEquiv_counit] at h
    exact h
  have hm : IsLinearizedMap L' J' (PullMap j m) := by
    change J'.iso.hom ≫ A.map c = P.map c ≫ K.iso.hom at hc
    change L'.iso.hom ≫ A.map u = P.map u ≫ K.iso.hom at hu
    change L'.iso.hom ≫ A.map (PullMap j m) = P.map (PullMap j m) ≫ J'.iso.hom
    apply (cancel_mono (A.map c)).mp
    simp only [Category.assoc, ← A.map_comp, hc, ← P.map_comp_assoc, hmc]
    exact hu
  let w := (actionGraphMap j : T.X ⊗ Y ⟶ T.X ⊗ X)
  let : IsIso (openBaseChange j w a.smul b.smul hj.symm H) :=
    hbc j w a.smul b.smul hj.symm (actionSquare_isPullback hj) inferInstance inferInstance (actionFlat a) H hH
  exact openBaseChange_hom_ext j w a.smul b.smul hj.symm H _ _ (restricted_equivariance hj L J m hm)

end EquivariantAdjunction

/-- For an equivariant quasi-compact open immersion, the actual direct image
has an equivariant counit, and the adjunction sends equivariant maps to
equivariant maps. -/
theorem openDirectImageAdjunction : OpenDirectImageAdjunction.{u} := by
  intro k _ T X Y a b j _ _ _ hj H
  obtain ⟨L, hL⟩ := openPushforward_linearization_of_flatBaseChange (j := j)
    flatOpenBaseChange H.sheaf H.quasicoherent hj H.lin
  refine ⟨L, openCounitIso j H.sheaf, rfl, hL, ?_⟩
  intro F A K he f hf
  have hId : IsLinearizedMap (pullbackLinearization hj A) K (𝟙 (Pull j F)) :=
    linearized_of_pullbackLinearizationComparison hj A K (Iso.refl _) he
  exact linearized_adjoint_of_flatBaseChange flatOpenBaseChange hj H.quasicoherent
    A H.lin L hL f (by simpa only [Category.id_comp] using linearizedMap_comp hId hf)

/-- A coherent equivariant subobject of the open pullback extends inside the
given quasi-coherent equivariant sheaf. -/
theorem subobjectExtension : SubobjectExtension.{u} :=
  subobjectExtensionFromAdjunction openDirectImageAdjunction

/-- A coherent equivariant sheaf extends along the invariant open immersion. -/
theorem coherentExtension : CoherentExtension.{u} := by
  apply coherentExtension_of_subobjectExtension subobjectExtension
  intro k _ T X Y a b j _ setting H
  let : LocallyOfFiniteType X.hom := setting.finiteType
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := setting.compact
  let : IsNoetherian X.left := AlgebraicGeometry.IsNoetherian.mk
  let : NoetherianSpace Y.left := j.left.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  exact openPushforward_linearization_of_flatBaseChange flatOpenBaseChange H.sheaf
    H.coherent.exists_quasicoherentData.choose.isQuasicoherent setting.equivariant H.lin

/-- A short exact sequence extends with its maps and equivariant
identifications on the open. -/
theorem shortExactExtension : ShortExactExtension.{u} := by
  apply shortExactExtension_of_extensions coherentExtension subobjectExtension
  intro k _ T X a _ F G f hf
  exact cokernelLinearization F.lin G.lin f hf

/-- Two extensions agree modulo classes supported on the complement. The
comparison extends the prescribed graph in their direct sum. -/
theorem graphComparison : GraphComparison.{u} :=
  graphComparison_of_subobjectExtension subobjectExtension

end

end LinearAlgebraicGroups.Representation.EquivariantCoherentOpenExtension
