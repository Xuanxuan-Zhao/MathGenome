import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.AffineModuleSheaves

namespace DerivedFormalization.AffineModuleSheaves

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

open Specs.DerivedFormalization.AffineModuleSheaves (qcValue qcDerivedValue inclusion)

abbrev QC (A : CommRingCat.{u}) := qcValue A

abbrev affineEquiv (A : CommRingCat.{u}) : ModuleCat.{u} A ≌ QC A :=
  AlgebraicGeometry.tildeEquiv (R := A)

abbrev QCDerived (A : CommRingCat.{u}) := qcDerivedValue A

theorem affineEquiv_exact (A : CommRingCat.{u}) :
    PreservesFiniteLimits (affineEquiv A).functor ∧
    PreservesFiniteColimits (affineEquiv A).functor ∧
    PreservesFiniteLimits (affineEquiv A).inverse ∧
    PreservesFiniteColimits (affineEquiv A).inverse :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem tildeSectionsLocalized (A : CommRingCat.{u}) (M : ModuleCat.{u} A) (a : A) :
    IsLocalizedModule.Away a (tilde.toOpen M (PrimeSpectrum.basicOpen a)).hom :=
  inferInstance

theorem qcSectionsLocalized (A : CommRingCat.{u}) (F : QC A) (a : A) :
    IsLocalizedModule.Away a
      ((modulesSpecToSheaf.obj F.obj).obj.map (PrimeSpectrum.basicOpen a).leTop.op).hom := by
  exact (isIso_fromTildeΓ_iff_isLocalizing F.obj).mp
    ((isQuasicoherent_iff_isIso_fromTildeΓ F.obj).mp F.property) a

private theorem tilde_app_basicOpen_injective {A : CommRingCat.{u}}
    {M N : ModuleCat.{u} A} (f : M ⟶ N) [Mono f] (a : A) :
    Function.Injective ((modulesSpecToSheaf.map (tilde.map f)).hom.app
      (op (PrimeSpectrum.basicOpen a))) := by
  let U := PrimeSpectrum.basicOpen a
  let s := Submonoid.powers a
  let m := (tilde.toOpen M U).hom
  let n := (tilde.toOpen N U).hom
  have : IsLocalizedModule s m := tildeSectionsLocalized A M a
  have : IsLocalizedModule s n := tildeSectionsLocalized A N a
  let fU := (modulesSpecToSheaf.map (tilde.map f)).hom.app (op U)
  change Function.Injective fU.hom
  have heq : fU.hom = IsLocalizedModule.map s m n f.hom := by
    apply IsLocalizedModule.linearMap_ext s m n
    rw [IsLocalizedModule.map_comp]
    exact congrArg ModuleCat.Hom.hom (tilde.toOpen_map_app f U)
  rw [heq]
  exact IsLocalizedModule.map_injective s m n f.hom ((ModuleCat.mono_iff_injective f).mp ‹_›)

private theorem tilde_preservesMonomorphisms (A : CommRingCat.{u}) :
    (tilde.functor A).PreservesMonomorphisms := by
  constructor
  intro M N f hf
  let g := modulesSpecToSheaf.map (tilde.map f)
  apply (modulesSpecToSheaf (R := A)).mono_of_mono_map
  change Mono g
  apply (TopCat.Sheaf.forget _ _).mono_of_mono_map
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  apply (ModuleCat.mono_iff_injective _).mpr
  change Function.Injective (g.hom.app U)
  intro x y hxy
  apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj (tilde M)).property
  intro p hp
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hpa, ha : PrimeSpectrum.basicOpen a ≤ U.unop⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp U.unop.2
  refine ⟨_, ha, hpa, tilde_app_basicOpen_injective f a ?_⟩
  have hnat := g.hom.naturality (homOfLE ha).op
  calc
    _ = (modulesSpecToSheaf.obj (tilde N)).obj.map (homOfLE ha).op (g.hom.app U x) :=
      congr($(hnat).hom x)
    _ = (modulesSpecToSheaf.obj (tilde N)).obj.map (homOfLE ha).op (g.hom.app U y) :=
      congrArg ((modulesSpecToSheaf.obj (tilde N)).obj.map (homOfLE ha).op) hxy
    _ = _ := congr($(hnat).hom y).symm

/-- Exactness in the ambient category of sheaves of modules. -/
theorem tilde_exact (A : CommRingCat.{u}) :
    PreservesFiniteLimits (tilde.functor A) ∧ PreservesFiniteColimits (tilde.functor A) := by
  have := tilde_preservesMonomorphisms A
  have : (tilde.functor A).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact ⟨Functor.preservesFiniteLimits_of_preservesHomology _, inferInstance⟩

theorem preimageBasicOpen {A B : CommRingCat.{u}} (φ : A ⟶ B) (a : A) :
    (Opens.map (Spec.map φ).base).obj (PrimeSpectrum.basicOpen a) =
      PrimeSpectrum.basicOpen (φ a) :=
  PrimeSpectrum.comap_basicOpen φ.hom a

variable {A B : CommRingCat.{u}}

/-- Global sections of direct image carry the scalar action restricted along the ring map. -/
def pushforwardGammaIso (φ : A ⟶ B) :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := A) ≅
      moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars φ.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤))

theorem pushforwardGamma (φ : A ⟶ B) :
    Nonempty (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := A) ≅
      moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars φ.hom) :=
  ⟨pushforwardGammaIso φ⟩

theorem pushforwardPreservesQC (φ : A ⟶ B) (F : QC B) :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj F.obj).IsQuasicoherent := by
  have : IsIso (Scheme.Modules.fromTildeΓ F.obj) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ F.obj).mp F.property
  exact (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr
    (isIso_fromTildeΓ_pushforward φ F.obj)

private def pullbackTildeIso (φ : A ⟶ B) :
    tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor B :=
  ((tilde.adjunction (R := A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
      (pushforwardGammaIso φ) |>.leftAdjointUniq
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := B)))

theorem pullbackPreservesQC (φ : A ⟶ B) (F : QC A) :
    ((Scheme.Modules.pullback (Spec.map φ)).obj F.obj).IsQuasicoherent := by
  let e := (pullbackTildeIso φ).app ((moduleSpecΓFunctor (R := A)).obj F.obj)
  let c := (inclusion A).mapIso ((affineEquiv A).counitIso.app F)
  refine (SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf).prop_of_iso
    (e.symm ≪≫ (Scheme.Modules.pullback (Spec.map φ)).mapIso c) ?_
  exact ((affineEquiv B).functor.obj
    ((ModuleCat.extendScalars φ.hom).obj ((moduleSpecΓFunctor (R := A)).obj F.obj))).property

/-- The restriction of the scheme direct image to quasi-coherent modules. -/
abbrev qcPushforward (φ : A ⟶ B) : QC B ⥤ QC A :=
  ObjectProperty.lift (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf)
    (inclusion B ⋙ Scheme.Modules.pushforward (Spec.map φ)) (pushforwardPreservesQC φ)

/-- The restriction of scheme pullback to quasi-coherent modules. -/
abbrev qcPullback (φ : A ⟶ B) : QC A ⥤ QC B :=
  ObjectProperty.lift (SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf)
    (inclusion A ⋙ Scheme.Modules.pullback (Spec.map φ)) (pullbackPreservesQC φ)

def qcPushforwardGammaIso (φ : A ⟶ B) :
    qcPushforward φ ⋙ (affineEquiv A).inverse ≅
      (affineEquiv B).inverse ⋙ ModuleCat.restrictScalars φ.hom :=
  Functor.isoWhiskerLeft (inclusion B) (pushforwardGammaIso φ)

/-- Direct image written in module coordinates. -/
def qcPushforwardTransportIso (φ : A ⟶ B) :
    qcPushforward φ ≅
      ((affineEquiv B).inverse ⋙ ModuleCat.restrictScalars φ.hom) ⋙ (affineEquiv A).functor :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (affineEquiv A).counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (qcPushforwardGammaIso φ) _

/-- Direct image of a tilde sheaf is the tilde sheaf of the restricted module. -/
def qcPushforwardIso (φ : A ⟶ B) :
    (affineEquiv B).functor ⋙ qcPushforward φ ≅
      ModuleCat.restrictScalars φ.hom ⋙ (affineEquiv A).functor :=
  Functor.isoWhiskerLeft _ (qcPushforwardTransportIso φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (affineEquiv B).unitIso.symm _ ≪≫ Functor.leftUnitor _) _

instance (φ : A ⟶ B) : PreservesFiniteLimits (qcPushforward φ) :=
  preservesFiniteLimits_of_natIso (qcPushforwardTransportIso φ).symm

instance (φ : A ⟶ B) : PreservesFiniteColimits (qcPushforward φ) :=
  preservesFiniteColimits_of_natIso (qcPushforwardTransportIso φ).symm

instance (φ : A ⟶ B) : (qcPushforward φ).Additive :=
  Functor.additive_of_iso (qcPushforwardTransportIso φ).symm

/-- Pullback of a tilde sheaf is the tilde sheaf of the scalar extension. -/
def qcPullbackIso (φ : A ⟶ B) :
    (affineEquiv A).functor ⋙ qcPullback φ ≅
      ModuleCat.extendScalars φ.hom ⋙ (affineEquiv B).functor := by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ((pullbackTildeIso φ).app M)) ?_
  intro M N f
  exact ObjectProperty.hom_ext _ ((pullbackTildeIso φ).hom.naturality f)

theorem qcPushforwardComparison (φ : A ⟶ B) (h : ∀ F : QC B,
    ((Scheme.Modules.pushforward (Spec.map φ)).obj F.obj).IsQuasicoherent) :
    Nonempty ((affineEquiv B).functor ⋙
        ObjectProperty.lift (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf)
          (inclusion B ⋙ Scheme.Modules.pushforward (Spec.map φ)) h ≅
      ModuleCat.restrictScalars φ.hom ⋙ (affineEquiv A).functor) :=
  ⟨qcPushforwardIso φ⟩

theorem qcPullbackComparison (φ : A ⟶ B) (h : ∀ F : QC A,
    ((Scheme.Modules.pullback (Spec.map φ)).obj F.obj).IsQuasicoherent) :
    Nonempty ((affineEquiv A).functor ⋙
        ObjectProperty.lift (SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf)
          (inclusion A ⋙ Scheme.Modules.pullback (Spec.map φ)) h ≅
      ModuleCat.extendScalars φ.hom ⋙ (affineEquiv B).functor) :=
  ⟨qcPullbackIso φ⟩

attribute [local instance] HasDerivedCategory.standard

private def deriveIso {C E : Type*} [Category* C] [Category* E] [Abelian C] [Abelian E]
    {F G : C ⥤ E} [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) _ _ _ _
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q)

/-- Termwise tilde and global sections, localized at quasi-isomorphisms. -/
def derivedEquiv (A : CommRingCat.{u}) :
    DerivedCategory (ModuleCat.{u} A) ≌ QCDerived A :=
  let e := affineEquiv A
  CategoryTheory.Equivalence.mk e.functor.mapDerivedCategory e.inverse.mapDerivedCategory
    ((Functor.mapDerivedCategoryIdIso _).symm ≪≫ deriveIso e.unitIso ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
    (Functor.mapDerivedCategoryCompIso _ _ ≪≫ deriveIso e.counitIso ≪≫
      Functor.mapDerivedCategoryIdIso _)

theorem derivedEquivalence (A : CommRingCat.{u}) :
    ∃ e : DerivedCategory (ModuleCat.{u} A) ≌ QCDerived A,
      e.functor = (affineEquiv A).functor.mapDerivedCategory ∧
      e.inverse = (affineEquiv A).inverse.mapDerivedCategory ∧
      (affineEquiv A).functor.mapDerivedCategory.IsTriangulated ∧
      (affineEquiv A).inverse.mapDerivedCategory.IsTriangulated :=
  ⟨derivedEquiv A, rfl, rfl, inferInstance, inferInstance⟩

theorem derivedTildeFactors (A : CommRingCat.{u}) :
    Nonempty (DerivedCategory.Q ⋙ (affineEquiv A).functor.mapDerivedCategory ≅
      (affineEquiv A).functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
  ⟨Functor.mapDerivedCategoryFactors _⟩

theorem derivedGammaFactors (A : CommRingCat.{u}) :
    Nonempty (DerivedCategory.Q ⋙ (affineEquiv A).inverse.mapDerivedCategory ≅
      (affineEquiv A).inverse.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
  ⟨Functor.mapDerivedCategoryFactors _⟩

end

end DerivedFormalization.AffineModuleSheaves
