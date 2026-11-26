import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v w v₁ v₂

namespace LinearAlgebraicGroups.FlatCohomology

abbrev OverRing (R : Type u) [CommRing R] := Over (Spec (CommRingCat.of R))

variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]

def groundRingHom (X : OverRing A) : A →+* Γ(X.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ X.hom.appTop).hom

def sections (X : OverRing A) : X.left.Modules ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation X.left.ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars (groundRingHom X)

instance (X : OverRing A) : (sections X).Additive where
  map_add := by intros; ext x; rfl

instance (X : OverRing A) : PreservesFiniteLimits (sections X) := by
  let evalLimits : PreservesFiniteLimits
      (SheafOfModules.evaluation.{u} X.left.ringCatSheaf (op ⊤)) := inferInstance
  let restrictLimits : PreservesFiniteLimits
      (ModuleCat.restrictScalars.{u,u,u} (groundRingHom X)) := inferInstance
  exact @comp_preservesFiniteLimits _ _ _ _ _ _
    (SheafOfModules.evaluation.{u} X.left.ringCatSheaf (op ⊤))
    (ModuleCat.restrictScalars.{u,u,u} (groundRingHom X)) evalLimits restrictLimits

abbrev cohomology (X : OverRing A) (n : ℕ) := (sections X).rightDerived n

variable {X : OverRing A} {Y : OverRing B} {Z : OverRing D}

private theorem groundRingHom_over (φ : A →+* B) (f : Y.left ⟶ X.left)
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) :
    f.appTop.hom.comp (groundRingHom X) = (groundRingHom Y).comp φ := by
  have h := congrArg Scheme.Hom.appTop w
  simp only [Scheme.Hom.comp_appTop] at h
  change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ X.hom.appTop ≫ f.appTop).hom =
    (CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ Y.hom.appTop).hom
  rw [h, Scheme.ΓSpecIso_inv_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Sections of the direct image, with their scalar actions compared. -/
def sectionsPushforward (φ : A →+* B) (f : Y.left ⟶ X.left)
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) :
    Scheme.Modules.pushforward f ⋙ sections X ≅
      sections Y ⋙ ModuleCat.restrictScalars.{u} φ :=
  NatIso.ofComponents (fun M =>
    (ModuleCat.restrictScalarsComp'App (groundRingHom X) f.appTop.hom
      (f.appTop.hom.comp (groundRingHom X)) rfl (M.val.obj (op ⊤))).symm ≪≫
    ModuleCat.restrictScalarsComp'App φ (groundRingHom Y)
      (f.appTop.hom.comp (groundRingHom X)) (groundRingHom_over φ f w)
      (M.val.obj (op ⊤))) (by
    intro M N g
    apply ModuleCat.hom_ext
    ext x
    rfl)

abbrev onCochains {C : Type v} {E : Type w} [Category.{v₁} C] [Category.{v₂} E]
    [HasZeroMorphisms C] [HasZeroMorphisms E] (F : C ⥤ E) [F.PreservesZeroMorphisms] :=
  F.mapHomologicalComplex (ComplexShape.up ℕ)

abbrev restrict (φ : A →+* B) := ModuleCat.restrictScalars.{u} φ

def sectionsPushforwardComplex (φ : A →+* B) (f : Y.left ⟶ X.left)
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (J : CochainComplex Y.left.Modules ℕ) :
    (onCochains (sections X)).obj ((onCochains (Scheme.Modules.pushforward f)).obj J) ≅
      (onCochains (restrict φ)).obj ((onCochains (sections Y)).obj J) :=
  ((Functor.mapHomologicalComplexCompIso
    (sectionsPushforward φ f w) (.up ℕ)) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (sections Y ⋙ restrict φ)) (.up ℕ)).symm).app J

/-- Restriction of scalars preserves the homology of cochains. -/
def restrictHomology (φ : A →+* B) (K : CochainComplex (ModuleCat.{u} B) ℕ) (n : ℕ) :
    ((onCochains (restrict φ)).obj K).homology n ≅ (restrict φ).obj (K.homology n) :=
  (K.sc n).mapHomologyIso (restrict φ)

def IsLift {F : X.left.Modules} {G : Y.left.Modules}
    (f : Y.left ⟶ X.left) (α : F ⟶ (Scheme.Modules.pushforward f).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (l : I.cocomplex ⟶ (onCochains (Scheme.Modules.pushforward f)).obj J.cocomplex) : Prop :=
  I.ι.f 0 ≫ l.f 0 = α ≫ (Scheme.Modules.pushforward f).map (J.ι.f 0)

def sectionsLift (φ : A →+* B) (f : Y.left ⟶ X.left)
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {I : CochainComplex X.left.Modules ℕ} {J : CochainComplex Y.left.Modules ℕ}
    (l : I ⟶ (onCochains (Scheme.Modules.pushforward f)).obj J) :
    (onCochains (sections X)).obj I ⟶
      (onCochains (restrict φ)).obj ((onCochains (sections Y)).obj J) :=
  (onCochains (sections X)).map l ≫ (sectionsPushforwardComplex φ f w J).hom

/-- The comparison is computed by every lift on every pair of injective resolutions. -/
def IsCohomologyMap (φ : A →+* B) (f : Y.left ⟶ X.left)
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {F : X.left.Modules} {G : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G) (n : ℕ)
    (m : (cohomology X n).obj F ⟶ (restrict φ).obj ((cohomology Y n).obj G)) : Prop :=
  ∀ (I : InjectiveResolution F) (J : InjectiveResolution G),
    (∃ l, IsLift f α I J l) ∧
    ∀ l, IsLift f α I J l →
      m = (I.isoRightDerivedObj (sections X) n).hom ≫
        HomologicalComplex.homologyMap (sectionsLift φ f w l) n ≫
        (restrictHomology φ ((onCochains (sections Y)).obj J.cocomplex) n).hom ≫
        (restrict φ).map (J.isoRightDerivedObj (sections Y) n).inv

def IsExactFlatPullback : Prop :=
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f], (Scheme.Modules.pullback f).PreservesHomology

def FlatPushforwardPreservesInjectives : Prop :=
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f],
    (Scheme.Modules.pushforward f).PreservesInjectiveObjects

def HasFlatCohomologyMap : Prop :=
  ∀ {A B : Type u} [CommRing A] [CommRing B] {X : OverRing A} {Y : OverRing B}
    (φ : A →+* B) (f : Y.left ⟶ X.left) [Flat f]
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {F : X.left.Modules} {G : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G) (n : ℕ),
    ∃! m, IsCohomologyMap φ f w α n m

theorem comp_over (φ : A →+* B) (ψ : B →+* D) (f : Y.left ⟶ X.left)
    (g : Z.left ⟶ Y.left)
    (wf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (wg : g ≫ Y.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom ψ)) :
    (g ≫ f) ≫ X.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [Category.assoc, wf, ← Category.assoc, wg, Category.assoc]
  exact congrArg (Z.hom ≫ ·) (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)).symm

def CohomologyMapComp : Prop :=
  ∀ {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    {X : OverRing A} {Y : OverRing B} {Z : OverRing D}
    (φ : A →+* B) (ψ : B →+* D) (f : Y.left ⟶ X.left) (g : Z.left ⟶ Y.left)
    [Flat f] [Flat g]
    (wf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (wg : g ≫ Y.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom ψ))
    {F : X.left.Modules} {G : Y.left.Modules} {H : Z.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G)
    (β : G ⟶ (Scheme.Modules.pushforward g).obj H) (n : ℕ)
    {m₁ m₂},
    IsCohomologyMap φ f wf α n m₁ → IsCohomologyMap ψ g wg β n m₂ →
    IsCohomologyMap (ψ.comp φ) (g ≫ f) (comp_over φ ψ f g wf wg)
      (α ≫ (Scheme.Modules.pushforward f).map β ≫
        (Scheme.Modules.pushforwardComp g f).hom.app H) n
      (m₁ ≫ (restrict φ).map m₂ ≫ (ModuleCat.restrictScalarsComp φ ψ).inv.app _)

def CohomologyMapId : Prop :=
  ∀ {A : Type u} [CommRing A] (X : OverRing A) {F G : X.left.Modules}
    (α : F ⟶ G) (n : ℕ),
    IsCohomologyMap (RingHom.id A) (𝟙 X.left) (by simp)
      (α ≫ (Scheme.Modules.pushforwardId X.left).inv.app G) n
      ((cohomology X n).map α ≫
        (ModuleCat.restrictScalarsId'App (RingHom.id A) rfl ((cohomology X n).obj G)).inv)

section Affine

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

set_option backward.isDefEq.respectTransparency false in
def affinePushforwardSections :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ restrict φ.hom :=
  NatIso.ofComponents (fun M =>
    (ModuleCat.restrictScalarsComp'App (Scheme.ΓSpecIso R).inv.hom (Spec.map φ).appTop.hom
      ((Spec.map φ).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) rfl (M.val.obj (op ⊤))).symm ≪≫
    ModuleCat.restrictScalarsComp'App φ.hom (Scheme.ΓSpecIso S).inv.hom
      ((Spec.map φ).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)
      (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality φ).symm) (M.val.obj (op ⊤))) (by
    intro M N f
    apply ModuleCat.hom_ext
    ext x
    rfl)

def AffinePullback : Prop :=
  ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S),
    ∃ e : tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
        ModuleCat.extendScalars.{u,u,u} φ.hom ⋙ tilde.functor S,
      ∀ M,
        (tilde.adjunction (R := R)).homEquiv _ _
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv
            _ _ (e.hom.app M)) =
        (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
          ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) ≫
          (affinePushforwardSections φ).inv.app _

end Affine

abbrev scalarExtensionProjection (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (X : OverRing k) :
    (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k R)))) ⟶ X.left :=
  pullback.fst _ _

def FlatScalarExtension : Prop :=
  ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] (X : OverRing k),
    Flat (scalarExtensionProjection k R X)

abbrev scalarExtension (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (X : OverRing k) : OverRing R :=
  Over.mk (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k R))))

theorem scalarExtension_over (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (X : OverRing k) :
    scalarExtensionProjection k R X ≫ X.hom = (scalarExtension k R X).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) :=
  pullback.condition

/-- The scalar extension of cohomology maps to the cohomology of the
pulled-back coefficients, with adjoint computed by every cochain lift. -/
def HasScalarExtensionCohomologyMap : Prop :=
  ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] (X : OverRing k)
    (F : X.left.Modules) (n : ℕ),
    let Y : OverRing R := scalarExtension k R X
    let p : Y.left ⟶ X.left := scalarExtensionProjection k R X
    let a := Scheme.Modules.pullbackPushforwardAdjunction p
    let H : ModuleCat.{u} k := (cohomology X n).obj F
    let H' : ModuleCat.{u} R := (cohomology Y n).obj ((Scheme.Modules.pullback p).obj F)
    ∃! m : (ModuleCat.extendScalars.{u,u,u} (algebraMap k R)).obj H ⟶ H',
      IsCohomologyMap (X := X) (Y := Y) (algebraMap k R) p
        (scalarExtension_over k R X) (a.unit.app F) n
        ((ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv H H' m)

end LinearAlgebraicGroups.FlatCohomology
