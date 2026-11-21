import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.SheafCohomology (resolutionModelMap)
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
universe a m u v r s w t

set_option quotPrecheck false
set_option linter.checkUnivs false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace AdvancedHomologicalAlgebra.HigherDirectImagesOriginalTheory

/-- Inverse image on opens, with independent universes for the two spaces. -/
def inverseOpens {X : TopCat.{u}} {Y : TopCat.{v}} (f : C(X, Y)) : Opens Y ⥤ Opens X where
  obj V := ⟨f ⁻¹' (V : Set Y), V.isOpen.preimage f.continuous⟩
  map i := homOfLE (fun _ hx ↦ i.le hx)

instance {X : TopCat.{u}} {Y : TopCat.{v}} (f : C(X, Y)) :
    RepresentablyFlat (inverseOpens f) := by
  constructor
  intro U
  refine @IsCofiltered.mk _ _ ?_ ?_
  · constructor
    · intro V W
      exact ⟨⟨⟨PUnit.unit⟩, V.right ⊓ W.right, homOfLE (le_inf V.hom.le W.hom.le)⟩,
        StructuredArrow.homMk (homOfLE inf_le_left),
        StructuredArrow.homMk (homOfLE inf_le_right), trivial⟩
    · exact fun _ _ _ _ ↦ ⟨_, 𝟙 _, by simp [eq_iff_true_of_subsingleton]⟩
  · exact ⟨StructuredArrow.mk (show U ⟶ (inverseOpens f).obj ⊤ from homOfLE le_top)⟩

instance {X : TopCat.{u}} {Y : TopCat.{v}} (f : C(X, Y)) :
    (inverseOpens f).IsContinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := by
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
  constructor
  intro U T hT x hx
  obtain ⟨V, i, hi, hxV⟩ := hT (f x) hx
  exact ⟨_, (inverseOpens f).map i, ⟨_, _, 𝟙 _, hi, Subsingleton.elim _ _⟩, hxV⟩

/-- A map of ringed spaces, with the actual maps on the original section rings. -/
structure RingedMap {X : TopCat.{u}} {Y : TopCat.{v}}
    (R : X.Sheaf RingCat.{r}) (S : Y.Sheaf RingCat.{s}) where
  continuousMap : C(X, Y)
  scalars (V : (Opens Y)ᵒᵖ) :
    S.obj.obj V →+* R.obj.obj ((inverseOpens continuousMap).op.obj V)
  naturality {V W : (Opens Y)ᵒᵖ} (i : V ⟶ W) :
    (R.obj.map ((inverseOpens continuousMap).op.map i)).hom.comp (scalars V) =
      (scalars W).comp (S.obj.map i).hom

variable {X : TopCat.{u}} {Y : TopCat.{v}} {Z : TopCat.{w}}
variable {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} {T : Z.Sheaf RingCat.{t}}
variable (f : RingedMap R S)

abbrev invOpen (V : Opens Y) : Opens X := (inverseOpens f.continuousMap).obj V

/-- Restrict scalars on sections over an inverse-image open. -/
abbrev sectionScalars (V : Opens Y) :=
  ModuleCat.restrictScalars.{m} (f.scalars (op V))

private def directImageObj (M : SheafOfModules.{m} R) : SheafOfModules.{m} S :=
  { val := by
      let F := inverseOpens f.continuousMap
      let P := F.op ⋙ M.val.presheaf
      letI (V : (Opens Y)ᵒᵖ) : Module (S.obj.obj V) (P.obj V) :=
        Module.compHom (M.val.obj (F.op.obj V)) (f.scalars V)
      exact PresheafOfModules.ofPresheaf P (fun {V W} i c x ↦ by
        change M.val.map (F.op.map i)
            (f.scalars V c • (show M.val.obj (F.op.obj V) from x)) =
          f.scalars W (S.obj.map i c) • M.val.map (F.op.map i) x
        rw [M.val.map_smul]
        exact congrArg (fun d : R.obj.obj (F.op.obj W) ↦ d • M.val.map (F.op.map i) x)
          (DFunLike.congr_fun (f.naturality i) c))
    isSheaf := Functor.op_comp_isSheaf _ _ _ ⟨_, M.isSheaf⟩ }

/-- Pushforward on the original sites and rings, at any coefficient size. -/
def directImageValue : SheafOfModules.{m} R ⥤ SheafOfModules.{m} S where
  obj := directImageObj f
  map {M N} g := ⟨PresheafOfModules.homMk
    (M₁ := (directImageObj f M).val) (M₂ := (directImageObj f N).val)
    (whiskerLeft (inverseOpens f.continuousMap).op ((PresheafOfModules.toPresheaf R.obj).map g.val))
    (fun V c x ↦ (g.val.app _).hom.map_smul (f.scalars V c) x)⟩
  map_id _ := by ext V x; rfl
  map_comp _ _ := by ext V x; rfl

instance : (directImageValue.{m} f).Additive where
  map_add := by intros; ext V x; rfl

set_option hygiene false in
local notation "Source" => AmbientSheaves.{max a v s} R
set_option hygiene false in
local notation "Target" => AmbientSheaves.{max a u r} S
set_option hygiene false in
local notation "TargetPresheaves" => AmbientPresheaves.{max a u r} S

abbrev ambientDirectImage : Source ⥤ Target := directImageValue f

/-- The same continuous map between the raised spaces. -/
def transportedMap :
    liftedSpace.{max a u v r s} X ⟶ liftedSpace.{max a u v r s} Y :=
  TopCat.ofHom ⟨fun x ↦ ULift.up (f.continuousMap x.down),
    continuous_uliftUp.comp (f.continuousMap.continuous.comp continuous_uliftDown)⟩

set_option hygiene false in
local notation "liftedSourceRing" => liftedRing.{max a v s} R
set_option hygiene false in
local notation "liftedTargetRing" => liftedRing.{max a u r} S

/-- The original scalar maps written in the lifted ring carriers. -/
def transportedScalars :
    liftedTargetRing ⟶
      (TopCat.Sheaf.pushforward RingCat (transportedMap.{a} f)).obj
        liftedSourceRing where
  hom.app V := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((f.scalars (op (opensEquiv Y V.unop))).comp ULift.ringEquiv.toRingHom))
  hom.naturality V W i := by
    ext c
    exact congrArg ULift.up (DFunLike.congr_fun
      (f.naturality ((opensEquiv Y).equivalence.functor.op.map i)).symm c.down)

abbrev transportedDirectImage :=
  AdvancedHomologicalAlgebra.HigherDirectImageLocalTheory.directImage
    liftedSourceRing
    liftedTargetRing
    (transportedMap.{a} f) (transportedScalars.{a} f)

end AdvancedHomologicalAlgebra.HigherDirectImagesOriginalTheory

namespace AdvancedHomologicalAlgebra.HigherDirectImagesOriginalTheory

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} {Y : TopCat.{v}} {Z : TopCat.{w}}
variable {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} {T : Z.Sheaf RingCat.{t}}
variable (f : RingedMap R S)

set_option hygiene false in
local notation "A" => AmbientSheaves.{max a v s} R
set_option hygiene false in
local notation "B" => AmbientSheaves.{max a u r} S
set_option hygiene false in
local notation "P" => AmbientPresheaves.{max a u r} S

abbrev presheafSections : A ⥤ P :=
  ambientDirectImage.{a} f ⋙ SheafOfModules.forget S

/-- Sheafification on the original target site. -/
abbrev associate : P ⥤ B := by
  letI := sectionHasSheafify.{max a u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
  exact PresheafOfModules.sheafification.{max a u v r s} (𝟙 S.obj)

instance : (associate.{a,u,v,r,s} (S := S)).Additive := by
  letI := sectionHasSheafify.{max a u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
  let H := associate.{a,u,v,r,s} (S := S)
  letI : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

variable [EnoughInjectives A]

/-- The original higher direct image, on the adequate category over the original ring. -/
def higherValue (q : ℕ) : A ⥤ B := by
  letI := sectionHasSheafify.{max a v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
  letI := sectionHasSheafify.{max a u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
  exact rightValue (ambientDirectImage.{a} f) q

/-- The local-cohomology presheaf, with its linear restriction maps, natural in
the original coefficient. Its resolution and restriction formulas are bound below. -/
def localPresheafValue (q : ℕ) : A ⥤ P := by
  letI := sectionHasSheafify.{max a v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
  letI := sectionHasSheafify.{max a u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
  exact rightValue (presheafSections.{a} f) q

def originalHigherValue [EnoughInjectives (AmbientSheaves.{max a m v s} R)] (q : ℕ) :
    SheafOfModules.{m} R ⥤ SheafOfModules.{max a m u v r s} S :=
  liftSheafCoefficients.{max a u v r s,u,r,m} R ⋙ higherValue.{max a m} f q

abbrev evaluateLocal (V : Opens Y) : P ⥤ SectionModules.{max a u r} S V :=
  PresheafOfModules.evaluation S.obj (op V)

abbrev localValue (V : Opens Y) (q : ℕ) :
    A ⥤ SectionModules.{max a u r} S V :=
  cohomologyValue.{max a v s} R (invOpen f V) q ⋙ sectionScalars.{max a u v r s} f V

/-- The two paths for restricting the scalar action along an inclusion of
target opens agree by naturality of the original structure-sheaf map. -/
def restrictionScalarsIso {V W : Opens Y} (j : W ⟶ V) :
    restrictSectionScalars.{max a v s} X R ((inverseOpens f.continuousMap).map j) ⋙
        sectionScalars.{max a u v r s} f V ≅
      sectionScalars.{max a u v r s} f W ⋙ restrictSectionScalars.{max a u r} Y S j := by
  let α := f.scalars (op V)
  let β := (R.obj.map ((inverseOpens f.continuousMap).map j).op).hom
  let γ := (S.obj.map j.op).hom
  let δ := f.scalars (op W)
  exact (ModuleCat.restrictScalarsComp α β).symm ≪≫
    ModuleCat.restrictScalarsCongr (f.naturality j.op) ≪≫
    ModuleCat.restrictScalarsComp γ δ

/-- The original section cohomology restriction, expressed over the target
section rings. The parameter is the HA-H01-Carrier restriction map. -/
def localRestrictionOf {V W : Opens Y} (j : W ⟶ V) (q : ℕ)
    (k : cohomologyValue.{max a v s} R (invOpen f V) q ⟶
      cohomologyValue.{max a v s} R (invOpen f W) q ⋙
        restrictSectionScalars.{max a v s} X R ((inverseOpens f.continuousMap).map j)) :
    localValue.{a} f V q ⟶ localValue.{a} f W q ⋙ restrictSectionScalars.{max a u r} Y S j :=
  whiskerRight k (sectionScalars f V) ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft _ (restrictionScalarsIso.{a} f j).hom ≫ (Functor.associator _ _ _).inv

/-- The pointwise homology identification on the very same resolution. -/
def evaluationModelIso (I : CochainComplex A ℤ) (V : Opens Y) (q : ℕ) :
    (evaluateLocal.{a,u,v,r,s} (S := S) V).obj
      (((presheafSections.{a} f).mapHomologicalComplex (.up ℤ)).obj I |>.homology (q : ℤ)) ≅
    (sectionScalars.{max a u v r s} f V).obj
      (((sectionsValue.{max a v s} R (invOpen f V)).mapHomologicalComplex (.up ℤ)).obj I
        |>.homology (q : ℤ)) := by
  let E := evaluateLocal.{a,u,v,r,s} (S := S) V
  let K := ((presheafSections.{a} f).mapHomologicalComplex (.up ℤ)).obj I
  let L := ((sectionsValue.{max a v s} R (invOpen f V)).mapHomologicalComplex (.up ℤ)).obj I
  let H := sectionScalars.{max a u v r s} f V
  exact ((K.sc (q : ℤ)).mapHomologyIso E).symm ≪≫
    (show ((E.mapHomologicalComplex (.up ℤ)).obj K).homology (q : ℤ) ≅
      ((H.mapHomologicalComplex (.up ℤ)).obj L).homology (q : ℤ) from Iso.refl _) ≪≫
    (L.sc (q : ℤ)).mapHomologyIso H

/-- Exact sheafification of the presheaf cohomology of the pushed resolution. -/
def sheafModelIso (I : CochainComplex A ℤ) (q : ℕ) :
    (associate.{a,u,v,r,s} (S := S)).obj
      (((presheafSections.{a} f).mapHomologicalComplex (.up ℤ)).obj I |>.homology (q : ℤ)) ≅
    (( (ambientDirectImage.{a} f).mapHomologicalComplex (.up ℤ)).obj I).homology (q : ℤ) := by
  letI := sectionHasSheafify.{max a v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
  letI := sectionHasSheafify.{max a u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
  let D := ambientDirectImage.{a} f
  let H := associate.{a,u,v,r,s} (S := S)
  let K := ((presheafSections.{a} f).mapHomologicalComplex (.up ℤ)).obj I
  let c : (D ⋙ SheafOfModules.forget S) ⋙ H ≅ D :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft D (asIso (PresheafOfModules.sheafificationAdjunction.{max a u v r s} (𝟙 S.obj)).counit) ≪≫
      Functor.rightUnitor _
  exact ((K.sc (q : ℤ)).mapHomologyIso H).symm ≪≫
    (HomologicalComplex.homologyFunctor B (.up ℤ) (q : ℤ)).mapIso
      ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).app I)

end AdvancedHomologicalAlgebra.HigherDirectImagesOriginalTheory

namespace Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients

open AdvancedHomologicalAlgebra.HigherDirectImagesOriginalTheory

attribute [local instance] HasDerivedCategory.standard
set_option linter.checkUnivs false

variable {X : TopCat.{u}} {Y : TopCat.{v}} {Z : TopCat.{w}}
variable {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} {T : Z.Sheaf RingCat.{t}}

set_option hygiene false in
local notation "A" => AmbientSheaves.{max a v s} R
set_option hygiene false in
local notation "B" => AmbientSheaves.{max a u r} S

def directImageType :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}},
    RingedMap R S → SheafOfModules.{m} R ⥤ SheafOfModules.{m} S

def directImageExpected : directImageType.{m,u,v,r,s} := @directImageValue.{m,u,v,r,s}

def higherType :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    [EnoughInjectives A], RingedMap R S → ℕ → A ⥤ B

def higherExpected : higherType.{a,u,v,r,s} :=
  fun {_ _ _ _} _ f q ↦ higherValue.{a} f q

def originalHigherType :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    [EnoughInjectives (AmbientSheaves.{max a m v s} R)], RingedMap R S → ℕ →
      SheafOfModules.{m} R ⥤ SheafOfModules.{max a m u v r s} S

def originalHigherExpected : originalHigherType.{a,m,u,v,r,s} :=
  fun {_ _ _ _} _ f q ↦ originalHigherValue.{a,m} f q

def localPresheafType :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    [EnoughInjectives A], RingedMap R S → ℕ → A ⥤ AmbientPresheaves.{max a u r} S

def localPresheafExpected : localPresheafType.{a,u,v,r,s} :=
  fun {_ _ _ _} _ f q ↦ localPresheafValue.{a} f q

/-- All ordinary section operations use the original inverse-image open and
ring map, including coefficient morphisms. -/
def sectionsType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S) {M N : SheafOfModules.{m} R} (k : M ⟶ N)
    {V W : Opens Y} (j : W ⟶ V) (c : S.obj.obj (op V))
    (x : M.val.obj (op (invOpen f V))),
    let D := directImageValue.{m} f
    (show (D.obj M).val.obj (op V) from x) = x ∧
    (c • (show (D.obj M).val.obj (op V) from x)) =
      (show (D.obj M).val.obj (op V) from f.scalars (op V) c • x) ∧
    (D.obj M).val.map j.op x = M.val.map ((inverseOpens f.continuousMap).map j).op x ∧
    (D.map k).val.app (op V) x = k.val.app (op (invOpen f V)) x

def leftExactType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S), PreservesFiniteLimits (directImageValue.{m} f)

def coefficientLiftType :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S), directImageValue.{m} f ⋙ liftSheafCoefficients.{a,v,s,m} S ≅
      liftSheafCoefficients.{a,u,r,m} R ⋙ directImageValue.{max a m} f

def coefficientLiftComparisonValue : coefficientLiftType.{a,m,u,v,r,s} := by
  intro X Y R S f
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget S).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ ?_) (fun {V W} j ↦ ?_))) ?_
  · let P := ((directImageValue.{m} f ⋙ liftSheafCoefficients.{a,v,s,m} S).obj M).val.obj V
    let Q := ((liftSheafCoefficients.{a,u,r,m} R ⋙ directImageValue.{max a m} f).obj M).val.obj V
    let e : (P : Type (max a m)) ≃ₗ[S.obj.obj V] (Q : Type (max a m)) :=
      { toAddEquiv := AddEquiv.refl _, map_smul' := fun _ _ ↦ rfl }
    exact e.toModuleIso
  · ext x
    rfl
  · intro M N k
    ext V x
    rfl

def coefficientLiftComparisonExpected : coefficientLiftType.{a,m,u,v,r,s} :=
  @coefficientLiftComparisonValue.{a,m,u,v,r,s}

def coefficientLiftNormalizedType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S) (M : SheafOfModules.{m} R) (V : Opens Y)
    (x : M.val.obj (op (invOpen f V))),
    ((coefficientLiftComparisonExpected.{a,m,u,v,r,s} f).hom.app M).val.app (op V) (ULift.up x) = ULift.up x

def pushforwardTransportType :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S), ambientDirectImage.{a} f ⋙ transport.{max a u r} S ≅
      transport.{max a v s} R ⋙ transportedDirectImage.{a} f

def pushforwardTransportExpected : pushforwardTransportType.{a,u,v,r,s} := by
  intro X Y R S f
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ ?_) (fun {V W} j ↦ ?_))) ?_
  · exact (show _ ≃ₗ[(liftedRing.{max a u r} S).obj.obj V] _ from
      { toAddEquiv := AddEquiv.refl _, map_smul' := fun _ _ ↦ rfl }).toModuleIso
  · ext x
    rfl
  · intro M N k
    ext V x
    rfl

def pushforwardTransportNormalizedType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S) (M : A) (V : Opens (liftedSpace.{max a u v r s} Y))
    (x : M.val.obj (op (invOpen f (opensEquiv Y V)))),
    ((pushforwardTransportExpected.{a,u,v,r,s} f).hom.app M).val.app (op V) x = x ∧
    ∀ c : S.obj.obj (op (opensEquiv Y V)),
      (transportedScalars.{a} f).hom.app (op V) (sectionRingEquiv.{max a u r} S V c) =
        sectionRingEquiv.{max a v s} R ((Opens.map (transportedMap.{a} f)).obj V)
          (f.scalars (op (opensEquiv Y V)) c)

def higherTransportType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    [EnoughInjectives A]
    [EnoughInjectives (AdvancedHomologicalAlgebra.SheafTheory.Modules (liftedRing.{max a v s} R))]
    [(transport.{max a u r} S).IsEquivalence] (f : RingedMap R S),
    letI := sectionHasSheafify.{max a v r s,u} X
    letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
    letI := sectionHasSheafify.{max a u r s,v} Y
    letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
    ResolutionComparison (ambientDirectImage.{a} f) (transportedDirectImage.{a} f)
      (transport.{max a v s} R) (transport.{max a u r} S) (pushforwardTransportExpected.{a,u,v,r,s} f)

def sheafificationType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    [EnoughInjectives A] (f : RingedMap R S),
    letI := sectionHasSheafify.{max a v r s,u} X
    letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
    letI := sectionHasSheafify.{max a u r s,v} Y
    letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
    ∃ e : ∀ q : ℕ, localPresheafValue.{a} f q ⋙ associate.{a,u,v,r,s} ≅ higherValue.{a} f q,
      ∀ (M : A) (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
        (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i),
        (∀ k : ℤ, Injective (I.X k)) → ∀ q : ℕ,
        (associate.{a,u,v,r,s} (S := S)).map
            (resolutionModelMap (presheafSections.{a} f) i hi q) ≫ (e q).hom.app M =
          (sheafModelIso.{a} f I q).hom ≫
            resolutionModelMap (ambientDirectImage.{a} f) i hi q

/-- The comparison on the original coefficient is induced by each augmented
injective resolution of its lift to the adequate category. -/
def originalLocalDescriptionType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    [EnoughInjectives (AmbientSheaves.{max a m v s} R)] (f : RingedMap R S),
    letI := sectionHasSheafify.{max a m v r s,u} X
    letI := sectionWEqualsLocallyBijective.{max a m v r s,u} X
    letI := sectionHasSheafify.{max a m u r s,v} Y
    letI := sectionWEqualsLocallyBijective.{max a m u r s,v} Y
    let J := liftSheafCoefficients.{max a u v r s,u,r,m} R
    let C := AmbientSheaves.{max a m v s} R
    let H := associate.{max a m,u,v,r,s} (S := S)
    ∃ e : ∀ q : ℕ, J ⋙ (localPresheafValue.{max a m} f q ⋙ H) ≅ originalHigherValue.{a,m} f q,
      ∀ (M : SheafOfModules.{m} R) (I : CochainComplex C ℤ) [I.IsStrictlyGE 0]
        (i : (CochainComplex.singleFunctor C 0).obj (J.obj M) ⟶ I) (hi : QuasiIso i),
        (∀ k : ℤ, Injective (I.X k)) → ∀ q : ℕ,
        H.map (resolutionModelMap (presheafSections.{max a m} f) i hi q) ≫ (e q).hom.app M =
          (sheafModelIso.{max a m} f I q).hom ≫
            resolutionModelMap (ambientDirectImage.{max a m} f) i hi q

section LocalMaps

variable (f : RingedMap R S) [EnoughInjectives A]

abbrev EvaluationFamily :=
  ∀ (V : Opens Y) (q : ℕ),
    localPresheafValue.{a} f q ⋙ evaluateLocal.{a,u,v,r,s} V ≅ localValue.{a} f V q

def IsLocalEvaluation (e : EvaluationFamily.{a} f) : Prop := by
  letI := sectionHasSheafify.{max a v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
  exact ∀ (M : A) (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
        (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i),
        (∀ k : ℤ, Injective (I.X k)) → ∀ (V : Opens Y) (q : ℕ),
        (evaluateLocal.{a,u,v,r,s} (S := S) V).map
            (resolutionModelMap (presheafSections.{a} f) i hi q) ≫ (e V q).hom.app M =
          (evaluationModelIso.{a} f I V q).hom ≫ (sectionScalars.{max a u v r s} f V).map
            (resolutionModelMap (sectionsValue.{max a v s} R (invOpen f V)) i hi q)

abbrev SectionRestrictionFamily {V W : Opens Y} (j : W ⟶ V) :=
  ∀ q : ℕ, cohomologyValue.{max a v s} R (invOpen f V) q ⟶
    cohomologyValue.{max a v s} R (invOpen f W) q ⋙
      restrictSectionScalars.{max a v s} X R ((inverseOpens f.continuousMap).map j)

def IsSectionRestriction {V W : Opens Y} (j : W ⟶ V)
    (k : SectionRestrictionFamily.{a} f j) : Prop := by
  letI := sectionHasSheafify.{max a v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
  let Γ := sectionsValue.{max a v s} R (invOpen f V)
  let Γ' := sectionsValue.{max a v s} R (invOpen f W)
  let j' := (inverseOpens f.continuousMap).map j
  let H := restrictSectionScalars.{max a v s} X R j'
  exact ∀ (M : A) (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
      (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i),
      (∀ k : ℤ, Injective (I.X k)) → ∀ q : ℕ,
      resolutionModelMap Γ i hi q ≫ (k q).app M =
        HomologicalComplex.homologyMap
          (((restrictSections.{max a v s} X R j').mapHomologicalComplex (.up ℤ)).app I) (q : ℤ) ≫
        ((((Γ'.mapHomologicalComplex (.up ℤ)).obj I).sc (q : ℤ)).mapHomologyIso H).hom ≫
        H.map (resolutionModelMap Γ' i hi q)

end LocalMaps

def localEvaluationType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    [EnoughInjectives A] (f : RingedMap R S),
    ∃ e : EvaluationFamily.{a} f, IsLocalEvaluation.{a} f e

def localRestrictionsType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    [EnoughInjectives A] (f : RingedMap R S) (e : EvaluationFamily.{a} f),
    IsLocalEvaluation.{a} f e →
    ∀ {V W : Opens Y} (j : W ⟶ V),
      ∃ k : SectionRestrictionFamily.{a} f j, IsSectionRestriction.{a} f j k ∧
        ∀ (q : ℕ) (M : A),
          let P := (localPresheafValue.{a} f q).obj M
          let H := restrictSectionScalars.{max a u r} Y S j
          P.map j.op ≫ H.map ((e W q).hom.app M) =
            (e V q).hom.app M ≫ (localRestrictionOf.{a} f j q (k q)).app M

def adequateEnoughInjectivesType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}},
    RingedMap R S → EnoughInjectives A ∧ EnoughInjectives B

def pushforwardFlasqueType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S) (M : SheafOfModules.{m} R),
    IsFlasque R M → IsFlasque S ((directImageValue.{m} f).obj M)

def injectiveImageAcyclicType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    [EnoughInjectives B] (f : RingedMap R S) (I : A),
    Injective I → IsFlasque S ((ambientDirectImage.{a} f).obj I) ∧
      ∀ (V : Opens Y) (q : ℕ),
        IsZero ((cohomologyValue.{max a u r} S V (q + 1)).obj
          ((ambientDirectImage.{a} f).obj I))

def flasqueHigherVanishingType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    [EnoughInjectives A] (f : RingedMap R S) (M : A),
    IsFlasque R M → ∀ q : ℕ, IsZero ((higherValue.{a} f (q + 1)).obj M)

def relativeAcyclicType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {Z : TopCat.{w}}
    {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} {T : Z.Sheaf RingCat.{t}}
    [EnoughInjectives (AmbientSheaves.{max a u r w t} S)]
    (f : RingedMap R S) (g : RingedMap S T) (I : AmbientSheaves.{max a v s w t} R),
    Injective I → ∀ q : ℕ, IsZero ((higherValue.{max a u r} g (q + 1)).obj
      ((ambientDirectImage.{max a w t} f).obj I))

/-- The same relative vanishing as an isomorphism of the actual HA-R08 unit. -/
def relativeUnitIsoType : Prop :=
  ∀ {X : TopCat.{u}} {Y : TopCat.{v}} {Z : TopCat.{w}}
    {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} {T : Z.Sheaf RingCat.{t}}
    [EnoughInjectives (AmbientSheaves.{max a u r w t} S)]
    (f : RingedMap R S) (g : RingedMap S T) (I : AmbientSheaves.{max a v s w t} R),
    letI := sectionHasSheafify.{max a u r w t s,v} Y
    letI := sectionWEqualsLocallyBijective.{max a u r w t s,v} Y
    letI := sectionHasSheafify.{max a u r v s t,w} Z
    letI := sectionWEqualsLocallyBijective.{max a u r v s t,w} Z
    Injective I → Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison.rightAcyclicValue
      (ambientDirectImage.{max a u r} g) ((ambientDirectImage.{max a w t} f).obj I)

end Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients
