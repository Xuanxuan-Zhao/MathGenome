import Specs.LinearAlgebraicGroups.Arithmetic.IwahoriScalarCocycleComposition
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.IwahoriScalarCocycleComposition

open Specs.IwahoriScalarCocycleComposition
open Specs.ExceptionalAffineBruhat (FieldPoints scalarPoints)
open Specs.ExceptionalIwahoriCongruence (integralRing localIntegers localIntegersInclusion
  changeRingHom integralRingMap)
open Specs.IntegralSemisimpleModel (Model Integers integerAlgebra integralSpec IntegralPoints)
open Specs.Pinning (BasedRootDatum)

attribute [local instance] integerAlgebra

noncomputable section

private theorem genericPoint_dominant (K : Type u) [Field K] [ValuativeRel K] :
    IsSchemeTheoreticallyDominant (genericPoint K) := by
  let i := CommRingCat.ofHom (localIntegersInclusion K).hom.toRingHom
  let j := (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  let q := Scheme.ΓSpecIso (CommRingCat.of (localIntegers K))
  have h : i ≫ j = q.inv ≫ (genericPoint K).appTop := Scheme.ΓSpecIso_inv_naturality i
  have he : (genericPoint K).appTop = q.hom ≫ i ≫ j := by
    rw [h, Iso.hom_inv_id_assoc]
  have hi : Function.Injective (genericPoint K).appTop := by
    rw [he]
    exact (ConcreteCategory.bijective_of_isIso j).injective.comp
      (Subtype.val_injective.comp (ConcreteCategory.bijective_of_isIso q.hom).injective)
  constructor
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  exact (RingHom.injective_iff_ker_eq_bot ((genericPoint K).appTop.hom)).mp hi

/-- The generic fibre detects equality of morphisms from a flat scheme to an affine scheme. -/
private theorem genericRestrictionInjective {K : Type u} [Field K] [ValuativeRel K]
    {X : Over (integerScheme K)} {Y : Scheme.{u}} (hX : Flat X.hom) (hY : IsAffine Y)
    {f g : X.left ⟶ Y}
    (h : pullback.fst X.hom (genericPoint K) ≫ f = pullback.fst X.hom (genericPoint K) ≫ g) :
    f = g := by
  let j := pullback.fst X.hom (genericPoint K)
  let _ : IsSchemeTheoreticallyDominant (genericPoint K) := genericPoint_dominant K
  let _ : IsSchemeTheoreticallyDominant j :=
    IsSchemeTheoreticallyDominant.pullbackFst _ _
  apply ext_of_isAffine
  have h' := congrArg Scheme.Hom.appTop h
  change f.appTop ≫ j.appTop = g.appTop ≫ j.appTop at h'
  exact CommRingCat.hom_ext (RingHom.ext fun x =>
    j.app_injective ⊤ (ConcreteCategory.congr_hom h' x))


section GenericTests

variable {K : Type u} [Field K] [ValuativeRel K]

/-- The generic fibre of an affine scheme over the valuation ring is itself an
affine test over the fraction field. -/
private theorem genericFibre_hasUniversalTest (X : Over (integerScheme K)) (hX : IsAffine X.left) :
    ∃ (R : TestAlgebra K) (x : genericTest R ⟶ X)
      (i : (genericTest R).left ≅ pullback X.hom (genericPoint K)),
      x.left = i.hom ≫ pullback.fst X.hom (genericPoint K) := by
  let P := Over.pullback (genericPoint K)
  let Xη := P.obj X
  have hXη : IsAffine Xη.left := by
    change IsAffine (pullback X.hom (genericPoint K))
    exact isAffine_of_isAffineHom (pullback.snd X.hom (genericPoint K))
  obtain ⟨T, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of K)).mpr hXη
  let R : TestAlgebra K := T.unop
  let f := ((Over.mapPullbackAdj (genericPoint K)).homEquiv ((testSpec K).obj (op R)) X).symm e.hom
  let i := (Over.forget (Spec (CommRingCat.of K))).mapIso e
  exact ⟨R, f, i, rfl⟩

/-- Equality on all generic affine tests implies equality on the whole flat
affine source. The generic fibre itself supplies the universal test. -/
private theorem hom_ext_of_genericTests
    {X : Over (integerScheme K)} {T : Scheme.{u}}
    (hX : IsAffine X.left) (hflat : Flat X.hom) (hT : IsAffine T)
    {f g : X.left ⟶ T}
    (h : ∀ (R : TestAlgebra K) (x : genericTest R ⟶ X), x.left ≫ f = x.left ≫ g) :
    f = g := by
  obtain ⟨R, x, i, hi⟩ := genericFibre_hasUniversalTest X hX
  apply genericRestrictionInjective hflat hT
  rw [← cancel_epi i.hom]
  simpa only [← Category.assoc, ← hi] using h R x

end GenericTests

private abbrev specMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :=
  Spec.map (CommRingCat.ofHom f)

private theorem specMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    specMap (g.comp f) = specMap g ≫ specMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

section OverMaps

variable {S T : Scheme.{u}} (d : T ⟶ S) {X : Over T} {Y Z : Over S}

private abbrev absoluteMap (f : X ⟶ (Over.pullback d).obj Y) : X.left ⟶ Y.left :=
  f.left ≫ pullback.fst Y.hom d

private theorem absoluteMap_over (f : X ⟶ (Over.pullback d).obj Y) :
    absoluteMap d f ≫ Y.hom = X.hom ≫ d := by
  change (f.left ≫ pullback.fst Y.hom d) ≫ Y.hom = _
  calc
    _ = f.left ≫ pullback.snd Y.hom d ≫ d :=
      (Category.assoc _ _ _).trans (congrArg (f.left ≫ ·) pullback.condition)
    _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ d) (Over.w f))

private theorem absoluteMap_post (f : X ⟶ (Over.pullback d).obj Y) (g : Y ⟶ Z) :
    absoluteMap d (f ≫ (Over.pullback d).map g) =
      absoluteMap d f ≫ g.left := by
  change (f.left ≫ ((Over.pullback d).map g).left) ≫ pullback.fst Z.hom d =
    (f.left ≫ pullback.fst Y.hom d) ≫ g.left
  have h := Over.pullback_map_left (k := g) d Y
  calc
    _ = f.left ≫ ((Over.pullback d).map g).left ≫ pullback.fst Z.hom d := Category.assoc _ _ _
    _ = f.left ≫ pullback.fst Y.hom d ≫ g.left := by
      exact congrArg (f.left ≫ ·)
        ((congrArg (· ≫ pullback.fst Z.hom d) h).trans (pullback.lift_fst _ _ _))
    _ = _ := (Category.assoc _ _ _).symm

end OverMaps

section Model

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [ValuativeRel K]
  {E : BasedRootDatum.{u}} {M' : Model E} (H : IwahoriModel M' K)

local notation "O" => localIntegers K
local notation "modelGroup" => H.model
local notation "X" => H.model.X
set_option quotPrecheck false in
local notation "overMap" => H.model.X.hom
set_option quotPrecheck false in
local notation "S" => H.model.X.left

private theorem genericImage_left_injective
    {Q : Over (Spec (CommRingCat.of K))}
    {x y : (Over.map (genericPoint K)).obj Q ⟶ H.model.X}
    (h : x.left ≫ H.projection = y.left ≫ H.projection) : x = y := by
  let P := Over.pullback (genericPoint K)
  let A := Over.mapPullbackAdj (genericPoint K)
  let t := H.toIntegral.hom.hom
  have ht : IsIso (P.map t) := by
    let G := Specs.IwahoriScalarCocycleComposition.groupBaseChange (localIntegersInclusion K).hom.toRingHom
    have : IsIso (G.map H.toIntegral) := H.genericIso
    exact (Grp.forget _).map_isIso (G.map H.toIntegral)
  have he : x ≫ t = y ≫ t := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact h
    · exact (Over.w (x ≫ t)).trans (Over.w (y ≫ t)).symm
  apply (A.homEquiv Q H.model.X).injective
  apply (cancel_mono (P.map t)).mp
  exact (A.homEquiv_naturality_right x t).symm.trans
    ((congrArg (A.homEquiv Q _) he).trans (A.homEquiv_naturality_right y t))

private abbrev retest (σ : Gal(K/F)) (R : TestAlgebra K) : TestAlgebra K :=
  { R with algebra := (((@algebraMap K R _ _ R.algebra)).comp σ.symm.toRingHom).toAlgebra }

private theorem aut_base_square (σ : Gal(K/F)) (b : O ≃+* O)
    (hb : ∀ z : O, (localIntegersInclusion K).hom (b z) = σ ((localIntegersInclusion K).hom z)) :
    specMap σ.symm.toRingHom ≫ genericPoint K =
      genericPoint K ≫ specMap b.symm.toRingHom := by
  let i : O →+* K := (localIntegersInclusion K).hom.toRingHom
  have he : σ.symm.toRingHom.comp i = i.comp b.symm.toRingHom := by
    apply RingHom.ext
    intro z
    change σ.symm (i z) = i (b.symm z)
    have hz : i (b (b.symm z)) = σ (i (b.symm z)) := hb (b.symm z)
    rw [RingEquiv.apply_symm_apply] at hz
    rw [hz, AlgEquiv.symm_apply_apply]
  exact (specMap_comp i _).symm.trans ((congrArg (fun f : O →+* K => specMap f) he).trans
    (specMap_comp _ i))

private theorem scalarFormula_point {s : H.model.X.left ⟶ H.model.X.left}
    (hs : GenericScalarFormula H s) {R : TestAlgebra K} (x : genericTest R ⟶ H.model.X) :
    x.left ≫ s ≫ H.projection = x.left ≫ H.projection := by
  let j := pullback.fst H.model.X.hom (genericPoint K)
  let y := ((testSpec K).obj (op R)).hom
  have h : x.left ≫ H.model.X.hom = y ≫ genericPoint K := Over.w x
  let z := pullback.lift x.left y h
  have hz : z ≫ j = x.left := pullback.lift_fst _ _ _
  change j ≫ s ≫ H.projection = j ≫ H.projection at hs
  calc
    x.left ≫ s ≫ H.projection = z ≫ j ≫ s ≫ H.projection :=
      (congrArg (· ≫ s ≫ H.projection) hz.symm).trans (Category.assoc _ _ _)
    _ = z ≫ j ≫ H.projection := congrArg (z ≫ ·) hs
    _ = x.left ≫ H.projection := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hz)

private theorem semilinearMap_over (b : O ≃+* O)
    (f : modelGroup ≅ (Specs.IwahoriScalarCocycleComposition.groupBaseChange b.symm.toRingHom).obj modelGroup) :
    semilinearMap H b f ≫ overMap = overMap ≫ specMap b.symm.toRingHom :=
  absoluteMap_over _ f.hom.hom.hom

private def semilinearTestPoint (σ : Gal(K/F)) (b : O ≃+* O)
    (hb : ∀ z : O, (localIntegersInclusion K).hom (b z) = σ ((localIntegersInclusion K).hom z))
    {R : TestAlgebra K} (x : genericTest R ⟶ X)
    (s : S ⟶ S) (hs : s ≫ overMap = overMap ≫ specMap b.symm.toRingHom) :
    genericTest (retest σ R) ⟶ X :=
  Over.homMk (x.left ≫ s) (by
    have hbase : (genericTest R).hom ≫ specMap b.symm.toRingHom =
        (genericTest (retest σ R)).hom := by
      change (specMap (algebraMap K R) ≫ genericPoint K) ≫ specMap b.symm.toRingHom =
        specMap ((algebraMap K R).comp σ.symm.toRingHom) ≫ genericPoint K
      rw [specMap_comp, Category.assoc, Category.assoc, aut_base_square σ b hb]
    exact (Category.assoc _ _ _).trans
      ((congrArg (x.left ≫ ·) hs).trans ((Over.w_assoc x _).trans hbase)))

private theorem hom_ext_of_projection {f g : S ⟶ S}
    (hbase : f ≫ overMap = g ≫ overMap)
    (hproj : ∀ (R : TestAlgebra K) (x : genericTest R ⟶ X),
      x.left ≫ f ≫ H.projection = x.left ≫ g ≫ H.projection)
    (htest : ∀ (R : TestAlgebra K) (x : genericTest R ⟶ X),
      ∃ R' : TestAlgebra K, ∃ x' : genericTest R' ⟶ X,
        ∃ e : (genericTest R').left = (genericTest R).left,
          x'.left = eqToHom e ≫ x.left ≫ f) :
    f = g := by
  have := H.smooth
  apply hom_ext_of_genericTests H.affine (inferInstance : Flat overMap) H.affine
  intro R x
  obtain ⟨R', x', e, he⟩ := htest R x
  let y' : genericTest R' ⟶ X :=
    Over.homMk (eqToHom e ≫ x.left ≫ g) (by
      rw [← Over.w x', he]
      simp only [Category.assoc, hbase])
  have hxy : x' = y' := genericImage_left_injective H
      (Q := (testSpec K).obj (op R')) (x := x') (y := y') (by
    rw [he]
    change (eqToHom e ≫ x.left ≫ f) ≫ H.projection =
      (eqToHom e ≫ x.left ≫ g) ≫ H.projection
    simpa only [Category.assoc] using congrArg (eqToHom e ≫ ·) (hproj R x))
  have hl := congrArg (fun z : genericTest R' ⟶ X => z.left) hxy
  rw [he] at hl
  exact (cancel_epi (eqToHom e)).mp hl

section Twist

variable {ρ : Gal(K/F) →* MulAut (FieldPoints M' K)} {r : Gal(K/F) → FieldPoints M' K}
  (a : CoefficientExtension H ρ) (b : ∀ σ : Gal(K/F), RepresentativeExtension H (r σ))

private abbrev scalarMap (σ : Gal(K/F)) : S ⟶ S :=
  semilinearMap H (a.onIntegers σ) (a.onModel σ)

private abbrev representativeMap (σ : Gal(K/F)) : S ⟶ S :=
  (b σ).onModel.hom.hom.hom.left

private abbrev twistedMap (σ : Gal(K/F)) : S ⟶ S :=
  scalarMap H a σ ≫ representativeMap H b σ

private def twistedIso (σ : Gal(K/F)) :
    modelGroup ≅ (Specs.IwahoriScalarCocycleComposition.groupBaseChange
      (a.onIntegers σ).symm.toRingHom).obj modelGroup :=
  a.onModel σ ≪≫ (Specs.IwahoriScalarCocycleComposition.groupBaseChange
    (a.onIntegers σ).symm.toRingHom).mapIso (b σ).onModel

private theorem twistedIso_absolute (σ : Gal(K/F)) :
    semilinearMap H (a.onIntegers σ) (twistedIso H a b σ) = twistedMap H a b σ := by
  exact absoluteMap_post _ (a.onModel σ).hom.hom.hom (b σ).onModel.hom.hom.hom

private theorem representative_over (σ : Gal(K/F)) :
    representativeMap H b σ ≫ overMap = overMap :=
  Over.w (b σ).onModel.hom.hom.hom

private theorem twisted_over (σ : Gal(K/F)) :
    twistedMap H a b σ ≫ overMap = scalarMap H a σ ≫ overMap := by
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (representative_over H b σ))

private abbrev scalarTest (σ : Gal(K/F)) {R : TestAlgebra K} (x : genericTest R ⟶ X) :
    genericTest (retest σ R) ⟶ X :=
  semilinearTestPoint H σ (a.onIntegers σ) (a.restricts σ) x
    (scalarMap H a σ) (semilinearMap_over H (a.onIntegers σ) (a.onModel σ))

private abbrev twistedTest (σ : Gal(K/F)) {R : TestAlgebra K} (x : genericTest R ⟶ X) :
    genericTest (retest σ R) ⟶ X :=
  scalarTest H a σ x ≫ (b σ).onModel.hom.hom.hom

private theorem scalarTest_image
    (ha : ∀ σ, GenericScalarFormula H (scalarMap H a σ))
    (σ : Gal(K/F)) {R : TestAlgebra K} (x : genericTest R ⟶ X) :
    H.genericImage (R := retest σ R) (scalarTest H a σ x) = H.genericImage (R := R) x := by
  apply Over.OverMorphism.ext
  change (x.left ≫ scalarMap H a σ) ≫ H.projection = x.left ≫ H.projection
  exact (Category.assoc _ _ _).trans (scalarFormula_point H (ha σ) x)

private abbrev evaluatePoints {A : Type u} [CommRing A] (f : K →+* A) :
    FieldPoints M' K →* IntegralPoints M'.group (integralRing A) :=
  changeRingHom M'.group (integralRingMap f)

omit [ValuativeRel K] in
private theorem evaluate_scalar {A : Type u} [CommRing A] (f : K →+* A)
    (g : K →+* K) (v : FieldPoints M' K) :
    evaluatePoints (M' := M') f (scalarPoints M' g v) =
      evaluatePoints (M' := M') (f.comp g) v := by
  apply Over.OverMorphism.ext
  change specMap f ≫ specMap g ≫ v.left = specMap (f.comp g) ≫ v.left
  rw [specMap_comp]
  exact (Category.assoc (specMap f) (specMap g) v.left).symm

private theorem twistedTest_image
    (ha : ∀ σ, GenericScalarFormula H (scalarMap H a σ))
    (σ : Gal(K/F)) {R : TestAlgebra K} (x : genericTest R ⟶ X) :
    H.genericImage (R := retest σ R) (twistedTest H a b σ x) =
      let c : IntegralPoints M'.group (integralRing R) :=
        evaluatePoints ((algebraMap K R).comp σ.symm.toRingHom) (r σ)
      c * H.genericImage (R := R) x * c⁻¹ := by
  have h := (b σ).generic_agrees (retest σ R) (scalarTest H a σ x)
  change H.genericImage (R := retest σ R) (twistedTest H a b σ x) =
    _ * H.genericImage (R := retest σ R) (scalarTest H a σ x) * _ at h
  rw [h, scalarTest_image H a ha σ x]
  rfl

variable (hr : ∀ σ τ, r (σ * τ) = r σ * ρ σ (r τ))
  (hρ : ∀ σ v, ρ σ v = scalarPoints M' σ.toRingHom v)
  (ha : ∀ σ, GenericScalarFormula H (scalarMap H a σ))

include hr in
omit [ValuativeRel K] in
private theorem cocycle_one : r 1 = 1 := by
  have h : r 1 = r 1 * r 1 := by
    simpa only [one_mul, map_one, MulAut.one_apply] using hr 1 1
  exact (mul_left_cancel ((mul_one (r 1)).trans h)).symm

include hr hρ in
omit [ValuativeRel K] in
private theorem evaluate_cocycle {A : Type u} [CommRing A] (f : K →+* A) (σ τ : Gal(K/F)) :
    evaluatePoints (f.comp (σ * τ).symm.toRingHom) (r (σ * τ)) =
      evaluatePoints ((f.comp τ.symm.toRingHom).comp σ.symm.toRingHom) (r σ) *
        evaluatePoints (f.comp τ.symm.toRingHom) (r τ) := by
  have hcomp : f.comp (σ * τ).symm.toRingHom =
      (f.comp τ.symm.toRingHom).comp σ.symm.toRingHom := rfl
  have hcancel : ((f.comp τ.symm.toRingHom).comp σ.symm.toRingHom).comp σ.toRingHom =
      f.comp τ.symm.toRingHom := by
    ext v
    exact congrArg (f.comp τ.symm.toRingHom) (σ.symm_apply_apply v)
  rw [hcomp, hr, map_mul, hρ, evaluate_scalar, hcancel]

include hr ha in
private theorem twisted_one :
    twistedMap H a b 1 = 𝟙 S := by
  apply hom_ext_of_projection H
  · exact (twisted_over H a b 1).trans (congrArg (· ≫ overMap) a.map_one)
  · intro R x
    have h := twistedTest_image H a b ha 1 x
    simp only [cocycle_one hr, map_one, inv_one, one_mul, mul_one] at h
    have hh := congrArg (fun y : IntegralPoints M'.group (integralRing R) => y.left) h
    change ((x.left ≫ scalarMap H a 1) ≫ representativeMap H b 1) ≫ H.projection =
      x.left ≫ H.projection at hh
    simpa only [Category.assoc, Category.id_comp] using hh
  · intro R x
    refine ⟨retest 1 R, twistedTest H a b 1 x, rfl, ?_⟩
    exact (Category.assoc _ _ _).trans (Category.id_comp _).symm

include hr hρ ha in
private theorem twisted_mul (σ τ : Gal(K/F)) :
    twistedMap H a b (σ * τ) = twistedMap H a b τ ≫ twistedMap H a b σ := by
  apply hom_ext_of_projection H
  · let d := specMap (a.onIntegers σ).symm.toRingHom
    have hs : scalarMap H a σ ≫ overMap = overMap ≫ d :=
      semilinearMap_over H _ _
    calc
      _ = scalarMap H a (σ * τ) ≫ overMap := twisted_over H a b _
      _ = (scalarMap H a τ ≫ scalarMap H a σ) ≫ overMap :=
        congrArg (· ≫ overMap) (a.map_mul σ τ)
      _ = (scalarMap H a τ ≫ overMap) ≫ d :=
        (Category.assoc _ _ _).trans
          ((congrArg (scalarMap H a τ ≫ ·) hs).trans (Category.assoc _ _ _).symm)
      _ = (twistedMap H a b τ ≫ overMap) ≫ d :=
        congrArg (· ≫ d) (twisted_over H a b τ).symm
      _ = _ := (Category.assoc _ _ _).trans
        ((congrArg (twistedMap H a b τ ≫ ·) (hs.symm.trans (twisted_over H a b σ).symm)).trans
          (Category.assoc _ _ _).symm)
  · intro R x
    have h₁ := twistedTest_image H a b ha (σ * τ) x
    have h₂ := twistedTest_image H a b ha σ (twistedTest H a b τ x)
    have h₃ := twistedTest_image H a b ha τ x
    have h : H.genericImage (R := retest (σ * τ) R) (twistedTest H a b (σ * τ) x) =
        H.genericImage (R := retest σ (retest τ R))
          (twistedTest H a b σ (twistedTest H a b τ x)) := by
      rw [h₁, h₂, h₃]
      change _ =
        evaluatePoints (((algebraMap K R).comp τ.symm.toRingHom).comp σ.symm.toRingHom) (r σ) *
          (evaluatePoints ((algebraMap K R).comp τ.symm.toRingHom) (r τ) *
            H.genericImage (R := R) x *
            (evaluatePoints ((algebraMap K R).comp τ.symm.toRingHom) (r τ))⁻¹) *
          (evaluatePoints (((algebraMap K R).comp τ.symm.toRingHom).comp σ.symm.toRingHom) (r σ))⁻¹
      rw [evaluate_cocycle hr hρ]
      simp only [mul_inv_rev, mul_assoc]
    have hh := congrArg (fun y : IntegralPoints M'.group (integralRing R) => y.left) h
    change ((x.left ≫ scalarMap H a (σ * τ)) ≫ representativeMap H b (σ * τ)) ≫ H.projection =
      ((((x.left ≫ scalarMap H a τ) ≫ representativeMap H b τ) ≫ scalarMap H a σ) ≫
        representativeMap H b σ) ≫ H.projection at hh
    simpa only [Category.assoc] using hh
  · intro R x
    refine ⟨retest (σ * τ) R, twistedTest H a b (σ * τ) x, rfl, ?_⟩
    exact (Category.assoc _ _ _).trans (Category.id_comp _).symm

private theorem fieldTest_hom :
    (genericTest (CommAlgCat.of K K)).hom = genericPoint K := by
  change Spec.map (𝟙 (CommRingCat.of K)) ≫ genericPoint K = _
  rw [Spec.map_id, Category.id_comp]

omit [ValuativeRel K] in
private theorem specAut_cancel (σ : Gal(K/F)) :
    specMap σ.toRingHom ≫ specMap σ.symm.toRingHom = 𝟙 (Spec (CommRingCat.of K)) := by
  rw [← specMap_comp]
  have h : σ.toRingHom.comp σ.symm.toRingHom = RingHom.id K :=
    RingHom.ext fun v => σ.apply_symm_apply v
  rw [h]
  exact Spec.map_id _

private def scalarFieldTest (σ : Gal(K/F))
    (x : genericTest (CommAlgCat.of K K) ⟶ X) :
    genericTest (CommAlgCat.of K K) ⟶ X :=
  Over.homMk (specMap σ.toRingHom ≫ x.left ≫ scalarMap H a σ) (by
    have hs : (x.left ≫ scalarMap H a σ) ≫ overMap =
        genericPoint K ≫ specMap (a.onIntegers σ).symm.toRingHom :=
      (Category.assoc _ _ _).trans
        ((congrArg (x.left ≫ ·) (semilinearMap_over H _ _)).trans
          ((Over.w_assoc x _).trans (congrArg (· ≫ _) fieldTest_hom)))
    have hbase : specMap σ.toRingHom ≫ genericPoint K ≫
        specMap (a.onIntegers σ).symm.toRingHom = genericPoint K := by
      rw [← aut_base_square σ _ (a.restricts σ), ← Category.assoc,
        specAut_cancel, Category.id_comp]
    exact (Category.assoc _ _ _).trans
      ((congrArg (specMap σ.toRingHom ≫ ·) hs).trans (hbase.trans fieldTest_hom.symm)))

omit [ValuativeRel K] in
private theorem evaluate_id (v : FieldPoints M' K) :
    evaluatePoints (RingHom.id K) v = v := by
  apply Over.OverMorphism.ext
  change Spec.map (𝟙 (CommRingCat.of K)) ≫ v.left = v.left
  exact (congrArg (· ≫ v.left) (Spec.map_id (CommRingCat.of K))).trans (Category.id_comp _)

private theorem twisted_field_agrees (σ : Gal(K/F))
    (x : genericTest (CommAlgCat.of K K) ⟶ X) :
    (twistAction ρ r hr σ (H.genericImage (R := CommAlgCat.of K K) x)).left =
      specMap σ.toRingHom ≫ x.left ≫ twistedMap H a b σ ≫ H.projection := by
  let y := scalarFieldTest H a σ x
  have hs : H.genericImage (R := CommAlgCat.of K K) y =
      ρ σ (H.genericImage (R := CommAlgCat.of K K) x) := by
    apply Over.OverMorphism.ext
    change (specMap σ.toRingHom ≫ x.left ≫ scalarMap H a σ) ≫ H.projection =
      (ρ σ (H.genericImage (R := CommAlgCat.of K K) x)).left
    exact (Category.assoc _ _ _).trans
      ((congrArg (specMap σ.toRingHom ≫ ·) (Category.assoc _ _ _)).trans
        (a.generic_agrees σ x).symm)
  have hp := (b σ).generic_agrees (CommAlgCat.of K K) y
  change H.genericImage (R := CommAlgCat.of K K) (y ≫ (b σ).onModel.hom.hom.hom) =
    evaluatePoints (RingHom.id K) (r σ) * H.genericImage (R := CommAlgCat.of K K) y *
      (evaluatePoints (RingHom.id K) (r σ))⁻¹ at hp
  rw [evaluate_id, hs] at hp
  change (MulAut.conj (r σ) (ρ σ (H.genericImage (R := CommAlgCat.of K K) x))).left = _
  rw [MulAut.conj_apply]
  have hl := (congrArg (fun v : FieldPoints M' K => v.left) hp).symm
  change _ =
    ((specMap σ.toRingHom ≫ x.left ≫ scalarMap H a σ) ≫ representativeMap H b σ) ≫
      H.projection at hl
  have hcomp :
      ((specMap σ.toRingHom ≫ x.left ≫ scalarMap H a σ) ≫ representativeMap H b σ) ≫
          H.projection =
        specMap σ.toRingHom ≫ x.left ≫ twistedMap H a b σ ≫ H.projection := by
    simp only [Category.assoc]
  exact hl.trans hcomp

end Twist

end Model

/-- Compose the scalar isomorphisms with the base changes of the representative
isomorphisms. The scalar cocycle identity yields the absolute action laws. -/
theorem twistedScalarExtensions : TwistedScalarExtensions.{u} := by
  intro F K _ _ _ _ E M' H ρ r hr hρ a ha b
  let A : CoefficientExtension H (twistAction ρ r hr) :=
    { onIntegers := a.onIntegers
      restricts := a.restricts
      onModel := twistedIso H a b
      map_one := (twistedIso_absolute H a b 1).trans (twisted_one H a b hr ha)
      map_mul := fun σ τ =>
        (twistedIso_absolute H a b (σ * τ)).trans
          ((twisted_mul H a b hr hρ ha σ τ).trans
            (congrArg₂ (fun f g : H.model.X.left ⟶ H.model.X.left => f ≫ g)
              (twistedIso_absolute H a b τ) (twistedIso_absolute H a b σ)).symm)
      generic_agrees := fun σ x => by
        rw [twistedIso_absolute]
        exact twisted_field_agrees H a b hr σ x }
  exact ⟨A, rfl, twistedIso_absolute H a b⟩

end

end LinearAlgebraicGroups.Arithmetic.IwahoriScalarCocycleComposition
