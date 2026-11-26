import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SplitIwahoriSchemeOperators
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IwahoriMarkedConjugation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IwahoriScalarCoefficientExtension
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IwahoriPinnedDiagramExtension
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IwahoriScalarCocycleComposition
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace LinearAlgebraicGroups.Arithmetic.SplitIwahoriSchemeOperators

open _root_.LinearAlgebraicGroups.Specs
open Specs.SplitIwahoriSchemeOperators
open Specs.ExceptionalAffineBuilding (RamifiedAffineBuildings SplitAffineBuildings)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalIwahoriCongruence (localIntegers localIntegersInclusion changeRingHom)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint integralTestAlgebra)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open Specs.Pinning (BasedRootDatum)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open private fibrePointEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

universe u

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
theorem genericRestrictionInjective : GenericRestrictionInjective.{u} := by
  intro K _ _ X Y hX hY f g h
  let j := pullback.fst X.hom (genericPoint K)
  let _ : IsSchemeTheoreticallyDominant (genericPoint K) := genericPoint_dominant K
  let _ : IsSchemeTheoreticallyDominant j :=
    IsSchemeTheoreticallyDominant.pullbackFst _ _
  apply ext_of_isAffine
  have h' := congrArg Scheme.Hom.appTop h
  change f.appTop ≫ j.appTop = g.appTop ≫ j.appTop at h'
  exact CommRingCat.hom_ext (RingHom.ext fun x =>
    j.app_injective ⊤ (ConcreteCategory.congr_hom h' x))

theorem genericRestrictionInjective_conditional
    (_ramified : RamifiedAffineBuildings.{u}) (_split : SplitAffineBuildings.{u}) :
    GenericRestrictionInjective.{u} :=
  genericRestrictionInjective

section GenericTests

variable {K : Type u} [Field K] [ValuativeRel K]

/-- The generic fibre of an affine scheme over the valuation ring is itself an
affine test over the fraction field. -/
theorem genericFibre_hasUniversalTest (X : Over (integerScheme K)) (hX : IsAffine X.left) :
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
theorem hom_ext_of_genericTests
    (hgeneric : GenericRestrictionInjective.{u})
    {X : Over (integerScheme K)} {T : Scheme.{u}}
    (hX : IsAffine X.left) (hflat : Flat X.hom) (hT : IsAffine T)
    {f g : X.left ⟶ T}
    (h : ∀ (R : TestAlgebra K) (x : genericTest R ⟶ X), x.left ≫ f = x.left ≫ g) :
    f = g := by
  obtain ⟨R, x, i, hi⟩ := genericFibre_hasUniversalTest X hX
  apply hgeneric K X T hflat hT
  rw [← cancel_epi i.hom]
  simpa only [← Category.assoc, ← hi] using h R x

end GenericTests

section SemilinearTests

open Specs.IntegralSemisimpleModel (IntegralPoints)

abbrev specMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :=
  Spec.map (CommRingCat.ofHom f)

theorem specMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    specMap (g.comp f) = specMap g ≫ specMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

section OverMaps

variable {S T : Scheme.{u}} (d : T ⟶ S) {X : Over T} {Y Z : Over S}

abbrev absoluteMap (f : X ⟶ (Over.pullback d).obj Y) : X.left ⟶ Y.left :=
  f.left ≫ pullback.fst Y.hom d

theorem absoluteMap_over (f : X ⟶ (Over.pullback d).obj Y) :
    absoluteMap d f ≫ Y.hom = X.hom ≫ d := by
  change (f.left ≫ pullback.fst Y.hom d) ≫ Y.hom = _
  calc
    _ = f.left ≫ pullback.snd Y.hom d ≫ d :=
      (Category.assoc _ _ _).trans (congrArg (f.left ≫ ·) pullback.condition)
    _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ d) (Over.w f))

theorem absoluteMap_post (f : X ⟶ (Over.pullback d).obj Y) (g : Y ⟶ Z) :
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

section GenericComparison

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} (H : IwahoriModel Y)

set_option quotPrecheck false in
local notation "O" => localIntegers K

theorem genericImage_left_injective {R : TestAlgebra K}
    {x y : genericTest R ⟶ H.model.X}
    (h : x.left ≫ H.projection = y.left ≫ H.projection) : x = y := by
  let P := Over.pullback (genericPoint K)
  let Q := (testSpec K).obj (op R)
  let A := Over.mapPullbackAdj (genericPoint K)
  let t := H.toIntegral.hom.hom
  have ht : IsIso (P.map t) := by
    let G := Specs.SplitIwahoriSchemeOperators.groupBaseChange (localIntegersInclusion K).hom.toRingHom
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

theorem hom_ext_of_genericProjection {f g : H.model.X.left ⟶ H.model.X.left}
    (hbase : f ≫ H.model.X.hom = g ≫ H.model.X.hom)
    (hproj : ∀ (R : TestAlgebra K) (x : genericTest R ⟶ H.model.X),
      x.left ≫ f ≫ H.projection = x.left ≫ g ≫ H.projection)
    (hbase' : ∀ (R : TestAlgebra K) (x : genericTest R ⟶ H.model.X),
      ∃ R' : TestAlgebra K, ∃ x' : genericTest R' ⟶ H.model.X,
        ∃ i : (genericTest R').left ≅ (genericTest R).left, x'.left = i.hom ≫ x.left ≫ f) :
    f = g := by
  have := H.smooth
  apply hom_ext_of_genericTests genericRestrictionInjective H.affine
    (inferInstance : Flat H.model.X.hom) H.affine
  intro R x
  obtain ⟨R', x', i, hi⟩ := hbase' R x
  let y' : genericTest R' ⟶ H.model.X :=
    Over.homMk (i.hom ≫ x.left ≫ g) (by
      rw [← Over.w x', hi]
      simp only [Category.assoc, hbase])
  have he : x' = y' := genericImage_left_injective H (by
    rw [hi]
    change (i.hom ≫ x.left ≫ f) ≫ H.projection = (i.hom ≫ x.left ≫ g) ≫ H.projection
    simpa only [Category.assoc] using congrArg (i.hom ≫ ·) (hproj R x))
  have hl := congrArg (fun z : genericTest R' ⟶ H.model.X => z.left) he
  rw [hi] at hl
  exact (cancel_epi i.hom).mp hl

variable {F : Type u} [Field F] [Algebra F K]

def retest (σ : Gal(K/F)) (R : TestAlgebra K) : TestAlgebra K :=
  { R with algebra := (((@algebraMap K R _ _ R.algebra)).comp σ.symm.toRingHom).toAlgebra }

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem aut_base_square (σ : Gal(K/F)) (b : O ≃+* O)
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

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem genericTest_hom (R : TestAlgebra K) :
    (genericTest R).hom = specMap (@algebraMap K R _ _ R.algebra) ≫ genericPoint K := rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem genericTest_left (R : TestAlgebra K) :
    (genericTest R).left = Spec (CommRingCat.of R) := rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem retest_ring (σ : Gal(K/F)) (R : TestAlgebra K) :
    CommRingCat.of (retest σ R) = CommRingCat.of R := rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem retest_left (σ : Gal(K/F)) (R : TestAlgebra K) :
    (genericTest (retest σ R)).left = (genericTest R).left :=
  (genericTest_left (retest σ R)).trans
    ((congrArg (fun A : CommRingCat => Spec A) (retest_ring σ R)).trans (genericTest_left R).symm)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem retest_algebraMap (σ : Gal(K/F)) (R : TestAlgebra K) :
    (@algebraMap K R _ _ (retest σ R).algebra) = (@algebraMap K R _ _ R.algebra).comp σ.symm.toRingHom := rfl

set_option linter.internalConstructors false in
theorem retest_hom (σ : Gal(K/F)) (b : O ≃+* O)
    (hb : ∀ z : O, (localIntegersInclusion K).hom (b z) = σ ((localIntegersInclusion K).hom z))
    (R : TestAlgebra K) :
    (genericTest (retest σ R)).hom =
      eqToHom (retest_left σ R) ≫ (genericTest R).hom ≫ specMap b.symm.toRingHom := by
  cases R with
  | @_mkInternal A c a =>
    let f : K →+* A := @algebraMap K A _ _ a
    change specMap (f.comp σ.symm.toRingHom) ≫ genericPoint K =
      (𝟙 (Spec (CommRingCat.of A))) ≫ (specMap f ≫ genericPoint K) ≫ specMap b.symm.toRingHom
    rw [Category.id_comp, specMap_comp, Category.assoc,
      aut_base_square (F := F) σ b hb, Category.assoc]

theorem semilinearMap_over (b : O ≃+* O)
    (f : H.model ≅ (Specs.SplitIwahoriSchemeOperators.groupBaseChange b.symm.toRingHom).obj H.model) :
    semilinearMap H b f ≫ H.model.X.hom =
      H.model.X.hom ≫ specMap b.symm.toRingHom :=
  absoluteMap_over _ f.hom.hom.hom

def semilinearTestPoint (σ : Gal(K/F)) (b : O ≃+* O)
    (hb : ∀ z : O, (localIntegersInclusion K).hom (b z) = σ ((localIntegersInclusion K).hom z))
    {R : TestAlgebra K} (x : genericTest R ⟶ H.model.X)
    (s : H.model.X.left ⟶ H.model.X.left)
    (hs : s ≫ H.model.X.hom = H.model.X.hom ≫ specMap b.symm.toRingHom) :
    genericTest (retest σ R) ⟶ H.model.X :=
  Over.homMk (eqToHom (retest_left σ R) ≫ x.left ≫ s) (by
    rw [Category.assoc, Category.assoc, hs, Over.w_assoc x]
    exact (retest_hom σ b hb R).symm)

theorem scalarFormula_point {s : H.model.X.left ⟶ H.model.X.left}
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

end GenericComparison

end SemilinearTests

section PinnedTests

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

@[instance_reducible] private def groundAlgebra (R : TestAlgebra K) : Algebra F R :=
  ((@algebraMap K R _ _ R.algebra).comp (algebraMap F K)).toAlgebra

private theorem groundAlgebra_retest (σ : Gal(K/F)) (R : TestAlgebra K) :
    (groundAlgebra (F := F) (retest σ R) : Algebra F R) = groundAlgebra (F := F) R := by
  apply Algebra.algebra_ext
  intro a
  change algebraMap K R (σ.symm (algebraMap F K a)) = algebraMap K R (algebraMap F K a)
  rw [σ.symm.commutes]

private theorem groundAlgebra_field :
    (groundAlgebra (F := F) (CommAlgCat.of K K) : Algebra F K) = ‹Algebra F K› := by
  apply Algebra.algebra_ext
  intro a
  rfl

variable {E : BasedRootDatum.{u}} {M' : Model E}
  (C : MarkedFibre M' F) (α : Aut C.realization.pinned)

/-- The two integral images of a point of the marked pinned fibre and its translate. -/
private def HasPinnedImages {A : Type u} [CommRing A] (alg : Algebra F A)
    (x y : Spec (CommRingCat.of A) ⟶ M'.group.X.left) : Prop :=
  let R := @CommAlgCat.of F _ A _ alg
  ∃ v : GroupPoints C.realization.pinned.pair.G.val R,
    (markedFibrePoint C R v).left = x ∧
    (markedFibrePoint C R (v ≫ α.asIso.hom.group.hom.hom.hom)).left = y

private theorem pinnedImages_unique {A : Type u} [CommRing A] (alg : Algebra F A)
    {x y z : Spec (CommRingCat.of A) ⟶ M'.group.X.left}
    (h : HasPinnedImages C α alg x y) (h' : HasPinnedImages C α alg x z) : y = z := by
  let R := @CommAlgCat.of F _ A _ alg
  obtain ⟨v, hv, hv'⟩ := h
  obtain ⟨w, hw, hw'⟩ := h'
  have he : v = w := by
    apply (fibrePointEquiv C R).injective
    exact Over.OverMorphism.ext (hv.trans hw.symm)
  rw [he] at hv'
  exact hv'.symm.trans hw'

private theorem pinnedCoefficientPoint_left (σ : Gal(K/F))
    (v : GroupPoints C.realization.pinned.pair.G.val (CommAlgCat.of F K)) :
    (pinnedCoefficientPoint C α σ v).left =
      specMap σ.toRingHom ≫
        (markedFibrePoint C (CommAlgCat.of F K) (v ≫ α.asIso.hom.group.hom.hom.hom)).left := by
  let R := CommAlgCat.of F K
  let t := CommAlgCat.ofHom σ.toAlgHom
  let u := v ≫ α.asIso.hom.group.hom.hom.hom
  obtain ⟨i, hi⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison C
  have hn : markedFibrePoint C R ((testSpec F).map t.op ≫ u) =
      changeRingHom M'.group ((integralTestAlgebra F).map t) (markedFibrePoint C R u) :=
    (hi R _).symm.trans ((ConcreteCategory.congr_hom (i.hom.naturality t) u).trans
      (congrArg (changeRingHom M'.group ((integralTestAlgebra F).map t)) (hi R u)))
  exact congrArg (fun w : FieldPoints M' K => w.left) hn

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} (H : IwahoriModel Y)

set_option quotPrecheck false in
local notation "O" => localIntegers K

set_option linter.internalConstructors false in
private theorem pinnedFormula_pre_scalar (σ : Gal(K/F)) (b : O ≃+* O)
    (hb : ∀ z : O, (localIntegersInclusion K).hom (b z) = σ ((localIntegersInclusion K).hom z))
    (s t : H.model.X.left ⟶ H.model.X.left)
    (hbase : s ≫ H.model.X.hom = H.model.X.hom ≫ specMap b.symm.toRingHom)
    (hs : GenericScalarFormula H s) (ht : GenericPinnedFormula H C α t) :
    GenericPinnedFormula H C α (s ≫ t) := by
  intro R x
  let y := semilinearTestPoint H σ b hb x s hbase
  have hpin := ht (retest σ R) y
  cases R with
  | @_mkInternal A instA algK =>
    let R := @CommAlgCat.of K _ A instA algK
    change HasPinnedImages C α (groundAlgebra (F := F) (retest σ R))
      ((𝟙 _ ≫ x.left ≫ s) ≫ H.projection)
      ((𝟙 _ ≫ x.left ≫ s) ≫ t ≫ H.projection) at hpin
    change HasPinnedImages C α (groundAlgebra (F := F) R)
      (x.left ≫ H.projection) (x.left ≫ (s ≫ t) ≫ H.projection)
    rw [groundAlgebra_retest σ R] at hpin
    simp only [Category.id_comp, Category.assoc] at hpin ⊢
    exact (scalarFormula_point H hs x) ▸ hpin

private theorem pinnedFormula_post_scalar (f : H.model.X ⟶ H.model.X)
    (s : H.model.X.left ⟶ H.model.X.left)
    (hs : GenericScalarFormula H s) (hf : GenericPinnedFormula H C α f.left) :
    GenericPinnedFormula H C α (f.left ≫ s) := by
  intro R x
  obtain ⟨v, h₁, h₂⟩ := hf R x
  have he := scalarFormula_point H hs (x ≫ f)
  change (x.left ≫ f.left) ≫ s ≫ H.projection = (x.left ≫ f.left) ≫ H.projection at he
  refine ⟨v, h₁, ?_⟩
  have h₃ : x.left ≫ f.left ≫ s ≫ H.projection = x.left ≫ f.left ≫ H.projection :=
    (Category.assoc x.left f.left (s ≫ H.projection)).symm.trans
      (he.trans (Category.assoc x.left f.left H.projection))
  exact h₂.trans (h₃.symm.trans (congrArg (x.left ≫ ·) (Category.assoc f.left s H.projection).symm))

private theorem pinned_scalar_commute (σ : Gal(K/F)) (b : O ≃+* O)
    (hb : ∀ z : O, (localIntegersInclusion K).hom (b z) = σ ((localIntegersInclusion K).hom z))
    (s : H.model.X.left ⟶ H.model.X.left) (f : H.model.X ⟶ H.model.X)
    (hbase : s ≫ H.model.X.hom = H.model.X.hom ≫ specMap b.symm.toRingHom)
    (hs : GenericScalarFormula H s) (hf : GenericPinnedFormula H C α f.left) :
    s ≫ f.left = f.left ≫ s := by
  refine hom_ext_of_genericProjection H ?_ ?_ ?_
  · calc
      _ = s ≫ H.model.X.hom := (Category.assoc _ _ _).trans (congrArg (s ≫ ·) (Over.w f))
      _ = H.model.X.hom ≫ specMap b.symm.toRingHom := hbase
      _ = _ := ((Category.assoc _ _ _).trans
        ((congrArg (f.left ≫ ·) hbase).trans (Over.w_assoc f _))).symm
  · intro R x
    have h := pinnedFormula_pre_scalar C α H σ b hb s f.left hbase hs hf R x
    have h' := pinnedFormula_post_scalar C α H f s hs hf R x
    exact pinnedImages_unique C α (groundAlgebra (F := F) R) h h'
  · intro R x
    let y := semilinearTestPoint H σ b hb x s hbase
    refine ⟨retest σ R, y ≫ f, eqToIso (retest_left σ R), ?_⟩
    change (eqToHom (retest_left σ R) ≫ x.left ≫ s) ≫ f.left =
      eqToHom (retest_left σ R) ≫ x.left ≫ s ≫ f.left
    simp only [Category.assoc]


end PinnedTests

section PinnedAssembly

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} (H : IwahoriModel Y)

variable (C : MarkedFibre M' F) (δ : Gal(K/F) →* Aut C.realization.pinned)
  (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
  (hρ : ∀ σ v, ρ σ (markedFibrePoint C (CommAlgCat.of F K) v) =
    pinnedCoefficientPoint C (δ σ) σ v)

include hρ in
private theorem pinnedField_agrees (σ : Gal(K/F))
    (s : H.model.X.left ⟶ H.model.X.left)
    (hs : GenericPinnedFormula H C (δ σ) s)
    (x : genericTest (CommAlgCat.of K K) ⟶ H.model.X) :
    (ρ σ (H.genericImage (R := CommAlgCat.of K K) x)).left =
      specMap σ.toRingHom ≫ x.left ≫ s ≫ H.projection := by
  let R := CommAlgCat.of K K
  have h := hs R x
  change HasPinnedImages C (δ σ) (groundAlgebra (F := F) R)
    (x.left ≫ H.projection) (x.left ≫ s ≫ H.projection) at h
  rw [groundAlgebra_field] at h
  obtain ⟨v, hv, hw⟩ := h
  have hi : markedFibrePoint C (CommAlgCat.of F K) v = H.genericImage (R := R) x :=
    Over.OverMorphism.ext hv
  have h₁ := congrArg (fun w : FieldPoints M' K => (ρ σ w).left) hi.symm
  have h₂ := congrArg (fun w : FieldPoints M' K => w.left) (hρ σ v)
  exact h₁.trans (h₂.trans ((pinnedCoefficientPoint_left C (δ σ) σ v).trans
    (congrArg (specMap σ.toRingHom ≫ ·) hw)))

variable {ρₛ : Gal(K/F) →* MulAut (FieldPoints M' K)}
  (a : CoefficientExtension H ρₛ) (f : Gal(K/F) →* Aut H.model)

private abbrev scalarAbsolute (σ : Gal(K/F)) : H.model.X.left ⟶ H.model.X.left :=
  semilinearMap H (a.onIntegers σ) (a.onModel σ)

private abbrev pinnedAbsolute (σ : Gal(K/F)) : H.model.X.left ⟶ H.model.X.left :=
  (f σ).asIso.hom.hom.hom.left

private def scalarThenPinnedIso (σ : Gal(K/F)) :
    H.model ≅ (Specs.SplitIwahoriSchemeOperators.groupBaseChange
      (a.onIntegers σ).symm.toRingHom).obj H.model :=
  (a.onModel σ).trans
    ((Specs.SplitIwahoriSchemeOperators.groupBaseChange
      (a.onIntegers σ).symm.toRingHom).mapIso (f σ).asIso)

private theorem scalarThenPinned_absolute (σ : Gal(K/F)) :
    semilinearMap H (a.onIntegers σ) (scalarThenPinnedIso H a f σ) =
      scalarAbsolute H a σ ≫ pinnedAbsolute H f σ :=
  absoluteMap_post (specMap (a.onIntegers σ).symm.toRingHom) (a.onModel σ).hom.hom.hom
    (f σ).asIso.hom.hom.hom

private theorem pinnedAbsolute_one : pinnedAbsolute H f 1 = 𝟙 H.model.X.left :=
  congrArg (fun q : Aut H.model => q.asIso.hom.hom.hom.left) (f.map_one)

private theorem pinnedAbsolute_mul (σ τ : Gal(K/F)) :
    pinnedAbsolute H f (σ * τ) = pinnedAbsolute H f τ ≫ pinnedAbsolute H f σ :=
  congrArg (fun q : Aut H.model => q.asIso.hom.hom.hom.left) (f.map_mul σ τ)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem comp_interchange {X : Scheme.{u}} (s t p q : X ⟶ X)
    (h : t ≫ p = p ≫ t) :
    (s ≫ t) ≫ (p ≫ q) = (s ≫ p) ≫ (t ≫ q) := by
  simp only [Category.assoc]
  rw [← Category.assoc t p q, h, Category.assoc]

include hρ in
private theorem assemblePinnedCoefficient
    (ha : ∀ σ, GenericScalarFormula H (scalarAbsolute H a σ))
    (hf : ∀ σ, GenericPinnedFormula H C (δ σ) (pinnedAbsolute H f σ)) :
    ∃ A : CoefficientExtension H ρ,
      ∀ σ, GenericPinnedFormula H C (δ σ) (semilinearMap H (A.onIntegers σ) (A.onModel σ)) := by
  have hcomm (σ τ : Gal(K/F)) :
      scalarAbsolute H a σ ≫ pinnedAbsolute H f τ =
        pinnedAbsolute H f τ ≫ scalarAbsolute H a σ :=
    pinned_scalar_commute C (δ τ) H σ (a.onIntegers σ) (a.restricts σ)
      (scalarAbsolute H a σ) (f τ).asIso.hom.hom.hom (semilinearMap_over H _ _) (ha σ) (hf τ)
  have hgeneric (σ : Gal(K/F)) :
      GenericPinnedFormula H C (δ σ)
        (semilinearMap H (a.onIntegers σ) (scalarThenPinnedIso H a f σ)) := by
    rw [scalarThenPinned_absolute]
    exact pinnedFormula_pre_scalar C (δ σ) H σ (a.onIntegers σ) (a.restricts σ)
      (scalarAbsolute H a σ) (pinnedAbsolute H f σ) (semilinearMap_over H _ _) (ha σ) (hf σ)
  refine ⟨{ onIntegers := a.onIntegers, restricts := a.restricts
            onModel := scalarThenPinnedIso H a f
            map_one := ?_, map_mul := ?_
            generic_agrees := fun σ x => pinnedField_agrees H C δ ρ hρ σ _ (hgeneric σ) x },
    hgeneric⟩
  · exact (scalarThenPinned_absolute H a f 1).trans
      ((congrArg₂ (fun g k : H.model.X.left ⟶ H.model.X.left => g ≫ k)
        a.map_one (pinnedAbsolute_one H f)).trans (Category.id_comp _))
  · intro σ τ
    let comp := fun g k : H.model.X.left ⟶ H.model.X.left => g ≫ k
    calc
      _ = scalarAbsolute H a (σ * τ) ≫ pinnedAbsolute H f (σ * τ) :=
        scalarThenPinned_absolute H a f (σ * τ)
      _ = (scalarAbsolute H a τ ≫ scalarAbsolute H a σ) ≫
            (pinnedAbsolute H f τ ≫ pinnedAbsolute H f σ) :=
        congrArg₂ comp (a.map_mul σ τ) (pinnedAbsolute_mul H f σ τ)
      _ = (scalarAbsolute H a τ ≫ pinnedAbsolute H f τ) ≫
            (scalarAbsolute H a σ ≫ pinnedAbsolute H f σ) :=
        comp_interchange _ _ _ _ (hcomm σ τ)
      _ = _ := (congrArg₂ comp (scalarThenPinned_absolute H a f τ)
        (scalarThenPinned_absolute H a f σ)).symm


end PinnedAssembly

section Interfaces

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

private def conjugationModel (H : IwahoriModel Y) : Specs.IwahoriMarkedConjugation.IwahoriModel Y :=
  ⟨H.model, H.affine, H.smooth, H.toIntegral, H.genericIso, H.residueIso, H.residueIso_overIntegral,
    H.borel, H.borel_marked, H.universal⟩

private def conjugationChart {H : IwahoriModel Y} (U : ScaledRootChart H) :
    Specs.IwahoriMarkedConjugation.ScaledRootChart (conjugationModel H) :=
  ⟨U.uniformizer, U.uniformizer_value, U.negative, U.positive, U.negative_enumerates,
    U.positive_enumerates, U.chart, U.open_chart, U.covers, U.scales⟩

private def scalarModel (H : IwahoriModel Y) : Specs.IwahoriScalarCoefficientExtension.IwahoriModel Y :=
  ⟨H.model, H.affine, H.smooth, H.toIntegral, H.genericIso, H.residueIso, H.residueIso_overIntegral,
    H.borel, H.borel_marked, H.universal⟩

private def scalarChart {H : IwahoriModel Y} (U : ScaledRootChart H) :
    Specs.IwahoriScalarCoefficientExtension.ScaledRootChart (scalarModel H) :=
  ⟨U.uniformizer, U.uniformizer_value, U.negative, U.positive, U.negative_enumerates,
    U.positive_enumerates, U.chart, U.open_chart, U.covers, U.scales⟩

private def pinnedModel (H : IwahoriModel Y) : Specs.IwahoriPinnedDiagramExtension.IwahoriModel Y :=
  ⟨H.model, H.affine, H.smooth, H.toIntegral, H.genericIso, H.residueIso, H.residueIso_overIntegral,
    H.borel, H.borel_marked, H.universal⟩

private def pinnedChart {H : IwahoriModel Y} (U : ScaledRootChart H) :
    Specs.IwahoriPinnedDiagramExtension.ScaledRootChart (pinnedModel H) :=
  ⟨U.uniformizer, U.uniformizer_value, U.negative, U.positive, U.negative_enumerates,
    U.positive_enumerates, U.chart, U.open_chart, U.covers, U.scales⟩

private def cocycleModel (H : IwahoriModel Y) :
    Specs.IwahoriScalarCocycleComposition.IwahoriModel M' K :=
  ⟨H.model, H.affine, H.smooth, H.toIntegral, H.genericIso⟩

end Interfaces

/-- The length-zero representative and its inverse extend on the given marked model. -/
theorem markedRepresentativeExtensions : MarkedRepresentativeExtensions.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y H U r hr
  obtain ⟨f, h, h'⟩ := IwahoriMarkedConjugation.markedConjugation Y
    (conjugationModel H) (conjugationChart U) r hr
  exact ⟨⟨f, h, h'⟩⟩

/-- The scalar cocycle gives the prescribed composite of scalar and representative operators. -/
theorem twistedScalarExtensions : TwistedScalarExtensions.{u} := by
  intro F K _ _ _ _ _ _ D E M M' c p p' e Y H ρ r hr hρ a ha b
  let T := cocycleModel H
  let a' : Specs.IwahoriScalarCocycleComposition.CoefficientExtension T ρ :=
    ⟨a.onIntegers, a.restricts, a.onModel, a.map_one, a.map_mul, a.generic_agrees⟩
  let b' (σ : Gal(K/F)) : Specs.IwahoriScalarCocycleComposition.RepresentativeExtension T (r σ) :=
    ⟨(b σ).onModel, (b σ).generic_agrees, (b σ).generic_inverse⟩
  obtain ⟨A, _, hA⟩ :=
    IwahoriScalarCocycleComposition.twistedScalarExtensions T ρ r hr hρ a' ha b'
  exact ⟨⟨A.onIntegers, A.restricts, A.onModel, A.map_one, A.map_mul, A.generic_agrees⟩, hA⟩

section CoefficientAssembly

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K]
  [ValuativeRel F] [ValuativeRel K] [TopologicalSpace F] [TopologicalSpace K]
  [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

private theorem scalarCoefficientOnModel (H : IwahoriModel Y) (U : ScaledRootChart H)
    (h : IsUnramifiedLocalExtension F K) (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
    (hρ : ∀ σ g, ρ σ g = scalarPoints M' σ.toRingHom g) :
    ∃ a : CoefficientExtension H ρ,
      ∀ σ, GenericScalarFormula H (semilinearMap H (a.onIntegers σ) (a.onModel σ)) := by
  obtain ⟨a, ha⟩ := IwahoriScalarCoefficientExtension.scalarCoefficientExtensions h Y
    (scalarModel H) (scalarChart U) ρ hρ
  exact ⟨⟨a.onIntegers, a.restricts, a.onModel, a.map_one, a.map_mul, a.generic_agrees⟩, ha⟩

omit [FiniteDimensional F K] [IsGalois F K] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [ValuativeExtension F K] in
private theorem pinnedFormula_of_child (H : IwahoriModel Y) (C : MarkedFibre M' F)
    (α : Aut C.realization.pinned) (f : H.model ⟶ H.model)
    (h : Specs.IwahoriPinnedDiagramExtension.GenericPinnedFormula (pinnedModel H) C α f) :
    GenericPinnedFormula H C α f.hom.hom.left := by
  intro R x
  obtain ⟨v, hx, hv⟩ := h R x
  exact ⟨v, hx, hv.trans (Category.assoc x.left f.hom.hom.left H.projection)⟩

end CoefficientAssembly

/-- The scalar and pinned coefficient operators extend to the split Iwahori model. -/
theorem splitCoefficientExtensions : SplitCoefficientExtensions.{u} := by
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ h D E M M' c p p' e Y H U ρ
  constructor
  · exact scalarCoefficientOnModel H U h ρ
  · intro C δ hρ
    let ρₛ : Gal(K/F) →* MulAut (FieldPoints M' K) :=
      LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat.markedCoefficientAction M'
    obtain ⟨a, ha⟩ := scalarCoefficientOnModel H U h ρₛ (fun _ _ => rfl)
    obtain ⟨f, hf⟩ := IwahoriPinnedDiagramExtension.pinnedDiagramExtension h Y
      (pinnedModel H) (pinnedChart U) C δ
    exact assemblePinnedCoefficient H C δ ρ hρ a f ha
      (fun σ => pinnedFormula_of_child H C (δ σ) (f σ).asIso.hom (hf σ))

end

end LinearAlgebraicGroups.Arithmetic.SplitIwahoriSchemeOperators
