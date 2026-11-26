import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalRealModelGeometry
import LinearAlgebraicGroups.Affine.HopfAlgebras
import LinearAlgebraicGroups.Affine.CharacteristicZeroSmoothness
import LinearAlgebraicGroups.Reductive.RadicalBaseChange
import LinearAlgebraicGroups.Classification.CentralIsogenies
import LinearAlgebraicGroups.Classification.Pinning
import LinearAlgebraicGroups.RootData.BorelNormalizer
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small

noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalRealModelGeometry

open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalRealModelGeometry
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.GeometricRadicals (GeometricGroup)

variable {F : Type u} [Field F] {k₀ : Type} [Field k₀]

section LiftTestAlgebra

variable (e : F ≃+* k₀)

private abbrev liftedAlgebra (R : TestAlgebra k₀) : Algebra F (ULift.{u} R) :=
  ((ULift.ringEquiv.symm.toRingHom.comp (algebraMap k₀ R)).comp e.toRingHom).toAlgebra

private abbrev liftedTest (R : TestAlgebra k₀) : TestAlgebra F :=
  letI := liftedAlgebra e R
  CommAlgCat.of F (ULift.{u} R)

private def liftedMap {R S : TestAlgebra k₀} (a : R ⟶ S) : liftedTest e R ⟶ liftedTest e S := by
  letI := liftedAlgebra e R
  letI := liftedAlgebra e S
  exact CommAlgCat.ofHom
    ({ toRingHom := a.hom.toRingHom.ulift
       commutes' := fun x => congrArg ULift.up (a.hom.commutes (e x)) } :
      ULift.{u} R →ₐ[F] ULift.{u} S)

end LiftTestAlgebra

private abbrev restrictAlgebra (e : F ≃+* k₀) (A : TestAlgebra F) : Algebra k₀ A :=
  ((algebraMap F A).comp e.symm.toRingHom).toAlgebra

private theorem finiteType_restrictAlgebra (e : F ≃+* k₀) (A : TestAlgebra F)
    (hA : Algebra.FiniteType F A) : @Algebra.FiniteType k₀ A _ _ (restrictAlgebra e A) := by
  letI := restrictAlgebra e A
  apply RingHom.finiteType_algebraMap.mp
  exact (RingHom.finiteType_algebraMap.mpr hA).comp
    (.of_surjective e.symm.toRingHom e.symm.surjective)

private theorem small_coordinateAlgebra (e : F ≃+* k₀) (A : TestAlgebra F)
    (hA : Algebra.FiniteType F A) : Small.{0} A := by
  letI := restrictAlgebra e A
  letI : Algebra.FiniteType k₀ A := finiteType_restrictAlgebra e A hA
  exact Algebra.FiniteType.small (R := k₀) (S := A)

/-- The transported coordinate algebra in the universe of the smaller base field. -/
private def smallerAlgebra (e : F ≃+* k₀) (A : TestAlgebra F) (hA : Algebra.FiniteType F A) :
    TestAlgebra k₀ := by
  letI := restrictAlgebra e A
  letI := small_coordinateAlgebra e A hA
  exact CommAlgCat.of k₀ (Shrink.{0} A)

private def smallerAlgebraEquiv (e : F ≃+* k₀) (A : TestAlgebra F)
    (hA : Algebra.FiniteType F A) : A ≃+* smallerAlgebra e A hA := by
  letI := small_coordinateAlgebra e A hA
  exact (Shrink.ringEquiv (α := A)).symm

private theorem smallerAlgebraEquiv_algebraMap (e : F ≃+* k₀) (A : TestAlgebra F)
    (hA : Algebra.FiniteType F A) (x : F) :
    smallerAlgebraEquiv e A hA (algebraMap F A x) =
      algebraMap k₀ (smallerAlgebra e A hA) (e x) := by
  letI := restrictAlgebra e A
  letI := small_coordinateAlgebra e A hA
  apply (Shrink.algEquiv k₀ A).injective
  change (Shrink.algEquiv k₀ A) ((Shrink.algEquiv k₀ A).symm (algebraMap F A x)) =
    (Shrink.algEquiv k₀ A) (algebraMap k₀ (Shrink.{0} A) (e x))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
  change algebraMap F A x = algebraMap F A (e.symm (e x))
  rw [RingEquiv.symm_apply_apply]

private theorem smallerAlgebra_finiteType (e : F ≃+* k₀) (A : TestAlgebra F)
    (hA : Algebra.FiniteType F A) : Algebra.FiniteType k₀ (smallerAlgebra e A hA) := by
  letI := restrictAlgebra e A
  letI := small_coordinateAlgebra e A hA
  exact (finiteType_restrictAlgebra e A hA).equiv (Shrink.algEquiv k₀ A).symm

section AlgebraMaps

variable (e : F ≃+* k₀) {A : TestAlgebra F} {B : TestAlgebra k₀}
    (d : A ≃+* B) (hd : ∀ x : F, d (algebraMap F A x) = algebraMap k₀ B (e x))

private def liftAlgebraMap {R : TestAlgebra k₀} (f : B ⟶ R) : A ⟶ liftedTest e R := by
  letI := liftedAlgebra e R
  exact CommAlgCat.ofHom
    ({ toRingHom := ULift.ringEquiv.symm.toRingHom.comp (f.hom.toRingHom.comp d.toRingHom)
       commutes' := by
         intro x
         change ULift.up (f.hom (d (algebraMap F A x))) =
           ULift.up (algebraMap k₀ R (e x))
         rw [hd, f.hom.commutes] } : A →ₐ[F] ULift.{u} R)

private def lowerAlgebraMap {R : TestAlgebra k₀} (f : A ⟶ liftedTest e R) : B ⟶ R := by
  letI := liftedAlgebra e R
  let f' : A →ₐ[F] ULift.{u} R := f.hom
  exact CommAlgCat.ofHom
    ({ toRingHom := ULift.ringEquiv.toRingHom.comp (f'.toRingHom.comp d.symm.toRingHom)
       commutes' := by
         intro x
         have h : d.symm (algebraMap k₀ B x) = algebraMap F A (e.symm x) := by
           apply d.injective
           rw [d.apply_symm_apply, hd, e.apply_symm_apply]
         change (f' (d.symm (algebraMap k₀ B x))).down = algebraMap k₀ R x
         rw [h, f'.commutes]
         change algebraMap k₀ R (e (e.symm x)) = algebraMap k₀ R x
         rw [RingEquiv.apply_symm_apply] } : B →ₐ[k₀] R)

/-- Algebra maps into a small test ring and into its lift are naturally equivalent. -/
private def liftedAlgebraMaps (R : TestAlgebra k₀) :
    (B ⟶ R) ≃ (A ⟶ liftedTest e R) where
  toFun := liftAlgebraMap e d hd
  invFun := lowerAlgebraMap e d hd
  left_inv f := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change f.hom (d (d.symm x)) = f.hom x
    rw [RingEquiv.apply_symm_apply]
  right_inv f := by
    apply CommAlgCat.hom_ext
    apply @AlgHom.ext F A (liftedTest e R) _ _ _ A.algebra (liftedTest e R).algebra
    intro x
    change ULift.up ((f.hom (d.symm (d x))).down) = f.hom x
    rw [RingEquiv.symm_apply_apply]

private theorem liftAlgebraMap_naturality {R S : TestAlgebra k₀}
    (f : B ⟶ R) (g : R ⟶ S) :
    liftAlgebraMap e d hd (f ≫ g) = liftAlgebraMap e d hd f ≫ liftedMap e g := by
  apply CommAlgCat.hom_ext
  apply @AlgHom.ext F A (liftedTest e S) _ _ _ A.algebra (liftedTest e S).algebra
  intro x
  rfl

end AlgebraMaps

private def specPointsEquiv {k : Type u} [Field k] (A R : TestAlgebra k) :
    (A ⟶ R) ≃ Points ((testSpec k).obj (op A)) R where
  toFun f := (testSpec k).map f.op
  invFun p := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage p).unop
  left_inv f := by simp
  right_inv p := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage p

private theorem specPointsEquiv_comp {k : Type u} [Field k] {A R S : TestAlgebra k}
    (f : A ⟶ R) (g : R ⟶ S) :
    specPointsEquiv A S (f ≫ g) = mapPoints g (specPointsEquiv A R f) :=
  (testSpec k).map_comp g.op f.op

private structure AffinePresentation (X : SchemeOver F) where
  coordinates : TestAlgebra F
  iso : (testSpec F).obj (op coordinates) ≅ X
  finiteType : Algebra.FiniteType F coordinates

private def affinePresentation (X : SchemeOver F) (hX : IsAffine X.left)
    (hft : LocallyOfFiniteType X.hom) : AffinePresentation X := by
  let A := (AlgebraicGeometry.essImage_algSpec.mpr hX).choose
  let s := (AlgebraicGeometry.essImage_algSpec.mpr hX).choose_spec.some
  refine ⟨A.unop, s, ?_⟩
  have h : LocallyOfFiniteType ((testSpec F).obj A).hom := by
    rw [← Over.w s.hom]
    letI : IsIso s.hom.left := inferInstance
    exact inferInstance
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap F A.unop))) at h
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  exact RingHom.finiteType_algebraMap.mp h

section SchemeModel

variable (e : F ≃+* k₀) {X : SchemeOver F} (P : AffinePresentation X)

private abbrev transportedCoordinates : TestAlgebra k₀ :=
  smallerAlgebra e P.coordinates P.finiteType

private abbrev transportedScheme : SchemeOver k₀ := (testSpec k₀).obj (op (transportedCoordinates e P))

private theorem transportedScheme_finiteType : LocallyOfFiniteType (transportedScheme e P).hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k₀ (transportedCoordinates e P))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr (smallerAlgebra_finiteType e P.coordinates P.finiteType)

private theorem transportedScheme_affine : IsAffine (transportedScheme e P).left := by
  change IsAffine (Spec (CommRingCat.of (transportedCoordinates e P)))
  infer_instance

private theorem transportedScheme_quasiCompact : QuasiCompact (transportedScheme e P).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k₀ (transportedCoordinates e P))))
  infer_instance

/-- The scheme point comparison induced by the isomorphism of coordinate rings. -/
private def transportedSchemePoints (R : TestAlgebra k₀) :
    Points (transportedScheme e P) R ≃ Points X (liftedTest e R) :=
  (specPointsEquiv (transportedCoordinates e P) R).symm.trans <|
    (liftedAlgebraMaps e (smallerAlgebraEquiv e P.coordinates P.finiteType)
      (smallerAlgebraEquiv_algebraMap e P.coordinates P.finiteType) R).trans <|
    (specPointsEquiv P.coordinates (liftedTest e R)).trans P.iso.homToEquiv

private theorem transportedSchemePoints_naturality {R S : TestAlgebra k₀}
    (g : R ⟶ S) (p : Points (transportedScheme e P) R) :
    transportedSchemePoints e P S (mapPoints g p) =
      mapPoints (liftedMap e g) (transportedSchemePoints e P R p) := by
  obtain ⟨f, rfl⟩ := (specPointsEquiv (transportedCoordinates e P) R).surjective p
  rw [← specPointsEquiv_comp]
  simp only [transportedSchemePoints, Equiv.trans_apply, Equiv.symm_apply_apply]
  let d := smallerAlgebraEquiv e P.coordinates P.finiteType
  have hd := smallerAlgebraEquiv_algebraMap e P.coordinates P.finiteType
  change specPointsEquiv _ _ (liftAlgebraMap e d hd (f ≫ g)) ≫ P.iso.hom =
    mapPoints (liftedMap e g) (specPointsEquiv _ _ (liftAlgebraMap e d hd f) ≫ P.iso.hom)
  rw [liftAlgebraMap_naturality, specPointsEquiv_comp]
  exact Category.assoc _ _ _

end SchemeModel

section GroupModel

variable (e : F ≃+* k₀) {G : GroupScheme F} (P : AffinePresentation G.X)

private def transportedGroupLaw : NaturalGroupLaw (transportedScheme e P) where
  group R := (transportedSchemePoints e P R).group
  map_one {R S} f := by
    apply (transportedSchemePoints e P S).injective
    rw [transportedSchemePoints_naturality]
    change ((groupPointsFunctor F).obj G).map (liftedMap e f)
        (transportedSchemePoints e P R ((transportedSchemePoints e P R).symm 1)) =
      transportedSchemePoints e P S ((transportedSchemePoints e P S).symm 1)
    simp only [Equiv.apply_symm_apply]
    exact (((groupPointsFunctor F).obj G).map (liftedMap e f)).hom.map_one
  map_mul {R S} f p q := by
    apply (transportedSchemePoints e P S).injective
    rw [transportedSchemePoints_naturality]
    change ((groupPointsFunctor F).obj G).map (liftedMap e f)
        (transportedSchemePoints e P R ((transportedSchemePoints e P R).symm
          (transportedSchemePoints e P R p * transportedSchemePoints e P R q))) =
      transportedSchemePoints e P S ((transportedSchemePoints e P S).symm
        (transportedSchemePoints e P S (mapPoints f p) * transportedSchemePoints e P S (mapPoints f q)))
    simp only [Equiv.apply_symm_apply, transportedSchemePoints_naturality]
    exact (((groupPointsFunctor F).obj G).map (liftedMap e f)).hom.map_mul _ _

/-- The affine group law recovered from the natural group law on the
transported scheme points. -/
private def smallGroupModel : AffineAlgebraicGroup k₀ :=
  let h := transportedScheme_affine e P
  let H : GroupScheme k₀ :=
    { X := transportedScheme e P
      grp := (groupLawEquiv (transportedScheme e P) h).symm (transportedGroupLaw e P) }
  ⟨H, h, transportedScheme_finiteType e P, transportedScheme_quasiCompact e P⟩

private def smallGroupPoints (R : TestAlgebra k₀) :
    GroupPoints (smallGroupModel e P).val R ≃* GroupPoints G (liftedTest e R) where
  toEquiv := transportedSchemePoints e P R
  map_mul' p q := by
    have h := (groupLawEquiv (transportedScheme e P) (transportedScheme_affine e P)).apply_symm_apply
      (transportedGroupLaw e P)
    have hm := congrArg (fun L : NaturalGroupLaw (transportedScheme e P) => (L.group R).mul p q) h
    change p * q = (transportedSchemePoints e P R).symm
      (transportedSchemePoints e P R p * transportedSchemePoints e P R q) at hm
    change transportedSchemePoints e P R (p * q) = _
    rw [hm, Equiv.apply_symm_apply]
    rfl

private theorem smallGroupPoints_naturality {R S : TestAlgebra k₀} (f : R ⟶ S)
    (p : GroupPoints (smallGroupModel e P).val R) :
    smallGroupPoints e P S (((groupPointsFunctor k₀).obj (smallGroupModel e P).val).map f p) =
      ((groupPointsFunctor F).obj G).map (liftedMap e f) (smallGroupPoints e P R p) :=
  transportedSchemePoints_naturality e P f p

end GroupModel

section LiftedPoints

variable (e : F ≃+* k₀) {X : SchemeOver F} (P : AffinePresentation X)

private def liftedCoordinatesIso : P.coordinates ≅ liftedTest e (transportedCoordinates e P) := by
  let R := transportedCoordinates e P
  letI := liftedAlgebra e R
  exact CommAlgCat.isoMk
    ({ ((smallerAlgebraEquiv e P.coordinates P.finiteType).trans ULift.ringEquiv.symm :
          P.coordinates ≃+* ULift.{u} R) with
      commutes' := fun x =>
        congrArg ULift.up (smallerAlgebraEquiv_algebraMap e P.coordinates P.finiteType x) } :
        P.coordinates ≃ₐ[F] ULift.{u} R)

private def liftedSpecIso : (testSpec F).obj (op (liftedTest e (transportedCoordinates e P))) ≅ X :=
  (testSpec F).mapIso (liftedCoordinatesIso e P).op ≪≫ P.iso

private theorem transportedSchemePoints_id :
    transportedSchemePoints e P (transportedCoordinates e P) (𝟙 (transportedScheme e P)) =
      (liftedSpecIso e P).hom := by
  have h : specPointsEquiv (transportedCoordinates e P) (transportedCoordinates e P) (𝟙 _) =
      𝟙 (transportedScheme e P) := (testSpec k₀).map_id _
  simp only [transportedSchemePoints, Equiv.trans_apply, ← h, Equiv.symm_apply_apply]
  rfl

include P in
private theorem hom_ext_of_liftedPoints {Y : SchemeOver F} {f g : X ⟶ Y}
    (h : ∀ R : TestAlgebra k₀, ∀ p : Points X (liftedTest e R), p ≫ f = p ≫ g) :
    f = g :=
  (cancel_epi (liftedSpecIso e P).hom).mp
    (h (transportedCoordinates e P) (liftedSpecIso e P).hom)

include P in
private theorem hom_of_liftedPoints {Y : SchemeOver F}
    (τ : ∀ R : TestAlgebra k₀, Points X (liftedTest e R) → Points Y (liftedTest e R))
    (hτ : ∀ {R S : TestAlgebra k₀} (a : R ⟶ S) (p : Points X (liftedTest e R)),
      τ S (mapPoints (liftedMap e a) p) = mapPoints (liftedMap e a) (τ R p)) :
    ∃ f : X ⟶ Y, ∀ R : TestAlgebra k₀, ∀ p : Points X (liftedTest e R),
      τ R p = p ≫ f := by
  let I := liftedSpecIso e P
  let R₀ := transportedCoordinates e P
  let q := τ R₀ I.hom
  refine ⟨I.inv ≫ q, ?_⟩
  intro R p
  obtain ⟨b, rfl⟩ := (transportedSchemePoints e P R).surjective p
  obtain ⟨a, rfl⟩ := (specPointsEquiv R₀ R).surjective b
  have ha : specPointsEquiv R₀ R a = mapPoints a (𝟙 (transportedScheme e P)) :=
    (Category.comp_id ((testSpec k₀).map a.op)).symm
  rw [ha, transportedSchemePoints_naturality, transportedSchemePoints_id]
  change τ R (mapPoints (liftedMap e a) I.hom) = _
  rw [hτ]
  change (testSpec F).map (liftedMap e a).op ≫ q =
    (((testSpec F).map (liftedMap e a).op) ≫ I.hom) ≫ I.inv ≫ q
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end LiftedPoints

section LiftedGroupHom

open CategoryTheory.MonoidalCategory CategoryTheory.Limits

variable (e : F ≃+* k₀) (A : AffineAlgebraicGroup F) {B : GroupScheme F}

private theorem groupHom_of_liftedPoints
    (τ : ∀ R : TestAlgebra k₀, GroupPoints A.val (liftedTest e R) →*
      GroupPoints B (liftedTest e R))
    (hτ : ∀ {R S : TestAlgebra k₀} (a : R ⟶ S) (p : GroupPoints A.val (liftedTest e R)),
      τ S (mapPoints (liftedMap e a) p) =
        mapPoints (liftedMap e a) (τ R p)) :
    ∃ f : A.val ⟶ B, ∀ R : TestAlgebra k₀, ∀ p : GroupPoints A.val (liftedTest e R),
      τ R p = ((groupPointsFunctor F).map f).app (liftedTest e R) p := by
  let P := affinePresentation A.val.X A.property.1 A.property.2.1
  obtain ⟨f, hf⟩ := hom_of_liftedPoints e P (fun R p => τ R p) hτ
  letI : IsMonHom f := by
    constructor
    · let U : SchemeOver F := 𝟙_ (SchemeOver F)
      have hUa : IsAffine U.left := by
        change IsAffine (Spec (CommRingCat.of F))
        infer_instance
      have hUf : LocallyOfFiniteType U.hom := by
        change LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of F)))
        infer_instance
      apply hom_ext_of_liftedPoints e (affinePresentation U hUa hUf)
      intro R p
      rw [show p = toUnit ((testSpec F).obj (op (liftedTest e R))) from toUnit_unique _ _]
      change (1 : Points A.val.X (liftedTest e R)) ≫ f = 1
      rw [← hf R]
      exact (τ R).map_one
    · let X := A.val.X
      let U : SchemeOver F := X ⊗ X
      have hXa : IsAffine X.left := A.property.1
      have hXf : LocallyOfFiniteType X.hom := A.property.2.1
      have hUa : IsAffine U.left := by
        change IsAffine (pullback X.hom X.hom)
        infer_instance
      have hUf : LocallyOfFiniteType U.hom := by
        have hs : LocallyOfFiniteType ((snd X X).left ≫ X.hom) := by
          change LocallyOfFiniteType (pullback.snd X.hom X.hom ≫ X.hom)
          infer_instance
        exact (Over.w (snd X X)) ▸ hs
      apply hom_ext_of_liftedPoints e (affinePresentation U hUa hUf)
      intro R p
      let x := p ≫ fst X X
      let y := p ≫ snd X X
      calc
        p ≫ μ[X] ≫ f = (x * y) ≫ f := by simp [x, y, Hom.mul_def]
        _ = (x ≫ f) * (y ≫ f) := by
          rw [← hf R (x * y), ← hf R x, ← hf R y]
          exact (τ R).map_mul x y
        _ = p ≫ (f ⊗ₘ f) ≫ μ[B.X] := by
          have hl : lift (x ≫ f) (y ≫ f) = p ≫ (f ⊗ₘ f) := by
            apply CartesianMonoidalCategory.hom_ext <;> simp [x, y]
          simp only [Hom.mul_def, hl, Category.assoc]
  exact ⟨Grp.homMk f, hf⟩

end LiftedGroupHom

section ExtensionComparison

variable {E : Type u} [Field E] [Algebra F E] {L : Type} [Field L] [Algebra k₀ L]
variable (e : F ≃+* k₀) (b : E ≃+* L)

private def restrictLiftedIso
    (h : ∀ x : F, b (algebraMap F E x) = algebraMap k₀ L (e x)) (R : TestAlgebra L) :
    (restrictTestAlgebra F E).obj (liftedTest b R) ≅
      liftedTest e ((restrictTestAlgebra k₀ L).obj R) := by
  let A := (restrictTestAlgebra F E).obj (liftedTest b R)
  let B := liftedTest e ((restrictTestAlgebra k₀ L).obj R)
  have hc (x : F) : @algebraMap F A _ _ A.algebra x = @algebraMap F B _ _ B.algebra x := by
    change ULift.up (algebraMap L R (b (algebraMap F E x))) =
      ULift.up (algebraMap L R (algebraMap k₀ L (e x)))
    rw [h]
  let f : A ⟶ B := ConcreteCategory.ofHom (C := CommAlgCat F)
    (@AlgHom.mk F A B _ _ _ A.algebra B.algebra (RingHom.id _) hc)
  let g : B ⟶ A := ConcreteCategory.ofHom (C := CommAlgCat F)
    (@AlgHom.mk F B A _ _ _ B.algebra A.algebra (RingHom.id _) (fun x => (hc x).symm))
  exact
    { hom := f
      inv := g
      hom_inv_id := CommAlgCat.hom_ext
        (@AlgHom.ext F A A _ _ _ A.algebra A.algebra _ _ (fun _ => rfl))
      inv_hom_id := CommAlgCat.hom_ext
        (@AlgHom.ext F B B _ _ _ B.algebra B.algebra _ _ (fun _ => rfl)) }

private theorem restrictLiftedIso_naturality
    (h : ∀ x : F, b (algebraMap F E x) = algebraMap k₀ L (e x))
    {R S : TestAlgebra L} (a : R ⟶ S) :
    (restrictLiftedIso e b h R).inv ≫ (restrictTestAlgebra F E).map (liftedMap b a) =
      liftedMap e ((restrictTestAlgebra k₀ L).map a) ≫ (restrictLiftedIso e b h S).inv := by
  let A := liftedTest e ((restrictTestAlgebra k₀ L).obj R)
  let B := (restrictTestAlgebra F E).obj (liftedTest b S)
  exact CommAlgCat.hom_ext
    (@AlgHom.ext F A B _ _ _ A.algebra B.algebra _ _ (fun _ => rfl))

private theorem baseChangePointGroupEquiv_map {k T : Type u} [Field k] [Field T] [Algebra k T]
    (G : GroupScheme k) {R S : TestAlgebra T} (a : R ⟶ S)
    (p : GroupPoints ((groupBaseChange k T).obj G) R) :
    baseChangePointGroupEquiv T G S (((groupPointsFunctor T).obj
        ((groupBaseChange k T).obj G)).map a p) =
      ((groupPointsFunctor k).obj G).map ((restrictTestAlgebra k T).map a)
        (baseChangePointGroupEquiv T G R p) :=
  baseChangePointsNaturality k T G.X a p

variable {G : GroupScheme F} {H : GroupScheme k₀}
  (compare : ∀ R : TestAlgebra k₀, GroupPoints H R ≃* GroupPoints G (liftedTest e R))

private def extensionPointComparison
    (h : ∀ x : F, b (algebraMap F E x) = algebraMap k₀ L (e x)) (R : TestAlgebra L) :
    GroupPoints ((groupBaseChange k₀ L).obj H) R ≃*
      GroupPoints ((groupBaseChange F E).obj G) (liftedTest b R) :=
  (baseChangePointGroupEquiv L H R).trans <|
    (compare ((restrictTestAlgebra k₀ L).obj R)).trans <|
    ((((groupPointsFunctor F).obj G).mapIso (restrictLiftedIso e b h R).symm).groupIsoToMulEquiv).trans
      (baseChangePointGroupEquiv E G (liftedTest b R)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPointComparison_naturality
    (h : ∀ x : F, b (algebraMap F E x) = algebraMap k₀ L (e x))
    (hnat : ∀ {R S : TestAlgebra k₀} (a : R ⟶ S) (p : GroupPoints H R),
      compare S (((groupPointsFunctor k₀).obj H).map a p) =
        ((groupPointsFunctor F).obj G).map (liftedMap e a) (compare R p))
    {R S : TestAlgebra L} (a : R ⟶ S) (p : GroupPoints ((groupBaseChange k₀ L).obj H) R) :
    extensionPointComparison e b compare h S
        (((groupPointsFunctor L).obj ((groupBaseChange k₀ L).obj H)).map a p) =
      ((groupPointsFunctor E).obj ((groupBaseChange F E).obj G)).map (liftedMap b a)
        (extensionPointComparison e b compare h R p) := by
  apply (baseChangePointGroupEquiv E G (liftedTest b S)).injective
  rw [baseChangePointGroupEquiv_map]
  let U := (groupPointsFunctor F).obj G
  let R' := (restrictTestAlgebra k₀ L).obj R
  let S' := (restrictTestAlgebra k₀ L).obj S
  let a' := (restrictTestAlgebra k₀ L).map a
  let p' : GroupPoints H R' := baseChangePointGroupEquiv L H R p
  let iR := (restrictLiftedIso e b h R).inv
  let iS := (restrictLiftedIso e b h S).inv
  change (baseChangePointGroupEquiv E G (liftedTest b S))
      ((baseChangePointGroupEquiv E G (liftedTest b S)).symm
        (U.map iS (compare S' (baseChangePointGroupEquiv L H S
          (((groupPointsFunctor L).obj ((groupBaseChange k₀ L).obj H)).map a p))))) =
    U.map ((restrictTestAlgebra F E).map (liftedMap b a))
      ((baseChangePointGroupEquiv E G (liftedTest b R))
        ((baseChangePointGroupEquiv E G (liftedTest b R)).symm (U.map iR (compare R' p'))))
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    baseChangePointGroupEquiv_map, hnat]
  have hc := congrArg (fun f => U.map f (compare R' p')) (restrictLiftedIso_naturality e b h a)
  simpa only [Functor.map_comp, GrpCat.comp_apply] using hc.symm

end ExtensionComparison

private abbrev closureEquiv (e : F ≃+* k₀) :
    AlgebraicClosure F ≃+* AlgebraicClosure k₀ :=
  IsAlgClosure.equivOfEquiv (AlgebraicClosure F) (AlgebraicClosure k₀) e

section ComparingCoordinateRings

variable (e : F ≃+* k₀) {X : SchemeOver k₀} {Y : SchemeOver F}
  (P : AffinePresentation X) (Q : AffinePresentation Y)

private def presentedPoints {k : Type u} [Field k] {S : SchemeOver k}
    (D : AffinePresentation S) (R : TestAlgebra k) : (D.coordinates ⟶ R) ≃ Points S R :=
  (specPointsEquiv D.coordinates R).trans D.iso.homToEquiv

private theorem presentedPoints_comp {k : Type u} [Field k] {T : SchemeOver k}
    (D : AffinePresentation T) {R S : TestAlgebra k} (f : D.coordinates ⟶ R) (a : R ⟶ S) :
    presentedPoints D S (f ≫ a) = mapPoints a (presentedPoints D R f) := by
  change specPointsEquiv D.coordinates S (f ≫ a) ≫ D.iso.hom =
    mapPoints a (specPointsEquiv D.coordinates R f ≫ D.iso.hom)
  rw [specPointsEquiv_comp f a]
  exact Category.assoc _ _ _

private structure CoordinateComparison
    (q : ∀ R : TestAlgebra k₀, Points X R ≃ Points Y (liftedTest e R)) where
  ringEquiv : Q.coordinates ≃+* P.coordinates
  eval (R : TestAlgebra k₀) (f : P.coordinates ⟶ R) (a : Q.coordinates) :
    ((presentedPoints Q (liftedTest e R)).symm (q R (presentedPoints P R f))).hom a =
      ULift.up (f.hom (ringEquiv a))

set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- Compare the coordinate algebras of affine schemes from their natural
point comparison on lifted test algebras. -/
private def coordinatesIsoOfPointComparison
    (q : ∀ R : TestAlgebra k₀, Points X R ≃ Points Y (liftedTest e R))
    (hnat : ∀ {R S : TestAlgebra k₀} (a : R ⟶ S) (p : Points X R),
      q S (mapPoints a p) = mapPoints (liftedMap e a) (q R p)) :
    CoordinateComparison e P Q q := by
  let A := P.coordinates
  let B := transportedCoordinates e Q
  let r (R : TestAlgebra k₀) : (B ⟶ R) ≃ Points Y (liftedTest e R) :=
    (specPointsEquiv B R).trans (transportedSchemePoints e Q R)
  have hr {R S : TestAlgebra k₀} (f : B ⟶ R) (a : R ⟶ S) :
      r S (f ≫ a) = mapPoints (liftedMap e a) (r R f) := by
    change transportedSchemePoints e Q S (specPointsEquiv B S (f ≫ a)) = _
    rw [specPointsEquiv_comp f a]
    exact transportedSchemePoints_naturality e Q a _
  let d (R : TestAlgebra k₀) : (A ⟶ R) ≃ (B ⟶ R) :=
    (presentedPoints P R).trans ((q R).trans (r R).symm)
  have hleft {R : TestAlgebra k₀} (f : A ⟶ R) :
      r R (d R f) = q R (presentedPoints P R f) := (r R).apply_symm_apply _
  have hd {R S : TestAlgebra k₀} (f : A ⟶ R) (a : R ⟶ S) :
      d S (f ≫ a) = d R f ≫ a := by
    apply (r S).injective
    rw [hleft, hr, hleft, presentedPoints_comp]
    exact hnat a _
  let f : B ⟶ A := d A (𝟙 A)
  let g : A ⟶ B := (d B).symm (𝟙 B)
  have hg : d B g = 𝟙 B := (d B).apply_symm_apply _
  let i : B ≅ A := by
    refine ⟨f, g, ?_, ?_⟩
    · have h := (hd (𝟙 A) g).symm
      rw [Category.id_comp] at h
      exact h.trans hg
    · apply (d A).injective
      rw [hd, hg, Category.id_comp]
  let eqv := smallerAlgebraEquiv e Q.coordinates Q.finiteType
  refine ⟨eqv.trans (CommAlgCat.algEquivOfIso i).toRingEquiv, ?_⟩
  intro R g a
  have he : d R g = f ≫ g := by
    simpa only [Category.id_comp] using (hd (𝟙 A) g)
  rw [← hleft, he]
  simp only [r, B, Equiv.trans_apply, transportedSchemePoints, Equiv.symm_apply_apply]
  change ((presentedPoints Q (liftedTest e R)).symm
    (presentedPoints Q (liftedTest e R)
      (liftAlgebraMap e eqv (smallerAlgebraEquiv_algebraMap e Q.coordinates Q.finiteType) (f ≫ g)))).hom a = _
  rw [Equiv.symm_apply_apply]
  rfl

end ComparingCoordinateRings

section BasicGeometry

private theorem isZero_of_subsingleton_liftedPoints (e : F ≃+* k₀) (G : AffineAlgebraicGroup F)
    (hs : ∀ R : TestAlgebra k₀, Subsingleton (GroupPoints G.val (liftedTest e R))) :
    IsZero G.val := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Grp.hom_ext
  let P := affinePresentation G.val.X G.property.1 G.property.2.1
  apply hom_ext_of_liftedPoints e P
  intro R p
  exact (hs R).elim _ _

private theorem subsingleton_points_of_isZero {k : Type u} [Field k] (G : GroupScheme k)
    (hG : IsZero G) (R : TestAlgebra k) : Subsingleton (GroupPoints G R) := by
  let e := (Grp.forget _).mapIso (hG.iso (Grp.isZero_trivial _))
  refine ⟨fun p q => (cancel_mono e.hom).mp ?_⟩
  change p ≫ e.hom = q ≫ e.hom
  exact toUnit_unique _ _

end BasicGeometry

section ScalarLift

open scoped TensorProduct

private def liftTestFunctor (e : F ≃+* k₀) : TestAlgebra k₀ ⥤ TestAlgebra F where
  obj := liftedTest e
  map := liftedMap e
  map_id A := CommAlgCat.hom_ext
    (@AlgHom.ext F (liftedTest e A) (liftedTest e A) _ _ _ (liftedTest e A).algebra
      (liftedTest e A).algebra _ _ (fun _ => rfl))
  map_comp {A _ C} _ _ := CommAlgCat.hom_ext
    (@AlgHom.ext F (liftedTest e A) (liftedTest e C) _ _ _ (liftedTest e A).algebra
      (liftedTest e C).algebra _ _ (fun _ => rfl))

private def liftTestFullyFaithful (e : F ≃+* k₀) : (liftTestFunctor e).FullyFaithful where
  preimage {A B} f := CommAlgCat.ofHom
    ({ toRingHom := ULift.ringEquiv.toRingHom.comp
        (f.hom.toRingHom.comp ULift.ringEquiv.symm.toRingHom)
       commutes' := fun x => by
         have h := f.hom.commutes (e.symm x)
         change f.hom (ULift.up (algebraMap k₀ A (e (e.symm x)))) =
           ULift.up (algebraMap k₀ B (e (e.symm x))) at h
         rw [e.apply_symm_apply] at h
         exact congrArg ULift.down h } : A →ₐ[k₀] B)
  map_preimage {A B} _ := CommAlgCat.hom_ext
    (@AlgHom.ext F (liftedTest e A) (liftedTest e B) _ _ _ (liftedTest e A).algebra
      (liftedTest e B).algebra _ _ (fun _ => rfl))
  preimage_map _ := CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)

private abbrev lowerScalars (e : F ≃+* k₀) (T : TestAlgebra F) : Algebra k₀ T :=
  ((algebraMap F T).comp e.symm.toRingHom).toAlgebra

/-- Regard a homomorphism from a lifted algebra as a homomorphism before the lift,
with scalars on its target restricted by the inverse field equivalence. -/
private def liftHomEquiv (e : F ≃+* k₀) (A : TestAlgebra k₀) (T : TestAlgebra F) :
    letI := lowerScalars e T
    (liftedTest e A ⟶ T) ≃ (A →ₐ[k₀] T) := by
  letI := lowerScalars e T
  letI := liftedAlgebra e A
  refine
    { toFun := fun f => ⟨f.hom.toRingHom.comp ULift.ringEquiv.symm.toRingHom, ?_⟩
      invFun := fun f => CommAlgCat.ofHom ⟨f.toRingHom.comp ULift.ringEquiv.toRingHom, ?_⟩
      left_inv := fun _ => CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)
      right_inv := fun _ => AlgHom.ext fun _ => rfl }
  · intro x
    have h := f.hom.commutes (e.symm x)
    change f.hom (ULift.up (algebraMap k₀ A (e (e.symm x)))) = algebraMap F T (e.symm x) at h
    change f.hom (ULift.up (algebraMap k₀ A x)) = algebraMap F T (e.symm x)
    simpa only [e.apply_symm_apply] using h
  · intro x
    have h := f.commutes (e x)
    change f (algebraMap k₀ A (e x)) = algebraMap F T (e.symm (e x)) at h
    change f (algebraMap k₀ A (e x)) = algebraMap F T x
    simpa only [e.symm_apply_apply] using h

private def liftBinaryCofan (e : F ≃+* k₀) (A B : TestAlgebra k₀) :
    BinaryCofan (liftedTest e A) (liftedTest e B) :=
  BinaryCofan.mk (liftedMap e (CommAlgCat.binaryCofan A B).inl)
    (liftedMap e (CommAlgCat.binaryCofan A B).inr)

private def liftBinaryCofanIsColimit (e : F ≃+* k₀) (A B : TestAlgebra k₀) :
    IsColimit (liftBinaryCofan e A B) := by
  refine BinaryCofan.IsColimit.mk _ (fun {T} f g => ?_) ?_ ?_ ?_
  · letI := lowerScalars e T
    exact (liftHomEquiv e ((CommAlgCat.binaryCofan A B).pt) T).symm
      (Algebra.TensorProduct.lift (liftHomEquiv e A T f) (liftHomEquiv e B T g)
        fun _ _ => Commute.all _ _)
  · intro T f g
    letI := lowerScalars e T
    apply (liftHomEquiv e A T).injective
    apply AlgHom.ext
    intro a
    change Algebra.TensorProduct.lift (liftHomEquiv e A T f) (liftHomEquiv e B T g)
        (fun _ _ => Commute.all _ _) (a ⊗ₜ[k₀] (1 : B)) = f.hom (ULift.up a)
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  · intro T f g
    letI := lowerScalars e T
    apply (liftHomEquiv e B T).injective
    apply AlgHom.ext
    intro b
    change Algebra.TensorProduct.lift (liftHomEquiv e A T f) (liftHomEquiv e B T g)
        (fun _ _ => Commute.all _ _) ((1 : A) ⊗ₜ[k₀] b) = g.hom (ULift.up b)
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  · intro T f g m hm₁ hm₂
    letI := lowerScalars e T
    apply (liftHomEquiv e ((CommAlgCat.binaryCofan A B).pt) T).injective
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro a
      exact (congrArg (fun h : liftedTest e A ⟶ T => h.hom (ULift.up a)) hm₁).trans
        (by
          change f.hom (ULift.up a) =
            Algebra.TensorProduct.lift (liftHomEquiv e A T f) (liftHomEquiv e B T g)
              (fun _ _ => Commute.all _ _) (a ⊗ₜ[k₀] (1 : B))
          rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
          rfl)
    · apply AlgHom.ext
      intro b
      exact (congrArg (fun h : liftedTest e B ⟶ T => h.hom (ULift.up b)) hm₂).trans
        (by
          change g.hom (ULift.up b) =
            Algebra.TensorProduct.lift (liftHomEquiv e A T f) (liftHomEquiv e B T g)
              (fun _ _ => Commute.all _ _) ((1 : A) ⊗ₜ[k₀] b)
          rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
          rfl)

private theorem scalarLiftPreservesProducts (e : F ≃+* k₀) :
    PreservesFiniteProducts (liftTestFunctor e).op := by
  have hT : IsIso (CartesianMonoidalCategory.terminalComparison (liftTestFunctor e).op) := by
    letI := liftedAlgebra e (CommAlgCat.of k₀ k₀)
    let i : CommAlgCat.of F F ≅ liftedTest e (CommAlgCat.of k₀ k₀) :=
      CommAlgCat.isoMk
        ({ e.trans ULift.ringEquiv.symm with commutes' := fun _ => rfl } :
          F ≃ₐ[F] liftedTest e (CommAlgCat.of k₀ k₀))
    have he : CartesianMonoidalCategory.terminalComparison (liftTestFunctor e).op = i.op.hom := by
      exact isTerminalTensorUnit.hom_ext _ _
    rw [he]
    exact ⟨⟨i.op.inv, i.op.hom_inv_id, i.op.inv_hom_id⟩⟩
  letI hi (A B : (TestAlgebra k₀)ᵒᵖ) : IsIso (CartesianMonoidalCategory.prodComparison (liftTestFunctor e).op A B) := by
    let h : IsLimit (BinaryFan.mk ((liftTestFunctor e).op.map (fst A B))
        ((liftTestFunctor e).op.map (snd A B))) :=
      BinaryCofan.IsColimit.op (liftBinaryCofanIsColimit e A.unop B.unop)
    let i := IsLimit.conePointUniqueUpToIso h (tensorProductIsBinaryProduct
      ((liftTestFunctor e).op.obj A) ((liftTestFunctor e).op.obj B))
    have he : CartesianMonoidalCategory.prodComparison (liftTestFunctor e).op A B = i.hom := rfl
    rw [he]
    infer_instance
  letI := preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison
    (liftTestFunctor e).op
  letI := preservesLimit_empty_of_isIso_terminalComparison (liftTestFunctor e).op
  letI := preservesLimitsOfShape_pempty_of_preservesTerminal (liftTestFunctor e).op
  exact .of_preserves_binary_and_terminal _

end ScalarLift

section GroupComparison

private structure GroupComparison (e : F ≃+* k₀)
    (G : AffineAlgebraicGroup F) (H : AffineAlgebraicGroup k₀) where
  equiv (R : TestAlgebra k₀) : GroupPoints H.val R ≃* GroupPoints G.val (liftedTest e R)
  naturality {R S : TestAlgebra k₀} (a : R ⟶ S) (p : GroupPoints H.val R) :
    equiv S (mapPoints a p) = mapPoints (liftedMap e a) (equiv R p)

private abbrev pointMap {k : Type u} [Field k] {G H : GroupScheme k} (f : G ⟶ H)
    (R : TestAlgebra k) := ((groupPointsFunctor k).map f).app R

variable {e : F ≃+* k₀} {G₁ G₂ : AffineAlgebraicGroup F} {H₁ H₂ : AffineAlgebraicGroup k₀}

private def GroupComparison.smallModel (e : F ≃+* k₀) (G : AffineAlgebraicGroup F) :
    GroupComparison e G (smallGroupModel e
      (affinePresentation G.val.X G.property.1 G.property.2.1)) where
  equiv := smallGroupPoints e _
  naturality := smallGroupPoints_naturality e _

private def Compatible (P : GroupComparison e G₁ H₁) (Q : GroupComparison e G₂ H₂)
    (f : G₁.val ⟶ G₂.val) (g : H₁.val ⟶ H₂.val) : Prop :=
  ∀ (R : TestAlgebra k₀) (p : GroupPoints H₁.val R),
    Q.equiv R (pointMap g R p) = pointMap f (liftedTest e R) (P.equiv R p)

private theorem GroupComparison.existsSmallMap (P : GroupComparison e G₁ H₁)
    (Q : GroupComparison e G₂ H₂) (f : G₁.val ⟶ G₂.val) :
    ∃ g : H₁.val ⟶ H₂.val, Compatible P Q f g := by
  let τ : (groupPointsFunctor k₀).obj H₁.val ⟶ (groupPointsFunctor k₀).obj H₂.val :=
    { app := fun R => GrpCat.ofHom ((Q.equiv R).symm.toMonoidHom.comp
        ((pointMap f (liftedTest e R)).hom.comp (P.equiv R).toMonoidHom))
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro p
        apply (Q.equiv S).injective
        change Q.equiv S ((Q.equiv S).symm
          (pointMap f _ (P.equiv S (mapPoints a p)))) =
          Q.equiv S (mapPoints a ((Q.equiv R).symm (pointMap f _ (P.equiv R p))))
        rw [MulEquiv.apply_symm_apply, Q.naturality, P.naturality, MulEquiv.apply_symm_apply]
        exact NatTrans.naturality_apply ((groupPointsFunctor F).map f) (liftedMap e a) _ }
  let g := (groupHomEquiv _ _ H₁.property.1).symm τ
  refine ⟨g, fun R p => ?_⟩
  have hg : (groupPointsFunctor k₀).map g = τ := (groupHomEquiv _ _ H₁.property.1).apply_symm_apply τ
  unfold pointMap at *
  rw [hg]
  exact (Q.equiv R).apply_symm_apply _

private theorem GroupComparison.existsLargeMap (P : GroupComparison e G₁ H₁)
    (Q : GroupComparison e G₂ H₂) (g : H₁.val ⟶ H₂.val) :
    ∃ f : G₁.val ⟶ G₂.val, Compatible P Q f g := by
  let τ (R : TestAlgebra k₀) : GroupPoints G₁.val (liftedTest e R) →*
      GroupPoints G₂.val (liftedTest e R) :=
    (Q.equiv R).toMonoidHom.comp ((pointMap g R).hom.comp (P.equiv R).symm.toMonoidHom)
  have hτ {R S : TestAlgebra k₀} (a : R ⟶ S) (p : GroupPoints G₁.val (liftedTest e R)) :
      τ S (mapPoints (liftedMap e a) p) = mapPoints (liftedMap e a) (τ R p) := by
    obtain ⟨x, rfl⟩ := (P.equiv R).surjective p
    rw [← P.naturality]
    change Q.equiv S (pointMap g S ((P.equiv S).symm (P.equiv S (mapPoints a x)))) =
      mapPoints (liftedMap e a)
        (Q.equiv R (pointMap g R ((P.equiv R).symm (P.equiv R x))))
    rw [← Q.naturality]
    have h1 := (P.equiv S).symm_apply_apply (mapPoints a x)
    have h2 : pointMap g S (mapPoints a x) = mapPoints a (pointMap g R x) :=
      NatTrans.naturality_apply ((groupPointsFunctor k₀).map g) a x
    have h3 := (P.equiv R).symm_apply_apply x
    exact congrArg (Q.equiv S)
      ((congrArg (fun y : GroupPoints H₁.val S => pointMap g S y) h1).trans
        (h2.trans (congrArg (fun y : GroupPoints H₁.val R => mapPoints a (pointMap g R y)) h3.symm)))
  obtain ⟨f, hf⟩ := groupHom_of_liftedPoints e G₁ τ hτ
  refine ⟨f, fun R p => ?_⟩
  rw [← hf R]
  change _ = Q.equiv R (pointMap g R ((P.equiv R).symm (P.equiv R p)))
  rw [MulEquiv.symm_apply_apply]

private theorem GroupComparison.smallMap_unique (P : GroupComparison e G₁ H₁)
    (Q : GroupComparison e G₂ H₂) {f : G₁.val ⟶ G₂.val} {g g' : H₁.val ⟶ H₂.val}
    (h : Compatible P Q f g) (h' : Compatible P Q f g') : g = g' := by
  apply (groupHomEquiv _ _ H₁.property.1).injective
  ext R x
  exact (Q.equiv R).injective ((h R x).trans (h' R x).symm)

private theorem GroupComparison.largeMap_unique (P : GroupComparison e G₁ H₁)
    (Q : GroupComparison e G₂ H₂) {f f' : G₁.val ⟶ G₂.val} {g : H₁.val ⟶ H₂.val}
    (h : Compatible P Q f g) (h' : Compatible P Q f' g) : f = f' := by
  apply Grp.hom_ext
  apply hom_ext_of_liftedPoints e (affinePresentation G₁.val.X G₁.property.1 G₁.property.2.1)
  intro R x
  obtain ⟨p, rfl⟩ := (P.equiv R).surjective x
  exact (h R p).symm.trans (h' R p)

private theorem Compatible.id (P : GroupComparison e G₁ H₁) :
    Compatible P P (𝟙 G₁.val) (𝟙 H₁.val) := by
  intro R p
  simp [pointMap]

private theorem Compatible.comp {G₃ : AffineAlgebraicGroup F} {H₃ : AffineAlgebraicGroup k₀}
    {P : GroupComparison e G₁ H₁} {Q : GroupComparison e G₂ H₂} {U : GroupComparison e G₃ H₃}
    {f : G₁.val ⟶ G₂.val} {f' : G₂.val ⟶ G₃.val} {g : H₁.val ⟶ H₂.val} {g' : H₂.val ⟶ H₃.val}
    (h : Compatible P Q f g) (h' : Compatible Q U f' g') :
    Compatible P U (f ≫ f') (g ≫ g') := by
  intro R p
  simp only [pointMap, Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply]
  rw [← show pointMap g' R (pointMap g R p) = _ from rfl]
  rw [h', h]

private theorem Compatible.isIso_iff {P : GroupComparison e G₁ H₁}
    {Q : GroupComparison e G₂ H₂} {f : G₁.val ⟶ G₂.val} {g : H₁.val ⟶ H₂.val}
    (h : Compatible P Q f g) :
    IsIso f ↔ IsIso g := by
  constructor
  · intro hf
    obtain ⟨g', hg'⟩ := Q.existsSmallMap P (inv f)
    refine ⟨⟨g', ?_, ?_⟩⟩
    · apply P.smallMap_unique P (h.comp hg')
      simpa only [IsIso.hom_inv_id] using Compatible.id P
    · apply Q.smallMap_unique Q (hg'.comp h)
      simpa only [IsIso.inv_hom_id] using Compatible.id Q
  · intro hg
    obtain ⟨f', hf'⟩ := Q.existsLargeMap P (inv g)
    refine ⟨⟨f', ?_, ?_⟩⟩
    · apply P.largeMap_unique P (h.comp hf')
      simpa only [IsIso.hom_inv_id] using Compatible.id P
    · apply Q.largeMap_unique Q (hf'.comp h)
      simpa only [IsIso.inv_hom_id] using Compatible.id Q

end GroupComparison

section LargeModel

private local instance {k : Type*} [Field k] : (testSpec k).Braided :=
  AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)

private abbrev scalarLift (e : F ≃+* k₀) : (TestAlgebra k₀)ᵒᵖ ⥤ (TestAlgebra F)ᵒᵖ :=
  (liftTestFunctor e).op

private local instance (e : F ≃+* k₀) : (scalarLift e).Monoidal := by
  letI : PreservesFiniteProducts (scalarLift e) := scalarLiftPreservesProducts e
  exact Functor.Monoidal.ofChosenFiniteProducts _

private theorem liftedTest_finiteType (e : F ≃+* k₀) (A : TestAlgebra k₀)
    (h : Algebra.FiniteType k₀ A) :
    @Algebra.FiniteType F (liftedTest e A) _ _ (liftedTest e A).algebra := by
  letI := liftedAlgebra e A
  change Algebra.FiniteType F (ULift.{u} A)
  apply RingHom.finiteType_algebraMap.mp
  change ((ULift.ringEquiv.symm.toRingHom.comp (algebraMap k₀ A)).comp e.toRingHom).FiniteType
  exact ((RingHom.FiniteType.of_surjective _ ULift.ringEquiv.symm.surjective).comp
    (RingHom.finiteType_algebraMap.mpr h)).comp (RingHom.FiniteType.of_surjective _ e.surjective)

private def affineGroupOfAlgebraObject {k : Type u} [Field k]
    (A : Grp (TestAlgebra k)ᵒᵖ) (hA : Algebra.FiniteType k A.X.unop) :
    AffineAlgebraicGroup k := by
  let G := (testSpec k).mapGrp.obj A
  refine ⟨G, ?_, ?_, ?_⟩
  · change IsAffine (Spec (CommRingCat.of A.X.unop))
    infer_instance
  · change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A.X.unop)))
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr hA)
  · change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k A.X.unop)))
    infer_instance

private def liftedGroupOfAlgebraObject (e : F ≃+* k₀)
    (A : Grp (TestAlgebra k₀)ᵒᵖ) (hA : Algebra.FiniteType k₀ A.X.unop) :
    AffineAlgebraicGroup F :=
  affineGroupOfAlgebraObject ((scalarLift e).mapGrp.obj A) (liftedTest_finiteType e _ hA)

set_option backward.isDefEq.respectTransparency false in
private def largeModelComparison (e : F ≃+* k₀) {H : AffineAlgebraicGroup k₀}
    (A : Grp (TestAlgebra k₀)ᵒᵖ) (hA : Algebra.FiniteType k₀ A.X.unop)
    (i : (testSpec k₀).mapGrp.obj A ≅ H.val) :
    GroupComparison e (liftedGroupOfAlgebraObject e A hA) H where
  equiv R := by
    letI : GrpObj A.X := A.grp
    let L := (scalarLift e).mapGrp.obj A
    letI : GrpObj L.X := L.grp
    let p := (((groupPointsFunctor k₀).mapIso i.symm).app R).groupIsoToMulEquiv
    let q := (algSpec.fullyFaithful (R := CommRingCat.of k₀)).homMulEquiv (X := op R) (M := A.X)
    let r := ((liftTestFullyFaithful e).op).homMulEquiv (X := op R) (M := A.X)
    let s := (algSpec.fullyFaithful (R := CommRingCat.of F)).homMulEquiv
      (X := op (liftedTest e R)) (M := L.X)
    exact p.trans (q.symm.trans (r.trans s))
  naturality {R S} a p := by
    let p' : Points ((testSpec k₀).obj A.X) R := pointMap i.inv R p
    have hh : pointMap i.inv S (mapPoints a p) = mapPoints a p' :=
      NatTrans.naturality_apply ((groupPointsFunctor k₀).map i.inv) a p
    let ff := algSpec.fullyFaithful (R := CommRingCat.of k₀)
    let L := scalarLift e
    change (testSpec F).map (L.map (ff.preimage (pointMap i.inv S (mapPoints a p)))) =
      (testSpec F).map (liftedMap e a).op ≫ (testSpec F).map (L.map (ff.preimage p'))
    rw [hh]
    have heq : ff.preimage (mapPoints a p') = a.op ≫ ff.preimage p' := by
      apply ff.map_injective
      exact (ff.map_preimage _).trans
        ((congrArg ((testSpec k₀).map a.op ≫ ·) (ff.map_preimage p').symm).trans
          (((testSpec k₀).map_comp a.op (ff.preimage p')).symm))
    refine (congrArg (fun h => (testSpec F).map (L.map h)) heq).trans ?_
    rw [L.map_comp, (testSpec F).map_comp]
    try rfl

private theorem existsLargeModel (e : F ≃+* k₀) (H : AffineAlgebraicGroup k₀) :
    ∃ G : AffineAlgebraicGroup F, Nonempty (GroupComparison e G H) := by
  obtain ⟨B, ⟨i⟩⟩ := essImage_hopfSpec.mpr H.property.1
  let A := ((commHopfAlgCatEquivCogrpCommAlgCat (CommRingCat.of k₀)).functor.leftOp).obj B
  have h : LocallyOfFiniteType ((testSpec k₀).mapGrp.obj A).X.hom := by
    have hh : LocallyOfFiniteType H.val.X.hom := H.property.2.1
    let j := ((Grp.forget (SchemeOver k₀)) ⋙ Over.forget _).mapIso i
    have hf : IsIso i.hom.hom.hom.left := j.isIso_hom
    have hcomp := locallyOfFiniteType_comp i.hom.hom.hom.left H.val.X.hom
    rw [Over.w i.hom.hom.hom] at hcomp
    exact hcomp
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k₀ A.X.unop))) at h
  have hA := RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h)
  exact ⟨liftedGroupOfAlgebraObject e A hA, ⟨largeModelComparison e A hA i⟩⟩

end LargeModel

section MorphismProperties

private def presentedMap {k : Type u} [Field k] {X Y : SchemeOver k}
    (P : AffinePresentation X) (Q : AffinePresentation Y) (f : X ⟶ Y) :
    Q.coordinates ⟶ P.coordinates :=
  (specPointsEquiv Q.coordinates P.coordinates).symm (P.iso.hom ≫ f ≫ Q.iso.inv)

private theorem presentedMap_spec {k : Type u} [Field k] {X Y : SchemeOver k}
    (P : AffinePresentation X) (Q : AffinePresentation Y) (f : X ⟶ Y) :
    (testSpec k).map (presentedMap P Q f).op = P.iso.hom ≫ f ≫ Q.iso.inv :=
  (specPointsEquiv Q.coordinates P.coordinates).apply_symm_apply _

private theorem presentedPoints_post {k : Type u} [Field k] {X Y : SchemeOver k}
    (P : AffinePresentation X) (Q : AffinePresentation Y) (f : X ⟶ Y)
    {R : TestAlgebra k} (a : P.coordinates ⟶ R) :
    presentedPoints Q R (presentedMap P Q f ≫ a) = presentedPoints P R a ≫ f := by
  change (testSpec k).map (presentedMap P Q f ≫ a).op ≫ Q.iso.hom =
    ((testSpec k).map a.op ≫ P.iso.hom) ≫ f
  rw [op_comp, Functor.map_comp, presentedMap_spec]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem presentedMap_morphismProperty {k : Type u} [Field k] {X Y : SchemeOver k}
    (P : AffinePresentation X) (Q : AffinePresentation Y) (f : X ⟶ Y)
    (W : MorphismProperty Scheme.{u}) [W.RespectsIso] :
    W (Spec.map (CommRingCat.ofHom (presentedMap P Q f).hom.toRingHom)) ↔ W f.left := by
  change W ((testSpec k).map (presentedMap P Q f).op).left ↔ _
  rw [presentedMap_spec]
  change W (P.iso.hom.left ≫ f.left ≫ Q.iso.inv.left) ↔ _
  letI : IsIso P.iso.hom.left := inferInstance
  letI : IsIso Q.iso.inv.left := inferInstance
  rw [W.cancel_left_of_respectsIso, W.cancel_right_of_respectsIso]

variable {e : F ≃+* k₀} {G₁ G₂ : AffineAlgebraicGroup F} {H₁ H₂ : AffineAlgebraicGroup k₀}

private def GroupComparison.coordinates (P : GroupComparison e G₁ H₁) :=
  coordinatesIsoOfPointComparison e
    (affinePresentation H₁.val.X H₁.property.1 H₁.property.2.1)
    (affinePresentation G₁.val.X G₁.property.1 G₁.property.2.1)
    (fun R => (P.equiv R).toEquiv) P.naturality

set_option backward.isDefEq.respectTransparency false in
private theorem Compatible.coordinateSquare
    {P : GroupComparison e G₁ H₁} {Q : GroupComparison e G₂ H₂}
    {f : G₁.val ⟶ G₂.val} {g : H₁.val ⟶ H₂.val} (h : Compatible P Q f g) :
    let A := affinePresentation G₁.val.X G₁.property.1 G₁.property.2.1
    let B := affinePresentation G₂.val.X G₂.property.1 G₂.property.2.1
    let C := affinePresentation H₁.val.X H₁.property.1 H₁.property.2.1
    let D := affinePresentation H₂.val.X H₂.property.1 H₂.property.2.1
    ∀ x, P.coordinates.ringEquiv ((presentedMap A B f.hom.hom).hom x) =
      (presentedMap C D g.hom.hom).hom (Q.coordinates.ringEquiv x) := by
  intro A B C D x
  let R := C.coordinates
  let a := presentedMap A B f.hom.hom
  let b := presentedMap C D g.hom.hom
  let j := (presentedPoints A (liftedTest e R)).symm
    (P.equiv R (presentedPoints C R (𝟙 R)))
  have hj : j.hom (a.hom x) = ULift.up (P.coordinates.ringEquiv (a.hom x)) :=
    P.coordinates.eval R (𝟙 R) (a.hom x)
  have hq := Q.coordinates.eval R b x
  change ((presentedPoints B (liftedTest e R)).symm
    (Q.equiv R (presentedPoints D R b))).hom x =
    ULift.up (b.hom (Q.coordinates.ringEquiv x)) at hq
  have hc : Q.equiv R (presentedPoints D R b) =
      presentedPoints B (liftedTest e R) (a ≫ j) := by
    have hd := presentedPoints_post C D g.hom.hom (𝟙 R)
    rw [Category.comp_id] at hd
    rw [hd, presentedPoints_post]
    change Q.equiv R (pointMap g R (presentedPoints C R (𝟙 R))) =
      pointMap f (liftedTest e R) (presentedPoints A (liftedTest e R) j)
    rw [h R]
    congr 1
    exact ((presentedPoints A (liftedTest e R)).apply_symm_apply _).symm
  rw [hc, Equiv.symm_apply_apply] at hq
  exact ULift.up.inj (hj.symm.trans hq)

private theorem specMap_closed_iff {R S : CommRingCat.{u}} (r : R ⟶ S) :
    IsClosedImmersion (Spec.map r) ↔ Function.Surjective r := by
  refine ⟨fun h => ?_, IsClosedImmersion.spec_of_surjective r⟩
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map r)).2
  have he : (Scheme.ΓSpecIso _).inv ≫ (Spec.map r).appTop ≫ (Scheme.ΓSpecIso _).hom = r := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← he]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2.comp
    (hs.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2)

private local instance : MorphismProperty.RespectsIso (@IsFinite.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun {_ _} f hf => by
    letI : IsIso f := hf
    infer_instance)

private local instance : MorphismProperty.RespectsIso (@Flat.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun {_ _} f hf => by
    letI : IsIso f := hf
    infer_instance)

/-- Compatible group maps have coordinate maps conjugate by ring isomorphisms. -/
private theorem Compatible.morphismProperties
    {P : GroupComparison e G₁ H₁} {Q : GroupComparison e G₂ H₂}
    {f : G₁.val ⟶ G₂.val} {g : H₁.val ⟶ H₂.val} (h : Compatible P Q f g) :
    (IsClosedImmersion f.hom.hom.left ↔ IsClosedImmersion g.hom.hom.left) ∧
    (IsFinite f.hom.hom.left ↔ IsFinite g.hom.hom.left) ∧
    (Flat f.hom.hom.left ↔ Flat g.hom.hom.left) ∧
    (Surjective f.hom.hom.left ↔ Surjective g.hom.hom.left) := by
  let A := affinePresentation G₁.val.X G₁.property.1 G₁.property.2.1
  let B := affinePresentation G₂.val.X G₂.property.1 G₂.property.2.1
  let C := affinePresentation H₁.val.X H₁.property.1 H₁.property.2.1
  let D := affinePresentation H₂.val.X H₂.property.1 H₂.property.2.1
  let a : B.coordinates →+* A.coordinates := (presentedMap A B f.hom.hom).hom.toRingHom
  let b : D.coordinates →+* C.coordinates := (presentedMap C D g.hom.hom).hom.toRingHom
  let p : A.coordinates ≃+* C.coordinates := P.coordinates.ringEquiv
  let q : B.coordinates ≃+* D.coordinates := Q.coordinates.ringEquiv
  have hpb (x : B.coordinates) : p (a x) = b (q x) := h.coordinateSquare x
  have ha : a = p.symm.toRingHom.comp (b.comp q.toRingHom) := by
    ext x
    exact (p.symm_apply_apply (a x)).symm.trans (congrArg p.symm (hpb x))
  have hb : b = p.toRingHom.comp (a.comp q.symm.toRingHom) := by
    ext x
    change b x = p (a (q.symm x))
    rw [hpb, q.apply_symm_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← presentedMap_morphismProperty A B f.hom.hom (@IsClosedImmersion),
      ← presentedMap_morphismProperty C D g.hom.hom (@IsClosedImmersion),
      specMap_closed_iff, specMap_closed_iff]
    change Function.Surjective a ↔ Function.Surjective b
    exact ⟨fun k => hb ▸ p.surjective.comp (k.comp q.symm.surjective),
      fun k => ha ▸ p.symm.surjective.comp (k.comp q.surjective)⟩
  · rw [← presentedMap_morphismProperty A B f.hom.hom (@IsFinite),
      ← presentedMap_morphismProperty C D g.hom.hom (@IsFinite),
      IsFinite.SpecMap_iff, IsFinite.SpecMap_iff]
    change a.Finite ↔ b.Finite
    exact ⟨fun k => hb ▸ (RingHom.Finite.of_surjective _ p.surjective).comp
      (k.comp (RingHom.Finite.of_surjective _ q.symm.surjective)),
      fun k => ha ▸ (RingHom.Finite.of_surjective _ p.symm.surjective).comp
      (k.comp (RingHom.Finite.of_surjective _ q.surjective))⟩
  · rw [← presentedMap_morphismProperty A B f.hom.hom (@Flat),
      ← presentedMap_morphismProperty C D g.hom.hom (@Flat),
      HasRingHomProperty.Spec_iff (P := @Flat), HasRingHomProperty.Spec_iff (P := @Flat)]
    change a.Flat ↔ b.Flat
    exact ⟨fun k => hb ▸ ((RingHom.Flat.of_bijective q.symm.bijective).comp k).comp
      (RingHom.Flat.of_bijective p.bijective),
      fun k => ha ▸ ((RingHom.Flat.of_bijective q.bijective).comp k).comp
      (RingHom.Flat.of_bijective p.symm.bijective)⟩
  · rw [← presentedMap_morphismProperty A B f.hom.hom (@Surjective),
      ← presentedMap_morphismProperty C D g.hom.hom (@Surjective), surjective_iff, surjective_iff]
    change Function.Surjective (PrimeSpectrum.comap a) ↔
      Function.Surjective (PrimeSpectrum.comap b)
    constructor
    · intro k
      rw [hb, PrimeSpectrum.comap_comp, PrimeSpectrum.comap_comp]
      exact (PrimeSpectrum.isHomeomorph_comap_of_bijective q.symm.bijective).surjective.comp
        (k.comp (PrimeSpectrum.isHomeomorph_comap_of_bijective p.bijective).surjective)
    · intro k
      rw [ha, PrimeSpectrum.comap_comp, PrimeSpectrum.comap_comp]
      exact (PrimeSpectrum.isHomeomorph_comap_of_bijective q.bijective).surjective.comp
        (k.comp (PrimeSpectrum.isHomeomorph_comap_of_bijective p.symm.bijective).surjective)

end MorphismProperties

section Subgroups

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup IsNormalSubgroup subgroupConjugation)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.GeometricRadicals (IsSmoothConnectedNormal)
open private schemeKernel_exists schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {e : F ≃+* k₀} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup k₀}

private structure RelatedSubgroup (P : GroupComparison e G H)
    (N : ClosedSubgroup G.val) (M : ClosedSubgroup H.val) where
  points : GroupComparison e (closedSubgroupAlgebraicGroup N) (closedSubgroupAlgebraicGroup M)
  inclusion : Compatible points P N.inclusion M.inclusion

private theorem GroupComparison.existsSmallSubgroup (P : GroupComparison e G H)
    (N : ClosedSubgroup G.val) : ∃ M : ClosedSubgroup H.val, Nonempty (RelatedSubgroup P N M) := by
  let Q := GroupComparison.smallModel e (closedSubgroupAlgebraicGroup N)
  obtain ⟨f, hf⟩ := Q.existsSmallMap P N.inclusion
  let M : ClosedSubgroup H.val :=
    ⟨_, f, hf.morphismProperties.1.mp N.isClosedImmersion⟩
  exact ⟨M, ⟨Q, hf⟩⟩

private theorem GroupComparison.existsLargeSubgroup (P : GroupComparison e G H)
    (M : ClosedSubgroup H.val) : ∃ N : ClosedSubgroup G.val, Nonempty (RelatedSubgroup P N M) := by
  obtain ⟨A, ⟨Q⟩⟩ := existsLargeModel e (closedSubgroupAlgebraicGroup M)
  obtain ⟨f, hf⟩ := Q.existsLargeMap P M.inclusion
  let N : ClosedSubgroup G.val :=
    ⟨_, f, hf.morphismProperties.1.mpr M.isClosedImmersion⟩
  exact ⟨N, ⟨Q, hf⟩⟩

private theorem RelatedSubgroup.subgroupOf_iff {P : GroupComparison e G H}
    {N N' : ClosedSubgroup G.val} {M M' : ClosedSubgroup H.val}
    (Q : RelatedSubgroup P N M) (Q' : RelatedSubgroup P N' M') :
    IsSubgroupOf N N' ↔ IsSubgroupOf M M' := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨g, hg⟩ := Q.points.existsSmallMap Q'.points f
    exact ⟨g, Q.points.smallMap_unique P (hf ▸ hg.comp Q'.inclusion) Q.inclusion⟩
  · rintro ⟨g, hg⟩
    obtain ⟨f, hf⟩ := Q.points.existsLargeMap Q'.points g
    exact ⟨f, Q.points.largeMap_unique P (hg ▸ hf.comp Q'.inclusion) Q.inclusion⟩

private theorem GroupComparison.connected_iff (P : GroupComparison e G H) :
    ConnectedSpace G.val.X.left ↔ ConnectedSpace H.val.X.left := by
  let A := affinePresentation G.val.X G.property.1 G.property.2.1
  let B := affinePresentation H.val.X H.property.1 H.property.2.1
  have hA : IsIso A.iso.hom.left := inferInstance
  have hB : IsIso B.iso.hom.left := inferInstance
  exact A.iso.hom.left.homeomorph.connectedSpace_iff.symm.trans
    ((PrimeSpectrum.homeomorphOfRingEquiv P.coordinates.ringEquiv).connectedSpace_iff.trans
      B.iso.hom.left.homeomorph.connectedSpace_iff)

private theorem GroupComparison.isZero_iff (P : GroupComparison e G H) :
    IsZero G.val ↔ IsZero H.val := by
  constructor
  · intro hG
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (groupHomEquiv _ _ H.property.1).injective
    ext R p
    apply (P.equiv R).injective
    have hR := subsingleton_points_of_isZero G.val hG (liftedTest e R)
    exact hR.elim _ _
  · intro hH
    apply isZero_of_subsingleton_liftedPoints e
    intro R
    have hR := subsingleton_points_of_isZero H.val hH R
    exact ⟨fun x y => (P.equiv R).symm.injective (hR.elim _ _)⟩

private def productPresentation {k : Type u} [Field k] (A B : AffineAlgebraicGroup k) :
    AffinePresentation (A.val.X ⊗ B.val.X) := by
  have hA := A.property.1
  have hB := B.property.1
  have hfA := A.property.2.1
  have hfB := B.property.2.1
  apply affinePresentation
  · change IsAffine (pullback A.val.X.hom B.val.X.hom)
    infer_instance
  · have h : LocallyOfFiniteType ((snd A.val.X B.val.X).left ≫ B.val.X.hom) := by
      change LocallyOfFiniteType (pullback.snd A.val.X.hom B.val.X.hom ≫ B.val.X.hom)
      infer_instance
    exact (Over.w (snd A.val.X B.val.X)) ▸ h

set_option backward.isDefEq.respectTransparency false in
private theorem RelatedSubgroup.normal_iff {P : GroupComparison e G H}
    {N : ClosedSubgroup G.val} {M : ClosedSubgroup H.val} (Q : RelatedSubgroup P N M) :
    IsNormalSubgroup N.inclusion ↔ IsNormalSubgroup M.inclusion := by
  constructor
  · intro hn
    let D := productPresentation H (closedSubgroupAlgebraicGroup M)
    let R := D.coordinates
    let x : GroupPoints H.val R := D.iso.hom ≫ fst H.val.X M.group.X
    let y : GroupPoints M.group R := D.iso.hom ≫ snd H.val.X M.group.X
    obtain ⟨z, hz⟩ := normalSubgroup_conjugate_sections hn (P.equiv R x) (Q.points.equiv R y)
    obtain ⟨w, hw⟩ := (Q.points.equiv R).surjective z
    have h : pointMap M.inclusion R w = x * pointMap M.inclusion R y * x⁻¹ := by
      apply (P.equiv R).injective
      have hw' : P.equiv R (pointMap M.inclusion R w) =
          pointMap N.inclusion (liftedTest e R) z :=
        (Q.inclusion R w).trans (congrArg (fun t : GroupPoints N.group (liftedTest e R) =>
          pointMap N.inclusion (liftedTest e R) t) hw)
      have hy' := Q.inclusion R y
      rw [map_mul, map_mul, map_inv]
      exact hw'.trans (hz.trans (congrArg
        (fun t : GroupPoints G.val (liftedTest e R) =>
          P.equiv R x * t * (P.equiv R x)⁻¹) hy'.symm))
    refine ⟨D.iso.inv ≫ w, ?_⟩
    apply (cancel_epi D.iso.hom).mp
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    change w ≫ M.inclusion.hom.hom = D.iso.hom ≫ subgroupConjugation M.inclusion
    simp only [subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv]
    exact h
  · intro hn
    let D := productPresentation G (closedSubgroupAlgebraicGroup N)
    let R := transportedCoordinates e D
    let j := liftedSpecIso e D
    let x : GroupPoints G.val (liftedTest e R) := j.hom ≫ fst G.val.X N.group.X
    let y : GroupPoints N.group (liftedTest e R) := j.hom ≫ snd G.val.X N.group.X
    let a := (P.equiv R).symm x
    let b := (Q.points.equiv R).symm y
    obtain ⟨c, hc⟩ := normalSubgroup_conjugate_sections hn a b
    let z := Q.points.equiv R c
    have h : pointMap N.inclusion (liftedTest e R) z =
        x * pointMap N.inclusion (liftedTest e R) y * x⁻¹ := by
      have hc' : pointMap M.inclusion R c = a * pointMap M.inclusion R b * a⁻¹ := hc
      have hb' : P.equiv R (pointMap M.inclusion R b) =
          pointMap N.inclusion (liftedTest e R) y :=
        (Q.inclusion R b).trans (congrArg (fun t : GroupPoints N.group (liftedTest e R) =>
          pointMap N.inclusion (liftedTest e R) t) ((Q.points.equiv R).apply_symm_apply y))
      calc
        _ = P.equiv R (pointMap M.inclusion R c) := (Q.inclusion R c).symm
        _ = P.equiv R (a * pointMap M.inclusion R b * a⁻¹) := congrArg (P.equiv R) hc'
        _ = _ := by
          rw [map_mul, map_mul, map_inv, hb']
          simp only [a, MulEquiv.apply_symm_apply]
    refine ⟨j.inv ≫ z, ?_⟩
    apply (cancel_epi j.hom).mp
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    change z ≫ N.inclusion.hom.hom = j.hom ≫ subgroupConjugation N.inclusion
    simp only [subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv]
    exact h

end Subgroups

section SolvableGroups

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup IsSolvable DerivedSeries FactorsThrough commutatorMap)
open scoped commutatorElement
open private comp_commutatorMap_projections from LinearAlgebraicGroups.Solvable.SchemeDerivedGroup

variable {e : F ≃+* k₀} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup k₀}

set_option backward.isDefEq.respectTransparency false in
private theorem factorsCommutator {k : Type u} [Field k] {U : GroupScheme k}
    (D : ClosedSubgroup U) (h : FactorsThrough D (commutatorMap (𝟙 U) (𝟙 U)))
    (R : TestAlgebra k) (x y : GroupPoints U R) :
    ∃ z : GroupPoints D.group R, pointMap D.inclusion R z = ⁅x, y⁆ := by
  obtain ⟨f, hf⟩ := h
  change f ≫ D.inclusion.hom.hom = commutatorMap (𝟙 U) (𝟙 U) at hf
  refine ⟨lift x y ≫ f, ?_⟩
  change (lift x y ≫ f) ≫ D.inclusion.hom.hom = _
  rw [Category.assoc, hf, comp_commutatorMap_projections]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem RelatedSubgroup.factorsCommutator_iff {P : GroupComparison e G H}
    {N : ClosedSubgroup G.val} {M : ClosedSubgroup H.val} (Q : RelatedSubgroup P N M) :
    FactorsThrough N (commutatorMap (𝟙 G.val) (𝟙 G.val)) ↔
      FactorsThrough M (commutatorMap (𝟙 H.val) (𝟙 H.val)) := by
  constructor
  · intro h
    let D := productPresentation H H
    let R := D.coordinates
    let x : GroupPoints H.val R := D.iso.hom ≫ fst H.val.X H.val.X
    let y : GroupPoints H.val R := D.iso.hom ≫ snd H.val.X H.val.X
    obtain ⟨z, hz⟩ := factorsCommutator N h (liftedTest e R) (P.equiv R x) (P.equiv R y)
    let w : GroupPoints M.group R := (Q.points.equiv R).symm z
    have hM : pointMap M.inclusion R w = ⁅x, y⁆ := by
      apply (P.equiv R).injective
      have hw : Q.points.equiv R w = z := (Q.points.equiv R).apply_symm_apply z
      have h := Q.inclusion R w
      exact h.trans ((congrArg (fun p : GroupPoints N.group (liftedTest e R) =>
        pointMap N.inclusion (liftedTest e R) p) hw).trans
          (hz.trans (map_commutatorElement (P.equiv R) x y).symm))
    refine ⟨D.iso.inv ≫ w, ?_⟩
    change (D.iso.inv ≫ w) ≫ M.inclusion.hom.hom = _
    apply (cancel_epi D.iso.hom).mp
    rw [Category.assoc, Iso.hom_inv_id_assoc, comp_commutatorMap_projections]
    change pointMap M.inclusion R w =
      ⁅(D.iso.hom ≫ fst H.val.X H.val.X) ≫ 𝟙 H.val.X,
        (D.iso.hom ≫ snd H.val.X H.val.X) ≫ 𝟙 H.val.X⁆
    simpa only [Category.comp_id] using hM
  · intro h
    let D := productPresentation G G
    let R := transportedCoordinates e D
    let i := liftedSpecIso e D
    let x : GroupPoints G.val (liftedTest e R) := i.hom ≫ fst G.val.X G.val.X
    let y : GroupPoints G.val (liftedTest e R) := i.hom ≫ snd G.val.X G.val.X
    obtain ⟨w, hw⟩ := factorsCommutator M h R ((P.equiv R).symm x) ((P.equiv R).symm y)
    let z : GroupPoints N.group (liftedTest e R) := Q.points.equiv R w
    have hN : pointMap N.inclusion (liftedTest e R) z = ⁅x, y⁆ := by
      calc
        _ = P.equiv R (pointMap M.inclusion R w) := (Q.inclusion R w).symm
        _ = P.equiv R (⁅(P.equiv R).symm x, (P.equiv R).symm y⁆) :=
          congrArg (P.equiv R) hw
        _ = _ := by rw [map_commutatorElement, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    refine ⟨i.inv ≫ z, ?_⟩
    change (i.inv ≫ z) ≫ N.inclusion.hom.hom = _
    apply (cancel_epi i.hom).mp
    rw [Category.assoc, Iso.hom_inv_id_assoc, comp_commutatorMap_projections]
    change pointMap N.inclusion (liftedTest e R) z =
      ⁅(i.hom ≫ fst G.val.X G.val.X) ≫ 𝟙 G.val.X,
        (i.hom ≫ snd G.val.X G.val.X) ≫ 𝟙 G.val.X⁆
    simpa only [Category.comp_id] using hN

private theorem RelatedSubgroup.derived_iff {P : GroupComparison e G H}
    {N : ClosedSubgroup G.val} {M : ClosedSubgroup H.val} (Q : RelatedSubgroup P N M) :
    IsDerivedSubgroup N ↔ IsDerivedSubgroup M := by
  constructor
  · rintro ⟨hn, hf, hmin⟩
    refine ⟨Q.normal_iff.mp hn, Q.factorsCommutator_iff.mp hf, ?_⟩
    intro M' hm' hf'
    obtain ⟨N', ⟨Q'⟩⟩ := P.existsLargeSubgroup M'
    exact (Q.subgroupOf_iff Q').mp
      (hmin N' (Q'.normal_iff.mpr hm') (Q'.factorsCommutator_iff.mpr hf'))
  · rintro ⟨hn, hf, hmin⟩
    refine ⟨Q.normal_iff.mpr hn, Q.factorsCommutator_iff.mpr hf, ?_⟩
    intro N' hn' hf'
    obtain ⟨M', ⟨Q'⟩⟩ := P.existsSmallSubgroup N'
    exact (Q.subgroupOf_iff Q').mpr
      (hmin M' (Q'.normal_iff.mp hn') (Q'.factorsCommutator_iff.mp hf'))

set_option backward.isDefEq.respectTransparency false in
private theorem GroupComparison.derivedSeries_small (P : GroupComparison e G H)
    {n : ℕ} {A : GroupScheme F} (d : DerivedSeries G.val n A) :
    ∃ (U : AffineAlgebraicGroup F) (V : AffineAlgebraicGroup k₀),
      U.val = A ∧ DerivedSeries H.val n V.val ∧ Nonempty (GroupComparison e U V) := by
  induction d with
  | zero => exact ⟨G, H, rfl, .zero, ⟨P⟩⟩
  | @succ n A _ N hN ih =>
    obtain ⟨U, V, hU, hV, ⟨Q⟩⟩ := ih
    subst A
    obtain ⟨M, ⟨Q'⟩⟩ := Q.existsSmallSubgroup N
    exact ⟨closedSubgroupAlgebraicGroup N, closedSubgroupAlgebraicGroup M,
      rfl, .succ hV M (Q'.derived_iff.mp hN), ⟨Q'.points⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem GroupComparison.derivedSeries_large (P : GroupComparison e G H)
    {n : ℕ} {A : GroupScheme k₀} (d : DerivedSeries H.val n A) :
    ∃ (U : AffineAlgebraicGroup F) (V : AffineAlgebraicGroup k₀),
      V.val = A ∧ DerivedSeries G.val n U.val ∧ Nonempty (GroupComparison e U V) := by
  induction d with
  | zero => exact ⟨G, H, rfl, .zero, ⟨P⟩⟩
  | @succ n A _ M hM ih =>
    obtain ⟨U, V, hV, hU, ⟨Q⟩⟩ := ih
    subst A
    obtain ⟨N, ⟨Q'⟩⟩ := Q.existsLargeSubgroup M
    exact ⟨closedSubgroupAlgebraicGroup N, closedSubgroupAlgebraicGroup M,
      rfl, .succ hU N (Q'.derived_iff.mpr hM), ⟨Q'.points⟩⟩

private theorem trivial_iff_isZero {k : Type u} [Field k] (A : GroupScheme k) :
    Nonempty (A ≅ Grp.trivial (SchemeOver k)) ↔ IsZero A :=
  ⟨fun ⟨i⟩ => (Grp.isZero_trivial _).of_iso i, fun h => ⟨h.iso (Grp.isZero_trivial _)⟩⟩

private theorem GroupComparison.solvable_iff (P : GroupComparison e G H) :
    IsSolvable G.val ↔ IsSolvable H.val := by
  constructor
  · rintro ⟨n, A, d, ht⟩
    obtain ⟨U, V, hU, hV, ⟨Q⟩⟩ := P.derivedSeries_small d
    exact ⟨n, V.val, hV, (trivial_iff_isZero V.val).mpr <| Q.isZero_iff.mp <|
      (trivial_iff_isZero U.val).mp (hU ▸ ht)⟩
  · rintro ⟨n, A, d, ht⟩
    obtain ⟨U, V, hV, hU, ⟨Q⟩⟩ := P.derivedSeries_large d
    exact ⟨n, U.val, hU, (trivial_iff_isZero U.val).mpr <| Q.isZero_iff.mpr <|
      (trivial_iff_isZero V.val).mp (hV ▸ ht)⟩

end SolvableGroups

section GeometricProperties

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup IsSchemeKernel)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.GeometricRadicals (IsSemisimple IsSmoothConnectedNormal geometricSolvableRadical)
open LinearAlgebraicGroups.GeometricRadicals (geometricSolvableRadicalLargest)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.CentralIsogenies (IsCentralIsogeny)
open private connected_baseChange_iff from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private schemeKernel_exists schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {e : F ≃+* k₀} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup k₀}

private def GroupComparison.geometric (P : GroupComparison e G H) :
    GroupComparison (closureEquiv e) (GeometricGroup G) (GeometricGroup H) := by
  let hc := IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure F) (AlgebraicClosure k₀) e
  exact ⟨extensionPointComparison e (closureEquiv e) P.equiv hc,
    extensionPointComparison_naturality e (closureEquiv e) P.equiv hc P.naturality⟩

private theorem connected_iff_geometricallyConnected {k : Type u} [Field k]
    (A : AffineAlgebraicGroup k) :
    ConnectedSpace A.val.X.left ↔ GeometricallyConnected A.val.X.hom := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · letI := h
    exact geometricallyConnected_of_connected A
  · apply (connected_baseChange_iff (K := AlgebraicClosure k) A).mp
    exact h.geometrically_connectedSpace _ _ _
      (IsPullback.of_hasPullback A.val.X.hom (fieldSpecMap k (AlgebraicClosure k)))

private theorem isZero_of_subgroupOf {k : Type u} [Field k] {A : GroupScheme k}
    (N M : ClosedSubgroup A) (hle : IsSubgroupOf N M) (hM : IsZero M.group) : IsZero N.group := by
  obtain ⟨f, hf⟩ := hle
  have hi : N.inclusion = 0 := by
    rw [← hf, hM.eq_of_tgt f 0, zero_comp]
  haveI : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  haveI : Mono N.inclusion.hom.hom.left := inferInstance
  haveI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Grp.hom_ext
  apply (cancel_mono N.inclusion.hom.hom).mp
  have h : 𝟙 N.group ≫ N.inclusion = (0 : N.group ⟶ N.group) ≫ N.inclusion := by simp [hi]
  exact congrArg (Grp.forget (SchemeOver k)).map h

private theorem GroupComparison.semisimple_iff [CharZero F] [CharZero k₀]
    (P : GroupComparison e G H) :
    IsSemisimple G ↔ IsSemisimple H := by
  let Q := P.geometric
  let A := geometricSolvableRadical G
  let B := geometricSolvableRadical H
  have hA := geometricSolvableRadicalLargest G
  have hB := geometricSolvableRadicalLargest H
  have hsG := characteristicZeroSmoothness _ G
  have hsH := characteristicZeroSmoothness _ H
  have hcon : GeometricallyConnected G.val.X.hom ↔ GeometricallyConnected H.val.X.hom :=
    (connected_iff_geometricallyConnected G).symm.trans
      (P.connected_iff.trans (connected_iff_geometricallyConnected H))
  constructor
  · intro h
    obtain ⟨N, ⟨R⟩⟩ := Q.existsLargeSubgroup B
    have hz : IsZero A.group := (trivial_iff_isZero _).mp h.2.2
    have hnr : IsSmoothConnectedNormal N :=
      ⟨characteristicZeroSmoothness _ (closedSubgroupAlgebraicGroup N),
        R.points.connected_iff.mpr hB.1.2.1, R.normal_iff.mpr hB.1.2.2⟩
    have hn := isZero_of_subgroupOf N A
      (hA.2.2 N hnr (R.points.solvable_iff.mpr hB.2.1)) hz
    exact ⟨hsH, hcon.mp h.2.1, (trivial_iff_isZero _).mpr (R.points.isZero_iff.mp hn)⟩
  · intro h
    obtain ⟨M, ⟨R⟩⟩ := Q.existsSmallSubgroup A
    have hz : IsZero B.group := (trivial_iff_isZero _).mp h.2.2
    have hmr : IsSmoothConnectedNormal M :=
      ⟨characteristicZeroSmoothness _ (closedSubgroupAlgebraicGroup M),
        R.points.connected_iff.mp hA.1.2.1, R.normal_iff.mp hA.1.2.2⟩
    have hm := isZero_of_subgroupOf M B
      (hB.2.2 M hmr (R.points.solvable_iff.mp hA.2.1)) hz
    exact ⟨hsG, hcon.mpr h.2.1, (trivial_iff_isZero _).mpr (R.points.isZero_iff.mpr hm)⟩

private theorem GroupComparison.absolutelyAlmostSimple [CharZero F] [CharZero k₀]
    (P : GroupComparison e G H) (h : IsAbsolutelyAlmostSimple G) :
    IsAbsolutelyAlmostSimple H := by
  let Q := P.geometric
  refine ⟨P.semisimple_iff.mp h.1, fun hH => h.2.1 (Q.isZero_iff.mpr hH), ?_⟩
  intro M hM
  obtain ⟨N, ⟨R⟩⟩ := Q.existsLargeSubgroup M
  have hN : IsSmoothConnectedNormal N :=
    ⟨characteristicZeroSmoothness _ (closedSubgroupAlgebraicGroup N),
      R.points.connected_iff.mpr hM.2.1, R.normal_iff.mpr hM.2.2⟩
  exact (h.2.2 N hN).imp R.points.isZero_iff.mp R.inclusion.isIso_iff.mp

set_option backward.isDefEq.respectTransparency false in
private theorem kernelPointsCentral {k : Type u} [Field k] {A B : GroupScheme k}
    {f : A ⟶ B} {M : ClosedSubgroup A} (hM : IsSchemeKernel f M)
    (hC : Centralizes (𝟙 A) M.inclusion.hom.hom)
    (R : TestAlgebra k) (x z : GroupPoints A R)
    (hz : pointMap f R z = 1) : z * x * z⁻¹ = x := by
  obtain ⟨w, hw⟩ := (schemeKernel_sections hM z).mpr hz
  have hh := congrArg (fun a => lift x w ≫ a) hC
  change (lift x w ≫ conjugateFamily (𝟙 A) M.inclusion.hom.hom) =
    lift x w ≫ fst A.X M.group.X ≫ (𝟙 A : A ⟶ A).hom.hom at hh
  simp only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, lift_fst, lift_snd] at hh
  change (w ≫ M.inclusion.hom.hom) * (x ≫ 𝟙 A.X) *
    (w ≫ M.inclusion.hom.hom)⁻¹ = x ≫ 𝟙 A.X at hh
  change w ≫ M.inclusion.hom.hom = z at hw
  rw [hw, Category.comp_id] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
private theorem Compatible.centralIsogeny_large
    {G₁ G₂ : AffineAlgebraicGroup F} {H₁ H₂ : AffineAlgebraicGroup k₀}
    {P : GroupComparison e G₁ H₁} {Q : GroupComparison e G₂ H₂}
    {f : G₁.val ⟶ G₂.val} {g : H₁.val ⟶ H₂.val} (h : Compatible P Q f g)
    (hg : IsCentralIsogeny g) : IsCentralIsogeny f := by
  have hp := h.morphismProperties.2
  obtain ⟨M, hM, hC⟩ := hg.2.2.2
  have hG₂ := G₂.property.1
  obtain ⟨N, hN⟩ := schemeKernel_exists f
  refine ⟨hp.1.mpr hg.1, hp.2.1.mpr hg.2.1, hp.2.2.mpr hg.2.2.1, N, hN, ?_⟩
  let D : AffinePresentation (G₁.val.X ⊗ N.group.X) :=
    productPresentation G₁ (closedSubgroupAlgebraicGroup N)
  apply hom_ext_of_liftedPoints e D
  intro R p
  let x : GroupPoints G₁.val (liftedTest e R) := p ≫ fst G₁.val.X N.group.X
  let w : GroupPoints N.group (liftedTest e R) := p ≫ snd G₁.val.X N.group.X
  let z := pointMap N.inclusion (liftedTest e R) w
  have hz : pointMap f (liftedTest e R) z = 1 :=
    (schemeKernel_sections hN z).mp ⟨w, rfl⟩
  let a := (P.equiv R).symm x
  let b := (P.equiv R).symm z
  have ha : P.equiv R a = x := (P.equiv R).apply_symm_apply x
  have hb : P.equiv R b = z := (P.equiv R).apply_symm_apply z
  have hb' : pointMap g R b = 1 := by
    apply (Q.equiv R).injective
    rw [map_one, h R, hb]
    exact hz
  have hc := kernelPointsCentral hM hC R a b hb'
  have eq := congrArg (P.equiv R) hc
  have hh : z * x * z⁻¹ = x := by
    rw [map_mul, map_mul, map_inv, ha, hb] at eq
    exact eq
  change p ≫ conjugateFamily (𝟙 G₁.val) N.inclusion.hom.hom =
    p ≫ fst G₁.val.X N.group.X ≫ (𝟙 G₁.val : G₁.val ⟶ G₁.val).hom.hom
  simp only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
  change (w ≫ N.inclusion.hom.hom) * (x ≫ 𝟙 G₁.val.X) *
    (w ≫ N.inclusion.hom.hom)⁻¹ = x ≫ 𝟙 G₁.val.X
  rw [Category.comp_id]
  exact hh

private theorem GroupComparison.simplyConnected [CharZero F] [CharZero k₀]
    (P : GroupComparison e G H) (h : GeometricallySimplyConnected G) :
    GeometricallySimplyConnected H := by
  intro B hB g hg
  let Q := P.geometric
  obtain ⟨A, ⟨R⟩⟩ := existsLargeModel (closureEquiv e) B
  obtain ⟨f, hf⟩ := R.existsLargeMap Q g
  exact hf.isIso_iff.mp (h A (R.semisimple_iff.mpr hB) f (hf.centralIsogeny_large hg))

end GeometricProperties

section BorelPairs

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.GeometricRadicals (IsMaximalTorus IsSplitTorus IsTorus)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel IsSmoothConnectedSolvable)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Pinning (SplitBorelPair)
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private isKBorel_iff_of_isAlgClosed geometricMaximal_of_maximal subgroup_extend subgroup_descend
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private torus_baseChange_algClosure from LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private isTorus_iff_coordinates from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private split_of_torus torus_of_split from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting

variable {e : F ≃+* k₀} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup k₀}

private def liftUnits (R : TestAlgebra k₀) : Rˣ ≃* (ULift.{u} R)ˣ :=
  Units.mapEquiv ULift.ringEquiv.symm.toMulEquiv

private def liftUnitPower (r : ℕ) (R : TestAlgebra k₀) :
    (ULift.{0} (Fin r) → Rˣ) ≃* (ULift.{u} (Fin r) → (ULift.{u} R)ˣ) where
  toFun x i := liftUnits.{u} R (x (ULift.up i.down))
  invFun x i := (liftUnits.{u} R).symm (x (ULift.up i.down))
  left_inv x := funext fun i => (liftUnits.{u} R).symm_apply_apply (x i)
  right_inv x := funext fun i => (liftUnits.{u} R).apply_symm_apply (x i)
  map_mul' x y := funext fun i =>
    (liftUnits.{u} R).map_mul (x (ULift.up i.down)) (y (ULift.up i.down))

private abbrev powerTorus (k : Type u) [Field k] (r : ℕ) :=
  StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))

set_option backward.isDefEq.respectTransparency false in
private def powerTorusComparison (e : F ≃+* k₀) (r : ℕ) :
    GroupComparison e (powerTorus F r) (powerTorus k₀ r) where
  equiv R :=
    ((StandardGroups.multiplicativePowerGroupPointsIso k₀ (ULift.{0} (Fin r))).app R
      ).groupIsoToMulEquiv.trans <|
    (liftUnitPower r R).trans
      (((StandardGroups.multiplicativePowerGroupPointsIso F (ULift.{u} (Fin r))).app
        (liftedTest e R)).groupIsoToMulEquiv).symm
  naturality {R S} a p := by
    let c := StandardGroups.multiplicativePowerGroupPointsIso k₀ (ULift.{0} (Fin r))
    let d := StandardGroups.multiplicativePowerGroupPointsIso F (ULift.{u} (Fin r))
    let iR := (d.app (liftedTest e R)).groupIsoToMulEquiv
    let iS := (d.app (liftedTest e S)).groupIsoToMulEquiv
    apply iS.injective
    change iS (iS.symm (liftUnitPower r S (c.hom.app S (mapPoints a p)))) =
      d.hom.app (liftedTest e S) (mapPoints (liftedMap e a)
        (iR.symm (liftUnitPower r R (c.hom.app R p))))
    let q := iR.symm (liftUnitPower r R (c.hom.app R p))
    have hc : c.hom.app S (mapPoints a p) =
        (Specs.StandardGroups.multiplicativePowerPoints k₀ (ULift.{0} (Fin r))).map a
          (c.hom.app R p) := NatTrans.naturality_apply c.hom a p
    have hd : d.hom.app (liftedTest e S) (mapPoints (liftedMap e a) q) =
        (Specs.StandardGroups.multiplicativePowerPoints F (ULift.{u} (Fin r))).map
          (liftedMap e a) (d.hom.app (liftedTest e R) q) :=
      NatTrans.naturality_apply d.hom (liftedMap e a) q
    calc
      _ = liftUnitPower r S (c.hom.app S (mapPoints a p)) := iS.apply_symm_apply _
      _ = liftUnitPower r S
          ((Specs.StandardGroups.multiplicativePowerPoints k₀ (ULift.{0} (Fin r))).map a
            (c.hom.app R p)) := congrArg (liftUnitPower r S) hc
      _ = (Specs.StandardGroups.multiplicativePowerPoints F (ULift.{u} (Fin r))).map
          (liftedMap e a) (liftUnitPower r R (c.hom.app R p)) := by
        funext i
        apply Units.ext
        rfl
      _ = (Specs.StandardGroups.multiplicativePowerPoints F (ULift.{u} (Fin r))).map
          (liftedMap e a) (d.hom.app (liftedTest e R) q) :=
        congrArg (fun x => (Specs.StandardGroups.multiplicativePowerPoints F
          (ULift.{u} (Fin r))).map (liftedMap e a) x) (iR.apply_symm_apply _).symm
      _ = _ := hd.symm

private theorem GroupComparison.splitTorus_iff (P : GroupComparison e G H) :
    IsSplitTorus G.val ↔ IsSplitTorus H.val := by
  constructor
  · rintro ⟨r, ⟨i⟩⟩
    obtain ⟨g, hg⟩ := P.existsSmallMap (powerTorusComparison e r) i.hom
    let j := @asIso _ _ _ _ g (hg.isIso_iff.mp i.isIso_hom)
    exact ⟨r, ⟨j⟩⟩
  · rintro ⟨r, ⟨i⟩⟩
    obtain ⟨f, hf⟩ := P.existsLargeMap (powerTorusComparison e r) i.hom
    let j := @asIso _ _ _ _ f (hf.isIso_iff.mpr i.isIso_hom)
    exact ⟨r, ⟨j⟩⟩

private theorem torus_iff_split_of_algClosed {k : Type u} [Field k] [IsAlgClosed k]
    (A : AffineAlgebraicGroup k) : IsTorus A.val ↔ IsSplitTorus A.val :=
  (isTorus_iff_coordinates A).trans ⟨split_of_torus, torus_of_split⟩

private theorem maximal_of_geometricMaximal {k : Type u} [Field k] [IsAlgClosed k]
    (A : AffineAlgebraicGroup k) (T : ClosedSubgroup A.val)
    (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T) : IsMaximalTorus T := by
  refine ⟨(torus_iff_split_of_algClosed (closedSubgroupAlgebraicGroup T)).mpr hs, ?_⟩
  intro U hU hTU
  obtain ⟨hc, hT'⟩ := hm
  exact subgroup_descend (AlgebraicClosure k)
    (hT'.2 _ (torus_baseChange_algClosure (closedSubgroupAlgebraicGroup U) hU)
      (subgroup_extend (AlgebraicClosure k) hTU))

private theorem RelatedSubgroup.maximalTorus_iff [IsAlgClosed F] [IsAlgClosed k₀]
    {P : GroupComparison e G H} {N : ClosedSubgroup G.val} {M : ClosedSubgroup H.val}
    (Q : RelatedSubgroup P N M) : IsMaximalTorus N ↔ IsMaximalTorus M := by
  constructor
  · intro h
    refine ⟨(torus_iff_split_of_algClosed _).mpr
      (Q.points.splitTorus_iff.mp ((torus_iff_split_of_algClosed _).mp h.1)), ?_⟩
    intro M' hm' hle
    obtain ⟨N', ⟨Q'⟩⟩ := P.existsLargeSubgroup M'
    have hn' := (torus_iff_split_of_algClosed _).mpr
      (Q'.points.splitTorus_iff.mpr ((torus_iff_split_of_algClosed _).mp hm'))
    exact (Q'.subgroupOf_iff Q).mp (h.2 N' hn' ((Q.subgroupOf_iff Q').mpr hle))
  · intro h
    refine ⟨(torus_iff_split_of_algClosed _).mpr
      (Q.points.splitTorus_iff.mpr ((torus_iff_split_of_algClosed _).mp h.1)), ?_⟩
    intro N' hn' hle
    obtain ⟨M', ⟨Q'⟩⟩ := P.existsSmallSubgroup N'
    have hm' := (torus_iff_split_of_algClosed _).mpr
      (Q'.points.splitTorus_iff.mp ((torus_iff_split_of_algClosed _).mp hn'))
    exact (Q'.subgroupOf_iff Q).mpr (h.2 M' hm' ((Q.subgroupOf_iff Q').mp hle))

private theorem RelatedSubgroup.borel_iff [CharZero F] [CharZero k₀]
    {P : GroupComparison e G H} {N : ClosedSubgroup G.val} {M : ClosedSubgroup H.val}
    (Q : RelatedSubgroup P N M) : IsBorel N ↔ IsBorel M := by
  have hscs {N : ClosedSubgroup G.val} {M : ClosedSubgroup H.val} (Q : RelatedSubgroup P N M) :
      IsSmoothConnectedSolvable N ↔ IsSmoothConnectedSolvable M :=
    ⟨fun h => ⟨characteristicZeroSmoothness _ (closedSubgroupAlgebraicGroup M),
        Q.points.connected_iff.mp h.2.1, Q.points.solvable_iff.mp h.2.2⟩,
      fun h => ⟨characteristicZeroSmoothness _ (closedSubgroupAlgebraicGroup N),
        Q.points.connected_iff.mpr h.2.1, Q.points.solvable_iff.mpr h.2.2⟩⟩
  constructor
  · intro h
    refine ⟨(hscs Q).mp h.1, ?_⟩
    intro M' hm' hle
    obtain ⟨N', ⟨Q'⟩⟩ := P.existsLargeSubgroup M'
    exact (Q'.subgroupOf_iff Q).mp (h.2 N' ((hscs Q').mpr hm') ((Q.subgroupOf_iff Q').mpr hle))
  · intro h
    refine ⟨(hscs Q).mpr h.1, ?_⟩
    intro N' hn' hle
    obtain ⟨M', ⟨Q'⟩⟩ := P.existsSmallSubgroup N'
    exact (Q'.subgroupOf_iff Q).mpr (h.2 M' ((hscs Q').mp hn') ((Q.subgroupOf_iff Q').mp hle))

private theorem GroupComparison.existsSmallBorelPair
    [CharZero F] [CharZero k₀] [IsAlgClosed F] [IsAlgClosed k₀]
    (P : GroupComparison e G H) (hG : Specs.GeometricRadicals.IsSemisimple G)
    (A : SplitBorelPair F) (hA : A.G = G) :
    ∃ (B : SplitBorelPair k₀) (hB : B.G = H),
      Nonempty (RelatedSubgroup P (hA ▸ A.T) (hB ▸ B.T)) ∧
      Nonempty (RelatedSubgroup P (hA ▸ A.B) (hB ▸ B.B)) := by
  subst G
  obtain ⟨T, ⟨Q⟩⟩ := P.existsSmallSubgroup A.T
  obtain ⟨B, ⟨R⟩⟩ := P.existsSmallSubgroup A.B
  let pair : SplitBorelPair k₀ :=
    { G := H
      reductive := reductive_of_semisimple H (P.semisimple_iff.mp hG)
      T := T
      split := Q.points.splitTorus_iff.mp A.split
      maximal := geometricMaximal_of_maximal H T (Q.maximalTorus_iff.mp
        (maximal_of_geometricMaximal A.G A.T A.split A.maximal))
      B := B
      borel := (isKBorel_iff_of_isAlgClosed H B).mpr
        (R.borel_iff.mp ((isKBorel_iff_of_isAlgClosed A.G A.B).mp A.borel))
      containsTorus := (Q.subgroupOf_iff R).mp A.containsTorus }
  exact ⟨pair, rfl, ⟨Q⟩, ⟨R⟩⟩

end BorelPairs

section Characters

open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator)
open CocharacterDynamics (unitPoint unitCoordinates mapPoints_unitPoint)
open private gm unitEquiv unitEquiv_unitPoint
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

variable {e : F ≃+* k₀}
variable {G₁ G₂ : AffineAlgebraicGroup F} {H₁ H₂ : AffineAlgebraicGroup k₀}

private def GroupComparison.homEquiv (P : GroupComparison e G₁ H₁)
    (Q : GroupComparison e G₂ H₂) : (G₁.val ⟶ G₂.val) ≃ (H₁.val ⟶ H₂.val) where
  toFun f := (P.existsSmallMap Q f).choose
  invFun g := (P.existsLargeMap Q g).choose
  left_inv f := P.largeMap_unique Q (P.existsLargeMap Q _).choose_spec
    (P.existsSmallMap Q f).choose_spec
  right_inv g := P.smallMap_unique Q (P.existsSmallMap Q _).choose_spec
    (P.existsLargeMap Q g).choose_spec

private theorem GroupComparison.homEquiv_compatible (P : GroupComparison e G₁ H₁)
    (Q : GroupComparison e G₂ H₂) (f : G₁.val ⟶ G₂.val) :
    Compatible P Q f (P.homEquiv Q f) :=
  (P.existsSmallMap Q f).choose_spec

private def multiplicativeLine (k : Type u) [Field k] : AffineAlgebraicGroup k := by
  letI : Group.FG IntegerCharacters.{u} :=
    Group.fg_of_surjective
      (f := (MulEquiv.ulift.symm : Multiplicative ℤ ≃* IntegerCharacters.{u}).toMonoidHom)
      MulEquiv.ulift.symm.surjective
  exact Specs.StandardGroups.spectrum k (MonoidAlgebra k IntegerCharacters.{u})

private def multiplicativeLinePoints (e : F ≃+* k₀) (R : TestAlgebra k₀) :
    GroupPoints (gm k₀) R ≃* GroupPoints (gm F) (liftedTest e R) :=
  (unitEquiv R).trans ((liftUnits R).trans (unitEquiv (liftedTest e R)).symm)

private theorem multiplicativeLinePoints_unit (e : F ≃+* k₀) (R : TestAlgebra k₀) (x : Rˣ) :
    multiplicativeLinePoints e R (unitPoint R x) =
      unitPoint (liftedTest e R) (liftUnits R x) := by
  change (unitEquiv (liftedTest e R)).symm (liftUnits R (unitEquiv R (unitPoint R x))) = _
  rw [unitEquiv_unitPoint]
  apply (unitEquiv (liftedTest e R)).injective
  rw [MulEquiv.apply_symm_apply, unitEquiv_unitPoint]

private def multiplicativeLineComparison (e : F ≃+* k₀) :
    GroupComparison e (multiplicativeLine F) (multiplicativeLine k₀) where
  equiv := multiplicativeLinePoints e
  naturality {R S} a x := by
    have hx : unitPoint R (unitEquiv R x) = x :=
      (unitEquiv R).injective (unitEquiv_unitPoint R (unitEquiv R x))
    change multiplicativeLinePoints e S (mapPoints a x) =
      mapPoints (liftedMap e a) (multiplicativeLinePoints e R x)
    rw [← hx, mapPoints_unitPoint, multiplicativeLinePoints_unit,
      multiplicativeLinePoints_unit, mapPoints_unitPoint]
    rfl

set_option backward.isDefEq.respectTransparency false in
private def GroupComparison.characterEquiv (P : GroupComparison e G₁ H₁) :
    Character G₁.val ≃* Character H₁.val where
  toEquiv := P.homEquiv (multiplicativeLineComparison e)
  map_mul' χ ψ := by
    let C := multiplicativeLineComparison e
    apply P.smallMap_unique C (P.homEquiv_compatible C (χ * ψ))
    intro R p
    have hχ := P.homEquiv_compatible C χ R p
    have hψ := P.homEquiv_compatible C ψ R p
    change C.equiv R (p ≫ ((P.homEquiv C χ).hom.hom * (P.homEquiv C ψ).hom.hom)) =
      P.equiv R p ≫ (χ.hom.hom * ψ.hom.hom)
    rw [MonObj.comp_mul, MonObj.comp_mul, map_mul]
    exact congrArg₂ (· * ·) hχ hψ

set_option backward.isDefEq.respectTransparency false in
private theorem characterValue_eq_unitVal {k : Type u} [Field k] {T : GroupScheme k}
    (χ : Character T) (R : TestAlgebra k) (p : GroupPoints T R) :
    characterValue χ R p = (unitEquiv R (pointMap χ R p)).val := by
  let x := pointMap χ R p
  have h : unitPoint R (unitEquiv R x) = x :=
    (unitEquiv R).injective (unitEquiv_unitPoint R (unitEquiv R x))
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    x).unop.hom (MonoidAlgebra.single integerGenerator 1) = _
  rw [← h]
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((testSpec k).map (CommAlgCat.ofHom (unitCoordinates R (unitEquiv R x))).op)).unop.hom
      (MonoidAlgebra.single integerGenerator 1) = _
  rw [Functor.FullyFaithful.preimage_map]
  change unitCoordinates R (unitEquiv R x) (MonoidAlgebra.single integerGenerator 1) = _
  rw [unitCoordinates, MonoidAlgebra.lift_single, one_smul]
  change ((unitEquiv R x ^ (1 : ℤ) : Rˣ) : R) = _
  rw [zpow_one]

private theorem GroupComparison.characterValue (P : GroupComparison e G₁ H₁)
    (χ : Character G₁.val) (R : TestAlgebra k₀) (p : GroupPoints H₁.val R) :
    characterValue χ (liftedTest e R) (P.equiv R p) =
      ULift.up (characterValue (P.characterEquiv χ) R p) := by
  let C := multiplicativeLineComparison e
  have h := P.homEquiv_compatible C χ R p
  have h' := congrArg (unitEquiv (liftedTest e R)) h
  change (unitEquiv (liftedTest e R))
    ((unitEquiv (liftedTest e R)).symm (liftUnits R (unitEquiv R (pointMap (P.characterEquiv χ) R p)))) =
      unitEquiv (liftedTest e R) (pointMap χ (liftedTest e R) (P.equiv R p)) at h'
  rw [MulEquiv.apply_symm_apply] at h'
  rw [characterValue_eq_unitVal, characterValue_eq_unitVal, ← h']
  rfl

end Characters

section AdditiveCoordinates

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.RootGroups (AdditiveLine rootPoint HasScalarAction)
open RootData.RootGroups (additivePoints)
open private additiveLineGroup additivePoints_add additivePoints_natural rootPoint_natural
  rootPoint_eq from LinearAlgebraicGroups.RootData.RootGroups
open private characterValue_naturality from LinearAlgebraicGroups.RootData.SchemeCentre

variable {e : F ≃+* k₀} {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup k₀}

private def additiveLineComparison (e : F ≃+* k₀) (A : AdditiveLine F) (B : AdditiveLine k₀) :
    GroupComparison e (additiveLineGroup A) (additiveLineGroup B) where
  equiv R :=
    { toEquiv := (additivePoints B R).symm.trans
        (Equiv.ulift.symm.trans (additivePoints A (liftedTest e R)))
      map_mul' p q := by
        obtain ⟨a, rfl⟩ := (additivePoints B R).surjective p
        obtain ⟨b, rfl⟩ := (additivePoints B R).surjective q
        rw [← additivePoints_add]
        change additivePoints A (liftedTest e R)
            (ULift.up ((additivePoints B R).symm (additivePoints B R (a + b)))) =
          additivePoints A (liftedTest e R)
            (ULift.up ((additivePoints B R).symm (additivePoints B R a))) *
          additivePoints A (liftedTest e R)
            (ULift.up ((additivePoints B R).symm (additivePoints B R b)))
        simp only [Equiv.symm_apply_apply]
        exact additivePoints_add A (liftedTest e R) (ULift.up a) (ULift.up b) }
  naturality {R S} a p := by
    obtain ⟨v, rfl⟩ := (additivePoints B R).surjective p
    rw [additivePoints_natural]
    simp only [MulEquiv.coe_mk, Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [additivePoints_natural]
    rfl

private theorem additiveLineComparison_eval (e : F ≃+* k₀) (A : AdditiveLine F)
    (B : AdditiveLine k₀) (R : TestAlgebra k₀) (v : R) :
    (additiveLineComparison e A B).equiv R (additivePoints B R v) =
      additivePoints A (liftedTest e R) (ULift.up v) := by
  change additivePoints A (liftedTest e R) (ULift.up
    ((additivePoints B R).symm (additivePoints B R v))) = _
  rw [Equiv.symm_apply_apply]

private theorem Compatible.rootPoint {A : AdditiveLine F} {B : AdditiveLine k₀}
    {P : GroupComparison e G H} {x : A.group ⟶ G.val} {y : B.group ⟶ H.val}
    (h : Compatible (additiveLineComparison e A B) P x y) (R : TestAlgebra k₀) (v : R) :
    P.equiv R (rootPoint y R v) = rootPoint x (liftedTest e R) (ULift.up v) := by
  rw [rootPoint_eq, rootPoint_eq]
  have he := h R (additivePoints B R v)
  change P.equiv R ((additivePoints B R v) ≫ y.hom.hom) =
    (additiveLineComparison e A B).equiv R (additivePoints B R v) ≫ x.hom.hom at he
  exact he.trans (congrArg (· ≫ x.hom.hom) (additiveLineComparison_eval e A B R v))

set_option backward.isDefEq.respectTransparency false in
private theorem hasScalarAction_of_lifted {A : AdditiveLine F}
    (T : ClosedSubgroup G.val) (χ : Character T.group) (x : A.group ⟶ G.val)
    (h : ∀ (R : TestAlgebra k₀) (t : GroupPoints T.group (liftedTest e R))
      (a : liftedTest e R),
      let g := pointMap T.inclusion (liftedTest e R) t
      g * rootPoint x (liftedTest e R) a * g⁻¹ =
        rootPoint x (liftedTest e R) (characterValue χ (liftedTest e R) t * a)) :
    HasScalarAction T χ x := by
  intro R t a
  let D : AffinePresentation (T.group.X ⊗ A.group.X) :=
    productPresentation (Specs.Unipotent.closedSubgroupAlgebraicGroup T) (additiveLineGroup A)
  let S := transportedCoordinates e D
  let i := liftedSpecIso e D
  let t₀ : GroupPoints T.group (liftedTest e S) := i.hom ≫ fst T.group.X A.group.X
  let p₀ : GroupPoints A.group (liftedTest e S) := i.hom ≫ snd T.group.X A.group.X
  obtain ⟨a₀, ha₀⟩ := (additivePoints A (liftedTest e S)).surjective p₀
  let p : Points (T.group.X ⊗ A.group.X) R := lift t (additivePoints A R a)
  obtain ⟨b, hb⟩ := (specPointsEquiv (liftedTest e S) R).surjective (p ≫ i.inv)
  have hb' : (testSpec F).map b.op = p ≫ i.inv := hb
  have hp : mapPoints b i.hom = p := by
    change (testSpec F).map b.op ≫ i.hom = p
    rw [hb', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have ht : mapPoints b t₀ = t := by
    change (testSpec F).map b.op ≫ i.hom ≫ fst _ _ = t
    rw [← Category.assoc]
    change mapPoints b i.hom ≫ fst T.group.X A.group.X = t
    rw [hp, lift_fst]
  have ha : b.hom a₀ = a := by
    apply (additivePoints A R).injective
    rw [← additivePoints_natural, ha₀]
    change (testSpec F).map b.op ≫ i.hom ≫ snd _ _ = _
    rw [← Category.assoc]
    change mapPoints b i.hom ≫ snd T.group.X A.group.X = additivePoints A R a
    rw [hp, lift_snd]
  have eq := congrArg (((groupPointsFunctor F).obj G.val).map b).hom (h S t₀ a₀)
  have hg : mapPoints b (pointMap T.inclusion (liftedTest e S) t₀) = pointMap T.inclusion R t :=
    (NatTrans.naturality_apply ((groupPointsFunctor F).map T.inclusion) b t₀).symm.trans
      (congrArg (pointMap T.inclusion R) ht)
  change (((groupPointsFunctor F).obj G.val).map b)
    (pointMap T.inclusion _ t₀ * rootPoint x _ a₀ * (pointMap T.inclusion _ t₀)⁻¹) = _ at eq
  simp only [map_mul, map_inv] at eq
  change mapPoints b (pointMap T.inclusion _ t₀) *
    mapPoints b (rootPoint x _ a₀) * (mapPoints b (pointMap T.inclusion _ t₀))⁻¹ =
      mapPoints b (rootPoint x _ (characterValue χ _ t₀ * a₀)) at eq
  rw [hg, rootPoint_natural, rootPoint_natural, map_mul, ← characterValue_naturality, ht, ha] at eq
  exact eq

set_option backward.isDefEq.respectTransparency false in
private theorem RelatedSubgroup.scalarAction_iff {A : AdditiveLine F} {B : AdditiveLine k₀}
    {P : GroupComparison e G H} {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val}
    (Q : RelatedSubgroup P T S) {χ : Character T.group}
    {x : A.group ⟶ G.val} {y : B.group ⟶ H.val}
    (hx : Compatible (additiveLineComparison e A B) P x y) :
    HasScalarAction T χ x ↔ HasScalarAction S (Q.points.characterEquiv χ) y := by
  constructor
  · intro h R t a
    let p := Q.points.equiv R t
    have eq := h (liftedTest e R) p (ULift.up a)
    apply (P.equiv R).injective
    have ht := Q.inclusion R t
    have hc := Q.points.characterValue χ R t
    change P.equiv R (pointMap S.inclusion R t * rootPoint y R a * (pointMap S.inclusion R t)⁻¹) =
      P.equiv R (rootPoint y R (characterValue (Q.points.characterEquiv χ) R t * a))
    rw [map_mul, map_mul, map_inv, hx.rootPoint, hx.rootPoint]
    change P.equiv R (pointMap S.inclusion R t) * rootPoint x (liftedTest e R) (ULift.up a) *
        (P.equiv R (pointMap S.inclusion R t))⁻¹ =
      rootPoint x (liftedTest e R) (ULift.up (characterValue (Q.points.characterEquiv χ) R t * a))
    have hm : ULift.up (characterValue (Q.points.characterEquiv χ) R t * a) =
        characterValue χ (liftedTest e R) p * ULift.up a :=
      congrArg (fun s : liftedTest e R => s * ULift.up a) hc.symm
    exact (congrArg (fun g : GroupPoints G.val (liftedTest e R) =>
      g * rootPoint x (liftedTest e R) (ULift.up a) * g⁻¹) ht).trans
      (eq.trans (congrArg (rootPoint x (liftedTest e R)) hm.symm))
  · intro h
    apply hasScalarAction_of_lifted (e := e) T χ x
    intro R t a
    obtain ⟨p, rfl⟩ := (Q.points.equiv R).surjective t
    obtain ⟨b⟩ := a
    have eq := congrArg (P.equiv R) (h R p b)
    change P.equiv R (pointMap S.inclusion R p * rootPoint y R b * (pointMap S.inclusion R p)⁻¹) =
      P.equiv R (rootPoint y R (characterValue (Q.points.characterEquiv χ) R p * b)) at eq
    rw [map_mul, map_mul, map_inv, hx.rootPoint, hx.rootPoint] at eq
    have hp := Q.inclusion R p
    have hc := Q.points.characterValue χ R p
    have hm : ULift.up (characterValue (Q.points.characterEquiv χ) R p * b) =
        characterValue χ (liftedTest e R) (Q.points.equiv R p) * ULift.up b := by
      rw [hc]
      rfl
    exact (congrArg (fun g : GroupPoints G.val (liftedTest e R) =>
      g * rootPoint x (liftedTest e R) (ULift.up b) * g⁻¹) hp.symm).trans
      (eq.trans (congrArg (rootPoint x (liftedTest e R)) hm))

end AdditiveCoordinates

section RootsAndBases

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup Lie)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (absoluteRoots)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.AbstractPairing (Root)
open Specs.Pinning (SplitBorelPair AttachedDatum IsSimple)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open RootData.RootGroups (additivePoints rootSubgroups)
open RootData.BorelsAndChambers (geometricBorelRootSubgroups)
open Classification.Pinning (standardAdditiveLine)
open private additiveLineGroup rootPoint_eq rootPoint_zero rootPoint_comp rootPoint_eps_reduces
  rootPoint_injective_of_mono tangent_weight_of_scalarAction normalizes_of_point_conjugation
  from LinearAlgebraicGroups.RootData.RootGroups
open private mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private isKBorel_iff_of_isAlgClosed from LinearAlgebraicGroups.RootData.BorelNormalizer

set_option backward.isDefEq.respectTransparency false in
private theorem rootSubgroup_of_scalarCoordinate {k : Type u} [Field k] [CharZero k]
    {G : AffineAlgebraicGroup k} (T U : ClosedSubgroup G.val) {A : AdditiveLine k}
    {χ : Character T.group} (i : A.group ≅ U.group)
    (h : HasScalarAction T χ (i.hom ≫ U.inclusion)) :
    IsRootSubgroup T U χ := by
  refine ⟨characteristicZeroSmoothness k (closedSubgroupAlgebraicGroup U),
    ⟨A.operations, A.comultiplication, A.counit, A.antipode, ⟨i.symm⟩⟩, ?_,
    tangent_weight_of_scalarAction T U χ A i h⟩
  apply normalizes_of_point_conjugation T U
  intro R t p
  let j := ((groupPointsFunctor k).mapIso i).app R
  obtain ⟨a, ha⟩ := (additivePoints A R).surjective (j.inv p)
  have hp : pointMap i.hom R (additivePoints A R a) = p :=
    (congrArg j.hom ha).trans (j.groupIsoToMulEquiv.apply_symm_apply p)
  let b := Specs.CharacterPairing.characterValue χ R t * a
  refine ⟨pointMap i.hom R (additivePoints A R b), ?_⟩
  let g : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
  have hh : g * rootPoint (i.hom ≫ U.inclusion) R a * g⁻¹ =
    rootPoint (i.hom ≫ U.inclusion) R b := h R t a
  rw [rootPoint_eq, rootPoint_eq] at hh
  have he (x : R) : (additivePoints A R x) ≫ (i.hom ≫ U.inclusion).hom.hom =
      (pointMap i.hom R (additivePoints A R x)) ≫ U.inclusion.hom.hom :=
    (Category.assoc _ _ _).symm
  rw [he, he, hp] at hh
  exact hh.symm

set_option backward.isDefEq.respectTransparency false in
private theorem root_of_scalarCoordinate {k : Type u} [Field k]
    {G : AffineAlgebraicGroup k} (T U : ClosedSubgroup G.val)
    {A : AdditiveLine k} {χ : Character T.group} (i : A.group ≅ U.group)
    (h : IsRootSubgroup T U χ) (hne : χ ≠ 1) : χ ∈ absoluteRoots T := by
  let R := CommAlgCat.of k (DualNumber k)
  let x := i.hom ≫ U.inclusion
  let v : Lie k U.group := ⟨rootPoint i.hom R (DualNumber.eps : DualNumber k),
    rootPoint_eps_reduces i.hom⟩
  refine ⟨hne, mapPointKernel U.inclusion v, h.2.2.2 ⟨v, rfl⟩, ?_⟩
  intro hz
  letI : Mono U.inclusion.hom.hom := mono_over _ U.isClosedImmersion
  letI : IsIso i.hom.hom.hom := (Grp.forget (SchemeOver k)).map_isIso i.hom
  letI : Mono x.hom.hom := mono_comp i.hom.hom.hom U.inclusion.hom.hom
  have hv := congrArg (fun p : Lie k G.val => p.toMul.val) hz
  change rootPoint i.hom R (DualNumber.eps : DualNumber k) ≫ U.inclusion.hom.hom =
    (1 : GroupPoints G.val R) at hv
  rw [← rootPoint_comp, ← rootPoint_zero x R] at hv
  have he := rootPoint_injective_of_mono x R hv
  exact one_ne_zero (congrArg TrivSqZeroExt.snd he)

variable {e : F ≃+* k₀} {A : SplitBorelPair F} {B : SplitBorelPair k₀}
variable {P : GroupComparison e A.G B.G} (T : RelatedSubgroup P A.T B.T)

set_option backward.isDefEq.respectTransparency false in
private theorem RelatedSubgroup.root_small [CharZero k₀] {χ : Character A.T.group}
    (hχ : χ ∈ absoluteRoots A.T) :
    ∃ (U : ClosedSubgroup A.G.val) (V : ClosedSubgroup B.G.val),
      Nonempty (RelatedSubgroup P U V) ∧ IsRootSubgroup A.T U χ ∧
      IsRootSubgroup B.T V (T.points.characterEquiv χ) ∧
      T.points.characterEquiv χ ∈ absoluteRoots B.T := by
  obtain ⟨U, hU, _, _, ⟨L, i, hi⟩, _⟩ :=
    ((rootSubgroups A.G A.reductive A.T A.split A.maximal).2 χ hχ).2.2
  obtain ⟨V, ⟨Q⟩⟩ := P.existsSmallSubgroup U
  let M := standardAdditiveLine k₀
  obtain ⟨j, hj⟩ := (additiveLineComparison e L M).existsSmallMap Q.points i.hom
  let j' := @asIso _ _ _ _ j (hj.isIso_iff.mp i.isIso_hom)
  have hs := (T.scalarAction_iff (hj.comp Q.inclusion)).mp hi
  have hV := rootSubgroup_of_scalarCoordinate B.T V j' hs
  have hb : T.points.characterEquiv χ ≠ 1 := fun he =>
    hχ.1 (T.points.characterEquiv.injective (he.trans T.points.characterEquiv.map_one.symm))
  exact ⟨U, V, ⟨Q⟩, hU, hV, root_of_scalarCoordinate B.T V j' hV hb⟩

set_option backward.isDefEq.respectTransparency false in
private theorem RelatedSubgroup.root_large [CharZero F] {χ : Character A.T.group}
    (hχ : T.points.characterEquiv χ ∈ absoluteRoots B.T) :
    ∃ (U : ClosedSubgroup A.G.val) (V : ClosedSubgroup B.G.val),
      Nonempty (RelatedSubgroup P U V) ∧ IsRootSubgroup A.T U χ ∧
      IsRootSubgroup B.T V (T.points.characterEquiv χ) ∧ χ ∈ absoluteRoots A.T := by
  obtain ⟨V, hV, _, _, ⟨M, j, hj⟩, _⟩ :=
    ((rootSubgroups B.G B.reductive B.T B.split B.maximal).2 _ hχ).2.2
  obtain ⟨U, ⟨Q⟩⟩ := P.existsLargeSubgroup V
  let L := standardAdditiveLine F
  obtain ⟨i, hi⟩ := (additiveLineComparison e L M).existsLargeMap Q.points j.hom
  let i' := @asIso _ _ _ _ i (hi.isIso_iff.mpr j.isIso_hom)
  have hs := (T.scalarAction_iff (hi.comp Q.inclusion)).mpr hj
  have hU := rootSubgroup_of_scalarCoordinate A.T U i' hs
  have ha : χ ≠ 1 := fun he => hχ.1 (he ▸ T.points.characterEquiv.map_one)
  exact ⟨U, V, ⟨Q⟩, hU, hV, root_of_scalarCoordinate A.T U i' hU ha⟩

private def RelatedSubgroup.rootEquiv [CharZero F] [CharZero k₀] : Root A.T ≃ Root B.T :=
  T.points.characterEquiv.toEquiv.subtypeEquiv fun χ =>
    ⟨fun h => (T.root_small (χ := χ) h).choose_spec.choose_spec.2.2.2,
      fun h => (T.root_large (χ := χ) h).choose_spec.choose_spec.2.2.2⟩

private theorem RelatedSubgroup.positive_iff
    [CharZero F] [CharZero k₀] [IsAlgClosed F] [IsAlgClosed k₀]
    (S : RelatedSubgroup P A.B B.B) (a : Root A.T) :
    a ∈ subgroupRoots A.T A.B ↔ T.rootEquiv a ∈ subgroupRoots B.T B.B := by
  obtain ⟨U, V, ⟨Q⟩, hu, hv, _⟩ := T.root_small a.property
  have hA := (isKBorel_iff_of_isAlgClosed A.G A.B).mp A.borel
  have hB := (isKBorel_iff_of_isAlgClosed B.G B.B).mp B.borel
  exact (geometricBorelRootSubgroups A.G A.reductive A.T A.split A.maximal
    A.B hA A.containsTorus a U hu).trans
    ((Q.subgroupOf_iff S).trans
      (geometricBorelRootSubgroups B.G B.reductive B.T B.split B.maximal
        B.B hB B.containsTorus (T.rootEquiv a) V hv).symm)

private theorem RelatedSubgroup.simple_iff
    [CharZero F] [CharZero k₀] [IsAlgClosed F] [IsAlgClosed k₀]
    (S : RelatedSubgroup P A.B B.B) (a : Root A.T) :
    IsSimple A a ↔ IsSimple B (T.rootEquiv a) := by
  let f := T.points.characterEquiv
  let r := T.rootEquiv
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨(T.positive_iff S a).mp ha, ?_⟩
    intro b hb c hc hsum
    obtain ⟨b', rfl⟩ := r.surjective b
    obtain ⟨c', rfl⟩ := r.surjective c
    apply h b' ((T.positive_iff S b').mpr hb) c' ((T.positive_iff S c').mpr hc)
    apply f.injective
    change f a.val = f b'.val * f c'.val at hsum
    exact hsum.trans (f.map_mul _ _).symm
  · rintro ⟨ha, h⟩
    refine ⟨(T.positive_iff S a).mpr ha, ?_⟩
    intro b hb c hc hsum
    apply h (r b) ((T.positive_iff S b).mp hb) (r c) ((T.positive_iff S c).mp hc)
    change f a.val = f b.val * f c.val
    exact (congrArg f hsum).trans (f.map_mul _ _)

end RootsAndBases

section CartanTransport

open Specs.AbsoluteDynkinTypes (PreservesCartan HasDynkinType IsAbsolutelyAlmostSimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.Pinning (SplitBorelPair AttachedDatum)
open Classification.Pinning (datumExists)

/-- The root string through a different simple root determines each off-diagonal
Cartan entry. The roots and their base in the character lattice suffice. -/
private theorem cartanFromRootEquiv {I J X Y X' Y' : Type*}
    [Finite I] [Finite J] [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
    (D : RootDatum («ι» := I) X Y) (E : RootDatum («ι» := J) X' Y')
    (b : D.Base) (c : E.Base) (r : I ≃ J) (f : X ≃+ X')
    (hr : ∀ i, f (D.root i) = E.root (r i))
    (hs : ∀ i, i ∈ b.support ↔ r i ∈ c.support) :
    PreservesCartan (RootData.integralCartan D b) (RootData.integralCartan E c)
      (r.subtypeEquiv hs) := by
  classical
  let g : b.support ≃ c.support := r.subtypeEquiv hs
  intro i j
  change D.pairing j.val i.val = E.pairing (g j).val (g i).val
  by_cases hij : i = j
  · subst j
    rw [D.pairing_same, E.pairing_same]
  have hij' : g i ≠ g j := fun h => hij (g.injective h)
  have hm (x : X) : f x ∈ Set.range E.root ↔ x ∈ Set.range D.root := by
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨l, rfl⟩ := r.surjective k
      exact ⟨l, f.injective ((hr l).trans hk)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨r k, (hr k).symm⟩
  have hc (n : ℕ) : n ≤ D.chainTopCoeff i.val j.val ↔ n ≤ E.chainTopCoeff (g i).val (g j).val := by
    rw [← RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff (b.linearIndependent_pair_of_ne hij),
      ← RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff (c.linearIndependent_pair_of_ne hij')]
    change D.root j.val + n • D.root i.val ∈ Set.range D.root ↔
      E.root (r j.val) + n • E.root (r i.val) ∈ Set.range E.root
    simpa only [map_add, map_nsmul, hr] using (hm (D.root j.val + n • D.root i.val)).symm
  have htop : D.chainTopCoeff i.val j.val = E.chainTopCoeff (g i).val (g j).val :=
    le_antisymm ((hc _).mp le_rfl) ((hc _).mpr le_rfl)
  have hD := b.chainTopCoeff_eq_of_ne hij
  have hE := c.chainTopCoeff_eq_of_ne hij'
  have pD : D.pairingIn ℤ j.val i.val = D.pairing j.val i.val :=
    D.algebraMap_pairingIn ℤ j.val i.val
  have pE : E.pairingIn ℤ (g j).val (g i).val = E.pairing (g j).val (g i).val :=
    E.algebraMap_pairingIn ℤ (g j).val (g i).val
  omega

set_option backward.isDefEq.respectTransparency false in
private theorem comparedHasDynkinType {e : F ≃+* k₀}
    [CharZero F] [CharZero k₀] [IsAlgClosed F] [IsAlgClosed k₀]
    {A : SplitBorelPair F} {B : SplitBorelPair k₀} {P : GroupComparison e A.G B.G}
    (T : RelatedSubgroup P A.T B.T) (S : RelatedSubgroup P A.B B.B)
    (D : AttachedDatum A) (E : AttachedDatum B) (t : LieAlgebrasAndRepresentations.FiniteDynkinType)
    (hD : letI := D.comm; HasDynkinType (RootData.integralCartan D.datum.rootDatum D.base) t) :
    letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) t := by
  letI := D.comm
  letI := E.comm
  letI := D.datum.finiteRoots
  letI := E.datum.finiteRoots
  let r := T.rootEquiv
  let f := T.points.characterEquiv.toAdditive
  have hr (i : Specs.AbstractPairing.Root A.T) :
      f (D.datum.rootDatum.root i) = E.datum.rootDatum.root (r i) := by
    rw [D.datum.root_eq, E.datum.root_eq]
    rfl
  have hs (i : Specs.AbstractPairing.Root A.T) : i ∈ D.base.support ↔ r i ∈ E.base.support :=
    (D.simple_iff i).trans ((T.simple_iff S i).trans (E.simple_iff (r i)).symm)
  let g := r.subtypeEquiv hs
  have h := cartanFromRootEquiv D.datum.rootDatum E.datum.rootDatum D.base E.base r f hr hs
  obtain ⟨a, ha⟩ := hD
  refine ⟨g.symm.trans a, fun i j => ?_⟩
  have hij := h (g.symm i) (g.symm j)
  change RootData.integralCartan D.datum.rootDatum D.base (g.symm i) (g.symm j) =
    RootData.integralCartan E.datum.rootDatum E.base (g (g.symm i)) (g (g.symm j)) at hij
  rw [g.apply_symm_apply, g.apply_symm_apply] at hij
  exact hij.symm.trans (ha (g.symm i) (g.symm j))

set_option backward.isDefEq.respectTransparency false in
private theorem GroupComparison.absoluteType {e : F ≃+* k₀}
    [CharZero F] [CharZero k₀] {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup k₀}
    (P : GroupComparison e G H) (hG : IsSemisimple G)
    (t : LieAlgebrasAndRepresentations.FiniteDynkinType)
    (h : HasAbsoluteType G t) : HasAbsoluteType H t := by
  obtain ⟨A, hA, D, hD⟩ := h
  let Q := P.geometric
  have hgeo : IsSemisimple (GeometricGroup G) :=
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.semisimpleFieldExtension
      (K := AlgebraicClosure F) G hG.1 hG.2.1).mpr hG
  obtain ⟨B, hB, ⟨T⟩, ⟨S⟩⟩ := Q.existsSmallBorelPair hgeo A hA
  obtain ⟨E⟩ := datumExists B
  have hcomparison (G' : AffineAlgebraicGroup (AlgebraicClosure F))
      (H' : AffineAlgebraicGroup (AlgebraicClosure k₀)) (hA' : A.G = G') (hB' : B.G = H')
      (R : GroupComparison (closureEquiv e) G' H')
      (T' : RelatedSubgroup R (hA' ▸ A.T) (hB' ▸ B.T))
      (S' : RelatedSubgroup R (hA' ▸ A.B) (hB' ▸ B.B)) :
      letI := E.comm; HasDynkinType (RootData.integralCartan E.datum.rootDatum E.base) t := by
    subst G'
    subst H'
    exact comparedHasDynkinType T' S' D E t hD
  exact ⟨B, hB, E, hcomparison _ _ hA hB Q T S⟩

/-- A natural comparison of the affine point functors preserves the geometric
group predicates and the type of the attached Cartan matrix. -/
theorem realModelGeometry : RealModelGeometry.{u} := by
  intro F _ e G H compare hnat hG hsc t _ ht
  letI : CharZero F := charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  let P : GroupComparison e G H := ⟨compare, hnat⟩
  exact ⟨P.absolutelyAlmostSimple hG, P.simplyConnected hsc, P.absoluteType hG.1 t ht⟩

end CartanTransport

end LinearAlgebraicGroups.Arithmetic.ExceptionalRealModelGeometry
