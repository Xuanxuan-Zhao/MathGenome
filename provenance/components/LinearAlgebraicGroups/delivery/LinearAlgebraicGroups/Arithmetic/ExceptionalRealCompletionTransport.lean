import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalRealCompletionTransport
import LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
import LinearAlgebraicGroups.Arithmetic.ExceptionalCompletionGeometry
import LinearAlgebraicGroups.Arithmetic.ExceptionalRealModelGeometry
import LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import LinearAlgebraicGroups.Reductive.RadicalBaseChange
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.LinearAlgebra.Matrix.Reindex

noncomputable section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite Topology
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalRealCompletionTransport

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalRealCompletionTransport
open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (Index)
open Specs.StandardGroups (generalLinearPoints)
open AdelicGroups (PointsIn asMatrix)

variable {F : Type u} [Field F]

variable {k₀ : Type} [Field k₀]

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

variable (e : F ≃+* ℝ) {G : GroupScheme F} (P : AffinePresentation G.X)

private def transportedGroupLaw : NaturalGroupLaw (transportedScheme e P) where
  group R := (transportedSchemePoints e P R).group
  map_one {R S} f := by
    apply (transportedSchemePoints e P S).injective
    rw [transportedSchemePoints_naturality]
    change ((groupPointsFunctor F).obj G).map (realTestMap e f)
        (transportedSchemePoints e P R ((transportedSchemePoints e P R).symm 1)) =
      transportedSchemePoints e P S ((transportedSchemePoints e P S).symm 1)
    simp only [Equiv.apply_symm_apply]
    exact (((groupPointsFunctor F).obj G).map (realTestMap e f)).hom.map_one
  map_mul {R S} f p q := by
    apply (transportedSchemePoints e P S).injective
    rw [transportedSchemePoints_naturality]
    change ((groupPointsFunctor F).obj G).map (realTestMap e f)
        (transportedSchemePoints e P R ((transportedSchemePoints e P R).symm
          (transportedSchemePoints e P R p * transportedSchemePoints e P R q))) =
      transportedSchemePoints e P S ((transportedSchemePoints e P S).symm
        (transportedSchemePoints e P S (mapPoints f p) * transportedSchemePoints e P S (mapPoints f q)))
    simp only [Equiv.apply_symm_apply, transportedSchemePoints_naturality]
    exact (((groupPointsFunctor F).obj G).map (realTestMap e f)).hom.map_mul _ _

/-- The affine group law recovered from the natural group law on the
transported scheme points. -/
private def realGroupModel : AffineAlgebraicGroup ℝ :=
  let h := transportedScheme_affine e P
  let H : GroupScheme ℝ :=
    { X := transportedScheme e P
      grp := (groupLawEquiv (transportedScheme e P) h).symm (transportedGroupLaw e P) }
  ⟨H, h, transportedScheme_finiteType e P, transportedScheme_quasiCompact e P⟩

private def realGroupPoints (R : TestAlgebra ℝ) :
    GroupPoints (realGroupModel e P).val R ≃* GroupPoints G (realTestOver e R) where
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

private theorem realGroupPoints_naturality {R S : TestAlgebra ℝ} (f : R ⟶ S)
    (p : GroupPoints (realGroupModel e P).val R) :
    realGroupPoints e P S (((groupPointsFunctor ℝ).obj (realGroupModel e P).val).map f p) =
      ((groupPointsFunctor F).obj G).map (realTestMap e f) (realGroupPoints e P R p) :=
  transportedSchemePoints_naturality e P f p

end GroupModel

section TransportMorphisms

open private coordinateMap coordinateMap_spec specMap_surjective
  from LinearAlgebraicGroups.Arithmetic.IntegralModels

variable (e : F ≃+* ℝ) {X Y : SchemeOver F}
  (P : AffinePresentation X) (Q : AffinePresentation Y)

private def presentationMap (f : X ⟶ Y) : Q.coordinates ⟶ P.coordinates :=
  coordinateMap (P.iso.hom ≫ f ≫ Q.iso.inv)

private theorem presentationMap_spec (f : X ⟶ Y) :
    (testSpec F).map (presentationMap P Q f).op = P.iso.hom ≫ f ≫ Q.iso.inv :=
  coordinateMap_spec _

private def realCoordinateMap (f : Q.coordinates ⟶ P.coordinates) :
    transportedCoordinates e Q ⟶ transportedCoordinates e P := by
  let dP := smallerAlgebraEquiv e P.coordinates P.finiteType
  let dQ := smallerAlgebraEquiv e Q.coordinates Q.finiteType
  refine ConcreteCategory.ofHom (C := CommAlgCat ℝ)
    (X := transportedCoordinates e Q) (Y := transportedCoordinates e P)
    (@AlgHom.mk ℝ (transportedCoordinates e Q) (transportedCoordinates e P) _ _ _
      (transportedCoordinates e Q).algebra (transportedCoordinates e P).algebra
      (dP.toRingHom.comp (f.hom.toRingHom.comp dQ.symm.toRingHom)) ?_)
  intro x
  have hQ : dQ (algebraMap F Q.coordinates (e.symm x)) = algebraMap ℝ (transportedCoordinates e Q) x := by
    rw [smallerAlgebraEquiv_algebraMap, RingEquiv.apply_symm_apply]
  change dP (f.hom (dQ.symm (algebraMap ℝ (transportedCoordinates e Q) x))) =
    algebraMap ℝ (transportedCoordinates e P) x
  rw [← hQ, RingEquiv.symm_apply_apply, f.hom.commutes, smallerAlgebraEquiv_algebraMap,
    RingEquiv.apply_symm_apply]

private def realSchemeMap (f : X ⟶ Y) : transportedScheme e P ⟶ transportedScheme e Q :=
  (testSpec ℝ).map (realCoordinateMap e P Q (presentationMap P Q f)).op

private theorem realSchemeMap_points (f : X ⟶ Y) (R : TestAlgebra ℝ)
    (p : Points (transportedScheme e P) R) :
    transportedSchemePoints e Q R (p ≫ realSchemeMap e P Q f) = transportedSchemePoints e P R p ≫ f := by
  obtain ⟨a, rfl⟩ := (specPointsEquiv (transportedCoordinates e P) R).surjective p
  let b := presentationMap P Q f
  let bR := realCoordinateMap e P Q b
  have hcomp : specPointsEquiv (transportedCoordinates e P) R a ≫ realSchemeMap e P Q f =
      specPointsEquiv (transportedCoordinates e Q) R (bR ≫ a) :=
    ((testSpec ℝ).map_comp a.op bR.op).symm
  rw [hcomp]
  simp only [transportedSchemePoints, Equiv.trans_apply, Equiv.symm_apply_apply]
  let dP := smallerAlgebraEquiv e P.coordinates P.finiteType
  let dQ := smallerAlgebraEquiv e Q.coordinates Q.finiteType
  have hdP := smallerAlgebraEquiv_algebraMap e P.coordinates P.finiteType
  have hdQ := smallerAlgebraEquiv_algebraMap e Q.coordinates Q.finiteType
  have heq : liftAlgebraMap e dQ hdQ (bR ≫ a) = b ≫ liftAlgebraMap e dP hdP a := by
    apply CommAlgCat.hom_ext
    apply @AlgHom.ext F Q.coordinates (realTestOver e R) _ _ _ Q.coordinates.algebra
      (realTestOver e R).algebra
    intro x
    change ULift.up (a.hom (dP (b.hom (dQ.symm (dQ x))))) =
      ULift.up (a.hom (dP (b.hom x)))
    rw [RingEquiv.symm_apply_apply]
  change (testSpec F).map (liftAlgebraMap e dQ hdQ (bR ≫ a)).op ≫ Q.iso.hom =
    ((testSpec F).map (liftAlgebraMap e dP hdP a).op ≫ P.iso.hom) ≫ f
  rw [heq, op_comp, Functor.map_comp]
  simp only [b, presentationMap_spec, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem realSchemeMap_closed (f : X ⟶ Y) (hf : IsClosedImmersion f.left) :
    IsClosedImmersion (realSchemeMap e P Q f).left := by
  let b := presentationMap P Q f
  let bR := realCoordinateMap e P Q b
  have hb : IsClosedImmersion ((testSpec F).map b.op).left := by
    rw [presentationMap_spec P Q f]
    change IsClosedImmersion (P.iso.hom.left ≫ f.left ≫ Q.iso.inv.left)
    letI : IsIso P.iso.hom.left := inferInstance
    letI : IsIso Q.iso.inv.left := inferInstance
    exact inferInstance
  let b' := CommRingCat.ofHom b.hom.toRingHom
  have hs : Function.Surjective b.hom := specMap_surjective b' hb
  have hsR : Function.Surjective bR.hom :=
    (smallerAlgebraEquiv e P.coordinates P.finiteType).surjective.comp
      (hs.comp (smallerAlgebraEquiv e Q.coordinates Q.finiteType).symm.surjective)
  exact IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom bR.hom.toRingHom) hsR

end TransportMorphisms

section GroupMorphisms

variable (e : F ≃+* ℝ) {G H : GroupScheme F}
  (P : AffinePresentation G.X) (Q : AffinePresentation H.X)

private def realPointHom (f : G ⟶ H) :
    (groupPointsFunctor ℝ).obj (realGroupModel e P).val ⟶
      (groupPointsFunctor ℝ).obj (realGroupModel e Q).val where
  app R := GrpCat.ofHom ((realGroupPoints e Q R).symm.toMonoidHom.comp
    ((((groupPointsFunctor F).map f).app (realTestOver e R)).hom.comp
      (realGroupPoints e P R).toMonoidHom))
  naturality {R S} a := by
    apply GrpCat.ext
    intro p
    apply (realGroupPoints e Q S).injective
    change realGroupPoints e Q S (((realGroupPoints e Q S).symm)
      (((groupPointsFunctor F).map f).app (realTestOver e S)
        (realGroupPoints e P S (((groupPointsFunctor ℝ).obj (realGroupModel e P).val).map a p)))) =
      realGroupPoints e Q S (((groupPointsFunctor ℝ).obj (realGroupModel e Q).val).map a
        ((realGroupPoints e Q R).symm
          (((groupPointsFunctor F).map f).app (realTestOver e R) (realGroupPoints e P R p))))
    rw [MulEquiv.apply_symm_apply, realGroupPoints_naturality, realGroupPoints_naturality,
      MulEquiv.apply_symm_apply]
    exact NatTrans.naturality_apply ((groupPointsFunctor F).map f) (realTestMap e a) _

private def realGroupMap (f : G ⟶ H) :
    (realGroupModel e P).val ⟶ (realGroupModel e Q).val :=
  (groupHomEquiv _ _ (transportedScheme_affine e P)).symm (realPointHom e P Q f)

private theorem realGroupMap_points (f : G ⟶ H) (R : TestAlgebra ℝ)
    (p : GroupPoints (realGroupModel e P).val R) :
    realGroupPoints e Q R (((groupPointsFunctor ℝ).map (realGroupMap e P Q f)).app R p) =
      ((groupPointsFunctor F).map f).app (realTestOver e R) (realGroupPoints e P R p) := by
  have hg : (groupPointsFunctor ℝ).map (realGroupMap e P Q f) = realPointHom e P Q f :=
    (groupHomEquiv _ _ (transportedScheme_affine e P)).apply_symm_apply _
  rw [hg]
  exact MulEquiv.apply_symm_apply _ _

private theorem realGroupMap_scheme (f : G ⟶ H) :
    (realGroupMap e P Q f).hom.hom = realSchemeMap e P Q f.hom.hom := by
  let R := transportedCoordinates e P
  let p : GroupPoints (realGroupModel e P).val R := 𝟙 _
  have hp := realGroupMap_points e P Q f R p
  have hq := realSchemeMap_points e P Q f.hom.hom R p
  have h : transportedSchemePoints e Q R (p ≫ (realGroupMap e P Q f).hom.hom) =
      transportedSchemePoints e Q R (p ≫ realSchemeMap e P Q f.hom.hom) := hp.trans hq.symm
  have he := (transportedSchemePoints e Q R).injective h
  change (𝟙 (transportedScheme e P)) ≫ (realGroupMap e P Q f).hom.hom =
    (𝟙 (transportedScheme e P)) ≫ realSchemeMap e P Q f.hom.hom at he
  have hl : (𝟙 (transportedScheme e P)) ≫ (realGroupMap e P Q f).hom.hom =
      (realGroupMap e P Q f).hom.hom := Category.id_comp _
  have hr : (𝟙 (transportedScheme e P)) ≫ realSchemeMap e P Q f.hom.hom =
      realSchemeMap e P Q f.hom.hom := Category.id_comp _
  exact Eq.trans hl.symm (Eq.trans he hr)

end GroupMorphisms

section Matrices

private def lowerIndex (n : ℕ) : Index.{u} n ≃ Index.{0} n :=
  Equiv.ulift.trans Equiv.ulift.symm

private def matrixRingEquiv {R S I J : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (r : R ≃+* S) (b : I ≃ J) : Matrix I I R ≃+* Matrix J J S :=
  (Matrix.reindexRingEquiv R b).trans r.mapMatrix

private def matrixGroupEquiv {R S I J : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (r : R ≃+* S) (b : I ≃ J) :
    Matrix.GeneralLinearGroup I R ≃* Matrix.GeneralLinearGroup J S :=
  Units.mapEquiv (matrixRingEquiv r b).toMulEquiv

private def matrixGroupHomeomorph {R S I J : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (r : R ≃+* S) (b : I ≃ J) (hr : Continuous r) (hs : Continuous r.symm) :
    Matrix.GeneralLinearGroup I R ≃ₜ* Matrix.GeneralLinearGroup J S :=
  Units.mapContinuousMulEquiv
    { toMulEquiv := (matrixRingEquiv r b).toMulEquiv
      continuous_toFun := continuous_matrix fun i j => by
        change Continuous (fun a : Matrix I I R => r (a (b.symm i) (b.symm j)))
        exact hr.comp (continuous_id.matrix_elem _ _)
      continuous_invFun := continuous_matrix fun i j => by
        change Continuous (fun a : Matrix J J S => r.symm (a (b i) (b j)))
        exact hs.comp (continuous_id.matrix_elem _ _) }

variable (e : F ≃+* ℝ)

private def completionTestIso : realTestOver e realTest ≅ CommAlgCat.of F F := by
  letI := realTestAlgebra e realTest
  exact CommAlgCat.isoMk
    ({ (ULift.ringEquiv.trans e.symm : ULift.{u} ℝ ≃+* F) with
       commutes' := fun x => e.symm_apply_apply x } : ULift.{u} ℝ ≃ₐ[F] F)

private theorem completionTestIso_hom : (completionTestIso e).hom = completionTestMap e := by
  apply CommAlgCat.hom_ext
  rfl

private def realEvaluation {G : GroupScheme F} (P : AffinePresentation G.X) :
    GroupPoints (realGroupModel e P).val realTest ≃* GroupPoints G (CommAlgCat.of F F) :=
  (realGroupPoints e P realTest).trans
    ((((groupPointsFunctor F).obj G).mapIso (completionTestIso e)).groupIsoToMulEquiv)

private theorem realEvaluation_apply {G : GroupScheme F} (P : AffinePresentation G.X)
    (p : GroupPoints (realGroupModel e P).val realTest) :
    realEvaluation e P p =
      ((groupPointsFunctor F).obj G).map (completionTestMap e) (realGroupPoints e P realTest p) := by
  change ((groupPointsFunctor F).obj G).map (completionTestIso e).hom
    (realGroupPoints e P realTest p) = _
  rw [completionTestIso_hom]

variable {G : AffineAlgebraicGroup F} (i : MatrixRealization G)
  (P : AffinePresentation G.val.X) (Q : AffinePresentation i.ambient.val.X)

private def realAmbientMatrices (R : TestAlgebra ℝ) :
    GroupPoints (realGroupModel e Q).val R ≃*
      Matrix.GeneralLinearGroup (Index.{0} i.size) R :=
  (realGroupPoints e Q R).trans <|
    ((i.matrix.app (realTestOver e R)).groupIsoToMulEquiv).trans <|
      matrixGroupEquiv ULift.ringEquiv (lowerIndex i.size)

set_option backward.isDefEq.respectTransparency false in
private def realMatrixPoints :
    (groupPointsFunctor ℝ).obj (realGroupModel e Q).val ≅
      generalLinearPoints ℝ (Index.{0} i.size) :=
  NatIso.ofComponents (fun R => (realAmbientMatrices e i Q R).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro p
    change realAmbientMatrices e i Q S
        (((groupPointsFunctor ℝ).obj (realGroupModel e Q).val).map f p) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (realAmbientMatrices e i Q R p)
    change matrixGroupEquiv ULift.ringEquiv (lowerIndex i.size)
        (i.matrix.hom.app (realTestOver e S)
          (realGroupPoints e Q S
            (((groupPointsFunctor ℝ).obj (realGroupModel e Q).val).map f p))) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom
        (matrixGroupEquiv ULift.ringEquiv (lowerIndex i.size)
          (i.matrix.hom.app (realTestOver e R) (realGroupPoints e Q R p)))
    rw [realGroupPoints_naturality, NatTrans.naturality_apply i.matrix.hom]
    apply Units.ext
    apply Matrix.ext
    intro a b
    rfl)

private def realMatrixRealization : MatrixRealization (realGroupModel e P) where
  size := i.size
  ambient := realGroupModel e Q
  matrix := realMatrixPoints e i Q
  embedding := realGroupMap e P Q i.embedding
  closed := by
    change IsClosedImmersion (realGroupMap e P Q i.embedding).hom.hom.left
    rw [realGroupMap_scheme]
    exact realSchemeMap_closed e P Q i.embedding.hom.hom i.closed

set_option backward.isDefEq.respectTransparency false in
private theorem realMatrixRealization_entries
    (p : PointsIn (realMatrixRealization e i P Q) ℝ) :
    asMatrix (realMatrixRealization e i P Q) ℝ p =
      matrixGroupEquiv e (lowerIndex i.size) (asMatrix i F (realEvaluation e P p)) := by
  change matrixGroupEquiv ULift.ringEquiv (lowerIndex i.size)
      (i.matrix.hom.app (realTestOver e realTest)
        (realGroupPoints e Q realTest (((groupPointsFunctor ℝ).map
          (realGroupMap e P Q i.embedding)).app realTest p))) = _
  change GroupPoints (realGroupModel e P).val realTest at p
  rw [realGroupMap_points e P Q i.embedding realTest p, realEvaluation_apply e P p]
  let f := ((groupPointsFunctor F).map i.embedding) ≫ i.matrix.hom
  change matrixGroupEquiv ULift.ringEquiv (lowerIndex i.size)
      (f.app (realTestOver e realTest) (realGroupPoints e P realTest p)) =
    matrixGroupEquiv e (lowerIndex i.size)
      (f.app (CommAlgCat.of F F)
        (((groupPointsFunctor F).obj G.val).map (completionTestMap e)
          (realGroupPoints e P realTest p)))
  rw [NatTrans.naturality_apply f]
  apply Units.ext
  apply Matrix.ext
  intro a b
  change _ = e (e.symm _)
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- The comparison on rational points is a homeomorphism for the
matrix topologies of the original and transported realizations. -/
private def realEvaluationHomeomorph [TopologicalSpace F]
    (he : Continuous e) (hs : Continuous e.symm) :
    PointsIn (realMatrixRealization e i P Q) ℝ ≃ₜ* PointsIn i F := by
  let h := matrixGroupHomeomorph e (lowerIndex i.size) he hs
  let v : PointsIn (realMatrixRealization e i P Q) ℝ ≃* PointsIn i F := realEvaluation e P
  have hv : h ∘ asMatrix i F ∘ v = asMatrix (realMatrixRealization e i P Q) ℝ :=
    funext fun p => (realMatrixRealization_entries e i P Q p).symm
  have hind : IsInducing v :=
    ((h.isInducing.comp (.induced (asMatrix i F))).of_comp_iff).mp
      (by
        change IsInducing (h ∘ asMatrix i F ∘ v)
        rw [hv]
        exact .induced _)
  exact { v, v.toEquiv.toHomeomorphOfIsInducing hind with }

end Matrices

section RadicalPoints

open Specs.GeometricRadicals (IsReductive)
open Specs.BorelsAndChambers (contractingSubgroup)
open CocharacterDynamics (HasLimit)
open private limitIsParabolic from LinearAlgebraicGroups.Relative.MaximalSplitTori

/-- Rational parabolic radicals and cocharacter contracting subgroups
give the same generating set at the ground field. -/
theorem parabolicRadicalPoints_eq_cocharacterRadicalPoints
    [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G) (hG : IsReductive G) :
    parabolicRadicalPoints G = cocharacterRadicalPoints G := by
  ext g
  constructor
  · rintro ⟨P, hp, U, hu, x, rfl⟩
    obtain ⟨c, D, _, _, hrad, _⟩ := LocalCocharacterEvaluation.parabolicRadicalEvaluation.{u, 0} G i P hp
    obtain ⟨j, hj⟩ := hrad U hu
    refine ⟨c, D, ?_⟩
    refine ⟨((groupPointsFunctor F).map j.hom).app (CommAlgCat.of F F) x, ?_⟩
    change ((groupPointsFunctor F).map (j.hom ≫ D.contracting.inclusion)).app
      (CommAlgCat.of F F) x = _
    rw [hj]
  · rintro ⟨c, D, x, rfl⟩
    have hr := Relative.SplitContractingRadical.contractingSubgroupIsRadical G hG c D
    refine ⟨D.parabolic, limitIsParabolic G hG c D, contractingSubgroup D, hr.1, x, ?_⟩
    change ((groupPointsFunctor F).map
      (D.contractingToParabolic ≫ D.parabolic.inclusion)).app (CommAlgCat.of F F) x = _
    rw [D.contracting_in_G]

/-- A contraction on rational points is precisely a cocharacter orbit
with polynomial extension and limit the identity. -/
theorem mem_cocharacterRadicalPoints_iff (G : AffineAlgebraicGroup F)
    (p : GroupPoints G.val (CommAlgCat.of F F)) :
    p ∈ cocharacterRadicalPoints G ↔
      ∃ c : Specs.CharacterDescent.Cocharacter G.val, HasLimit c p 1 := by
  constructor
  · rintro ⟨c, D, h⟩
    exact ⟨c, (D.contracting_points (CommAlgCat.of F F) p).mpr h⟩
  · rintro ⟨c, h⟩
    obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition G c
    exact ⟨c, D, (D.contracting_points (CommAlgCat.of F F) p).mp h⟩

end RadicalPoints

section Cocharacters

open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics (cocharacterPoint unitPoint mapPoints_unitPoint)
open private gm unitEquiv unitEquiv_unitPoint from
  LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

variable (e : F ≃+* ℝ)

private def liftUnits (R : TestAlgebra ℝ) : Rˣ ≃* (ULift.{u} R)ˣ :=
  Units.mapEquiv ULift.ringEquiv.symm.toMulEquiv

private def multiplicativeLinePoints (R : TestAlgebra ℝ) :
    GroupPoints (gm ℝ) R ≃* GroupPoints (gm F) (realTestOver e R) :=
  (unitEquiv R).trans ((liftUnits R).trans (unitEquiv (realTestOver e R)).symm)

private theorem multiplicativeLinePoints_unit (R : TestAlgebra ℝ) (x : Rˣ) :
    multiplicativeLinePoints e R (unitPoint R x) =
      unitPoint (realTestOver e R) (liftUnits R x) := by
  change (unitEquiv (realTestOver e R)).symm (liftUnits R (unitEquiv R (unitPoint R x))) = _
  rw [unitEquiv_unitPoint]
  apply (unitEquiv (realTestOver e R)).injective
  rw [MulEquiv.apply_symm_apply, unitEquiv_unitPoint]

private theorem multiplicativeLinePoints_naturality {R S : TestAlgebra ℝ} (a : R ⟶ S)
    (x : GroupPoints (gm ℝ) R) :
    multiplicativeLinePoints e S (mapPoints a x) =
      mapPoints (realTestMap e a) (multiplicativeLinePoints e R x) := by
  have hx : unitPoint R (unitEquiv R x) = x :=
    (unitEquiv R).injective (unitEquiv_unitPoint R (unitEquiv R x))
  rw [← hx, mapPoints_unitPoint, multiplicativeLinePoints_unit,
    multiplicativeLinePoints_unit, mapPoints_unitPoint]
  rfl

variable {G : GroupScheme F} (P : AffinePresentation G.X)

private def realCocharacterHom (c : Cocharacter G) :
    (groupPointsFunctor ℝ).obj (gm ℝ) ⟶ (groupPointsFunctor ℝ).obj (realGroupModel e P).val where
  app R := GrpCat.ofHom ((realGroupPoints e P R).symm.toMonoidHom.comp
    ((((groupPointsFunctor F).map c).app (realTestOver e R)).hom.comp
      (multiplicativeLinePoints e R).toMonoidHom))
  naturality {R S} a := by
    apply GrpCat.ext
    intro x
    apply (realGroupPoints e P S).injective
    change realGroupPoints e P S ((realGroupPoints e P S).symm
        (((groupPointsFunctor F).map c).app (realTestOver e S)
          (multiplicativeLinePoints e S (mapPoints a x)))) =
      realGroupPoints e P S (((groupPointsFunctor ℝ).obj (realGroupModel e P).val).map a
        ((realGroupPoints e P R).symm
          (((groupPointsFunctor F).map c).app (realTestOver e R) (multiplicativeLinePoints e R x))))
    rw [MulEquiv.apply_symm_apply, realGroupPoints_naturality,
      MulEquiv.apply_symm_apply, multiplicativeLinePoints_naturality]
    exact NatTrans.naturality_apply ((groupPointsFunctor F).map c) (realTestMap e a) _

private theorem gmReal_affine : IsAffine (gm ℝ).X.left := by
  change IsAffine (Spec (CommRingCat.of (MonoidAlgebra ℝ Specs.DiagonalizableGroups.IntegerCharacters)))
  infer_instance

private def realCocharacter (c : Cocharacter G) : Cocharacter (realGroupModel e P).val :=
  (groupHomEquiv _ _ gmReal_affine).symm (realCocharacterHom e P c)

private theorem realCocharacter_point (c : Cocharacter G) (R : TestAlgebra ℝ) (x : Rˣ) :
    realGroupPoints e P R (cocharacterPoint (realCocharacter e P c) R x) =
      cocharacterPoint c (realTestOver e R) (liftUnits R x) := by
  have hc : (groupPointsFunctor ℝ).map (realCocharacter e P c) = realCocharacterHom e P c :=
    (groupHomEquiv _ _ gmReal_affine).apply_symm_apply _
  unfold cocharacterPoint
  rw [hc]
  change realGroupPoints e P R ((realGroupPoints e P R).symm
    (((groupPointsFunctor F).map c).app (realTestOver e R)
      (multiplicativeLinePoints e R (unitPoint R x)))) = _
  rw [MulEquiv.apply_symm_apply, multiplicativeLinePoints_unit]

end Cocharacters

section OrbitParameters

open CocharacterDynamics (polynomialAlgebra laurentAlgebra polynomialToLaurent polynomialEvaluate
  laurentConstants laurentParameter cocharacterPoint mapPoints_cocharacterPoint HasLimit orbit)
open Specs.CharacterDescent (Cocharacter)
open scoped Polynomial LaurentPolynomial

variable (e : F ≃+* ℝ)

private def liftedTestIso (R : TestAlgebra ℝ) (A : TestAlgebra F) (r : R ≃+* A)
    (hr : ∀ x : F, r (algebraMap ℝ R (e x)) = algebraMap F A x) :
    realTestOver e R ≅ A := by
  letI := realTestAlgebra e R
  exact CommAlgCat.isoMk
    ({ (ULift.ringEquiv.trans r : ULift.{u} R ≃+* A) with
      commutes' := hr } : ULift.{u} R ≃ₐ[F] A)

private abbrev fieldTest (k : Type u) [Field k] : TestAlgebra k := CommAlgCat.of k k

private def completionPolynomialIso :
    realTestOver e (polynomialAlgebra realTest) ≅ polynomialAlgebra (fieldTest F) :=
  liftedTestIso e _ _ (Polynomial.mapEquiv e.symm) (fun x => by
    change Polynomial.map e.symm.toRingHom (Polynomial.C (e x)) = Polynomial.C x
    rw [Polynomial.map_C]
    exact congrArg Polynomial.C (e.symm_apply_apply x))

private def completionLaurentIso :
    realTestOver e (laurentAlgebra realTest) ≅ laurentAlgebra (fieldTest F) :=
  liftedTestIso e _ _ (AddMonoidAlgebra.mapRingEquiv ℤ e.symm) (fun x => by
    change AddMonoidAlgebra.mapRingEquiv ℤ e.symm (LaurentPolynomial.C (e x)) =
      LaurentPolynomial.C x
    change AddMonoidAlgebra.mapRingEquiv ℤ e.symm (AddMonoidAlgebra.single 0 (e x)) =
      AddMonoidAlgebra.single 0 x
    rw [AddMonoidAlgebra.mapRingEquiv_single, RingEquiv.symm_apply_apply])

private theorem completionPolynomialIso_toLaurent :
    realTestMap e (polynomialToLaurent realTest) ≫ (completionLaurentIso e).hom =
      (completionPolynomialIso e).hom ≫ polynomialToLaurent (fieldTest F) := by
  apply CommAlgCat.hom_ext
  apply @AlgHom.ext F _ _ _ _ _ (realTestOver e (polynomialAlgebra realTest)).algebra _
  rintro ⟨p⟩
  let m := AddMonoidAlgebra.mapRingEquiv ℤ e.symm
  have h : m.toRingHom.comp Polynomial.toLaurent =
      Polynomial.toLaurent.comp (Polynomial.mapRingHom e.symm.toRingHom) := by
    apply Polynomial.ringHom_ext
    · intro z
      change m (Polynomial.toLaurent (Polynomial.C z)) =
        Polynomial.toLaurent (Polynomial.map e.symm.toRingHom (Polynomial.C z))
      simp only [Polynomial.toLaurent_C, Polynomial.map_C]
      exact AddMonoidAlgebra.mapRingEquiv_single e.symm _ _
    · change m (Polynomial.toLaurent Polynomial.X) =
        Polynomial.toLaurent (Polynomial.map e.symm.toRingHom Polynomial.X)
      simp only [Polynomial.map_X, Polynomial.toLaurent_X]
      change AddMonoidAlgebra.mapRingEquiv ℤ e.symm (AddMonoidAlgebra.single 1 1) =
        AddMonoidAlgebra.single 1 1
      rw [AddMonoidAlgebra.mapRingEquiv_single, map_one]
  exact DFunLike.congr_fun h p

private theorem completionPolynomialIso_evaluate :
    realTestMap e (polynomialEvaluate realTest 0) ≫ completionTestMap e =
      (completionPolynomialIso e).hom ≫ polynomialEvaluate (fieldTest F) 0 := by
  apply CommAlgCat.hom_ext
  apply @AlgHom.ext F _ _ _ _ _ (realTestOver e (polynomialAlgebra realTest)).algebra _
  rintro ⟨p⟩
  change e.symm (Polynomial.eval 0 p) = Polynomial.eval 0 (Polynomial.map e.symm.toRingHom p)
  exact (Polynomial.eval_zero_map e.symm.toRingHom p).symm

private theorem completionLaurentIso_constants :
    realTestMap e (laurentConstants realTest) ≫ (completionLaurentIso e).hom =
      completionTestMap e ≫ laurentConstants (fieldTest F) := by
  apply CommAlgCat.hom_ext
  apply @AlgHom.ext F _ _ _ _ _ (realTestOver e realTest).algebra _
  rintro ⟨x⟩
  change AddMonoidAlgebra.mapRingEquiv ℤ e.symm (AddMonoidAlgebra.single 0 x) =
    AddMonoidAlgebra.single 0 (e.symm x)
  exact AddMonoidAlgebra.mapRingEquiv_single e.symm _ _

private theorem completionLaurentIso_parameter :
    Units.map (completionLaurentIso e).hom.hom.toMonoidHom
        (liftUnits (laurentAlgebra realTest) (laurentParameter realTest)) =
      laurentParameter (fieldTest F) := by
  apply Units.ext
  change AddMonoidAlgebra.mapRingEquiv ℤ e.symm (AddMonoidAlgebra.single 1 1) =
    AddMonoidAlgebra.single 1 1
  rw [AddMonoidAlgebra.mapRingEquiv_single, map_one]

variable {G : GroupScheme F} (P : AffinePresentation G.X)

private def compareTestPoints (R : TestAlgebra ℝ) (A : TestAlgebra F)
    (s : realTestOver e R ≅ A) :
    GroupPoints (realGroupModel e P).val R ≃* GroupPoints G A :=
  (realGroupPoints e P R).trans ((((groupPointsFunctor F).obj G).mapIso s).groupIsoToMulEquiv)

private theorem compareTestPoints_map {R S : TestAlgebra ℝ} {A B : TestAlgebra F}
    (s : realTestOver e R ≅ A) (t : realTestOver e S ≅ B)
    (a : R ⟶ S) (b : A ⟶ B) (hsq : realTestMap e a ≫ t.hom = s.hom ≫ b)
    (p : GroupPoints (realGroupModel e P).val R) :
    compareTestPoints e P S B t (mapPoints a p) =
      mapPoints b (compareTestPoints e P R A s p) := by
  let U := (groupPointsFunctor F).obj G
  change U.map t.hom (realGroupPoints e P S
      (((groupPointsFunctor ℝ).obj (realGroupModel e P).val).map a p)) =
    U.map b (U.map s.hom (realGroupPoints e P R p))
  rw [realGroupPoints_naturality]
  have h := congrArg (fun f => U.map f (realGroupPoints e P R p)) hsq
  simpa only [Functor.map_comp, GrpCat.comp_apply] using h

private abbrev polynomialPoints :=
  compareTestPoints e P _ _ (completionPolynomialIso e)

private abbrev laurentPoints :=
  compareTestPoints e P _ _ (completionLaurentIso e)

set_option backward.isDefEq.respectTransparency false in
private theorem laurentPoints_orbit (c : Cocharacter G)
    (p : GroupPoints (realGroupModel e P).val realTest) :
    laurentPoints e P (orbit (realCocharacter e P c) p) =
      orbit c (realEvaluation e P p) := by
  have hc := compareTestPoints_map e P (completionTestIso e) (completionLaurentIso e)
    (laurentConstants realTest) (laurentConstants (fieldTest F))
    (by rw [completionTestIso_hom]; exact completionLaurentIso_constants e) p
  have ht : laurentPoints e P
      (cocharacterPoint (realCocharacter e P c) (laurentAlgebra realTest) (laurentParameter realTest)) =
      cocharacterPoint c (laurentAlgebra (fieldTest F)) (laurentParameter (fieldTest F)) := by
    change mapPoints (completionLaurentIso e).hom
      (realGroupPoints e P (laurentAlgebra realTest)
        (cocharacterPoint (realCocharacter e P c) (laurentAlgebra realTest) (laurentParameter realTest))) = _
    rw [realCocharacter_point, mapPoints_cocharacterPoint, completionLaurentIso_parameter]
  unfold orbit
  rw [(laurentPoints e P).map_mul, (laurentPoints e P).map_mul, (laurentPoints e P).map_inv]
  rw [ht, hc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- For a cocharacter of the completion group, its transported real
cocharacter has the same polynomial extensions and limits on rational points. -/
private theorem realCocharacter_hasLimit (c : Cocharacter G)
    (p z : GroupPoints (realGroupModel e P).val realTest) :
    HasLimit (realCocharacter e P c) p z ↔
      HasLimit c (realEvaluation e P p) (realEvaluation e P z) := by
  have hL := compareTestPoints_map e P (completionPolynomialIso e) (completionLaurentIso e)
    (polynomialToLaurent realTest) (polynomialToLaurent (fieldTest F))
    (completionPolynomialIso_toLaurent e)
  have hP := compareTestPoints_map e P (completionPolynomialIso e) (completionTestIso e)
    (polynomialEvaluate realTest 0) (polynomialEvaluate (fieldTest F) 0)
    (by rw [completionTestIso_hom]; exact completionPolynomialIso_evaluate e)
  constructor
  · rintro ⟨a, ha, hz⟩
    refine ⟨polynomialPoints e P a, ?_, ?_⟩
    · exact (hL a).symm.trans ((congrArg (laurentPoints e P) ha).trans
        (laurentPoints_orbit e P c p))
    · exact (hP a).symm.trans (congrArg (realEvaluation e P) hz)
  · rintro ⟨a, ha, hz⟩
    let b := (polynomialPoints e P).symm a
    have hb : polynomialPoints e P b = a := (polynomialPoints e P).apply_symm_apply a
    refine ⟨b, (laurentPoints e P).injective ?_, (realEvaluation e P).injective ?_⟩
    · change laurentPoints e P (mapPoints (polynomialToLaurent realTest) b) = _
      rw [hL b, hb, ha, laurentPoints_orbit]
    · change realEvaluation e P (mapPoints (polynomialEvaluate realTest 0) b) =
        realEvaluation e P z
      change compareTestPoints e P _ _ (completionTestIso e)
        (mapPoints (polynomialEvaluate realTest 0) b) = realEvaluation e P z
      rw [hP b, hb, hz]

end OrbitParameters

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

variable (e : F ≃+* ℝ) (A : AffineAlgebraicGroup F) {B : GroupScheme F}

private theorem groupHom_of_liftedPoints
    (τ : ∀ R : TestAlgebra ℝ, GroupPoints A.val (realTestOver e R) →*
      GroupPoints B (realTestOver e R))
    (hτ : ∀ {R S : TestAlgebra ℝ} (a : R ⟶ S) (p : GroupPoints A.val (realTestOver e R)),
      τ S (mapPoints (realTestMap e a) p) =
        mapPoints (realTestMap e a) (τ R p)) :
    ∃ f : A.val ⟶ B, ∀ R : TestAlgebra ℝ, ∀ p : GroupPoints A.val (realTestOver e R),
      τ R p = ((groupPointsFunctor F).map f).app (realTestOver e R) p := by
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
      rw [show p = toUnit ((testSpec F).obj (op (realTestOver e R))) from toUnit_unique _ _]
      change (1 : Points A.val.X (realTestOver e R)) ≫ f = 1
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

section ContractingRadicalTransport

open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (IntegerCharacters)
open Specs.GeometricRadicals (IsReductive)
open private gm from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private def multiplicativeLine (k : Type u) [Field k] : AffineAlgebraicGroup k := by
  letI : Group.FG IntegerCharacters.{u} :=
    Group.fg_of_surjective
      (f := (MulEquiv.ulift.symm : Multiplicative ℤ ≃* IntegerCharacters.{u}).toMonoidHom)
      MulEquiv.ulift.symm.surjective
  exact Specs.StandardGroups.spectrum k (MonoidAlgebra k IntegerCharacters.{u})

variable (e : F ≃+* ℝ) {G : GroupScheme F} (P : AffinePresentation G.X)

set_option backward.isDefEq.respectTransparency false in
private theorem realCocharacter_surjective :
    Function.Surjective (realCocharacter e P) := by
  intro d
  let t : ∀ R : TestAlgebra ℝ, GroupPoints (gm F) (realTestOver e R) →*
      GroupPoints G (realTestOver e R) := fun R =>
    (realGroupPoints e P R).toMonoidHom.comp
      ((((groupPointsFunctor ℝ).map d).app R).hom.comp
        (multiplicativeLinePoints e R).symm.toMonoidHom)
  have ht {R S : TestAlgebra ℝ} (a : R ⟶ S) (x : GroupPoints (gm F) (realTestOver e R)) :
      t S (mapPoints (realTestMap e a) x) = mapPoints (realTestMap e a) (t R x) := by
    obtain ⟨z, rfl⟩ := (multiplicativeLinePoints e R).surjective x
    change realGroupPoints e P S (((groupPointsFunctor ℝ).map d).app S
        ((multiplicativeLinePoints e S).symm
          (mapPoints (realTestMap e a) (multiplicativeLinePoints e R z)))) =
      mapPoints (realTestMap e a)
        (realGroupPoints e P R (((groupPointsFunctor ℝ).map d).app R
          ((multiplicativeLinePoints e R).symm (multiplicativeLinePoints e R z))))
    rw [← multiplicativeLinePoints_naturality, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    have h := NatTrans.naturality_apply ((groupPointsFunctor ℝ).map d) a z
    change realGroupPoints e P S (((groupPointsFunctor ℝ).map d).app S
      (((groupPointsFunctor ℝ).obj (gm ℝ)).map a z)) = _
    rw [h, realGroupPoints_naturality]
    rfl
  obtain ⟨c, hc⟩ := groupHom_of_liftedPoints e (multiplicativeLine F) t ht
  refine ⟨c, ?_⟩
  apply (groupHomEquiv _ _ gmReal_affine).injective
  change (groupPointsFunctor ℝ).map (realCocharacter e P c) = (groupPointsFunctor ℝ).map d
  have hfun : (groupPointsFunctor ℝ).map (realCocharacter e P c) = realCocharacterHom e P c :=
    (groupHomEquiv _ _ gmReal_affine).apply_symm_apply _
  rw [hfun]
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro x
  change (realGroupPoints e P R).symm
      (((groupPointsFunctor F).map c).app (realTestOver e R) (multiplicativeLinePoints e R x)) =
    ((groupPointsFunctor ℝ).map d).app R x
  rw [← hc R]
  change (realGroupPoints e P R).symm (realGroupPoints e P R
      (((groupPointsFunctor ℝ).map d).app R
        ((multiplicativeLinePoints e R).symm (multiplicativeLinePoints e R x)))) = _
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem realEvaluation_contractingPoints {A : AffineAlgebraicGroup F}
    (Q : AffinePresentation A.val.X) (p : GroupPoints (realGroupModel e Q).val realTest) :
    p ∈ cocharacterRadicalPoints (realGroupModel e Q) ↔
      realEvaluation e Q p ∈ cocharacterRadicalPoints A := by
  rw [mem_cocharacterRadicalPoints_iff, mem_cocharacterRadicalPoints_iff]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨d, rfl⟩ := realCocharacter_surjective e Q c
    refine ⟨d, ?_⟩
    have h := (realCocharacter_hasLimit e Q d p 1).mp hc
    rwa [(realEvaluation e Q).map_one] at h
  · rintro ⟨c, hc⟩
    refine ⟨realCocharacter e Q c, (realCocharacter_hasLimit e Q c p 1).mpr ?_⟩
    rwa [(realEvaluation e Q).map_one]

private theorem realEvaluation_contractingClosure {A : AffineAlgebraicGroup F}
    (Q : AffinePresentation A.val.X) (p : GroupPoints (realGroupModel e Q).val realTest) :
    p ∈ Subgroup.closure (cocharacterRadicalPoints (realGroupModel e Q)) ↔
      realEvaluation e Q p ∈ Subgroup.closure (cocharacterRadicalPoints A) := by
  let c := realEvaluation e Q
  have he : c '' cocharacterRadicalPoints (realGroupModel e Q) = cocharacterRadicalPoints A := by
    ext g
    obtain ⟨x, rfl⟩ := c.surjective g
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (realEvaluation_contractingPoints e Q x).mp (c.injective hyx ▸ hy)
    · intro hx
      exact ⟨x, (realEvaluation_contractingPoints e Q x).mpr hx, rfl⟩
  have h := MonoidHom.map_closure c.toMonoidHom (cocharacterRadicalPoints (realGroupModel e Q))
  change _ = Subgroup.closure (Set.image c (cocharacterRadicalPoints (realGroupModel e Q))) at h
  rw [he] at h
  change _ ↔ c p ∈ Subgroup.closure (cocharacterRadicalPoints A)
  rw [← h]
  constructor
  · intro hp
    exact ⟨p, hp, rfl⟩
  · rintro ⟨x, hx, hxp⟩
    exact c.injective hxp ▸ hx

end ContractingRadicalTransport

open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.GeometricRadicals (IsReductive IsSemisimple GeometricGroup)

section ExtensionComparison

variable {E : Type u} [Field E] [Algebra F E] {L : Type} [Field L] [Algebra ℝ L]
variable (e : F ≃+* ℝ) (b : E ≃+* L)

private def restrictLiftedIso
    (h : ∀ x : F, b (algebraMap F E x) = algebraMap ℝ L (e x)) (R : TestAlgebra L) :
    (restrictTestAlgebra F E).obj (liftedTest b R) ≅
      realTestOver e ((restrictTestAlgebra ℝ L).obj R) := by
  let A := (restrictTestAlgebra F E).obj (liftedTest b R)
  let B := realTestOver e ((restrictTestAlgebra ℝ L).obj R)
  have hc (x : F) : @algebraMap F A _ _ A.algebra x = @algebraMap F B _ _ B.algebra x := by
    change ULift.up (algebraMap L R (b (algebraMap F E x))) =
      ULift.up (algebraMap L R (algebraMap ℝ L (e x)))
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
    (h : ∀ x : F, b (algebraMap F E x) = algebraMap ℝ L (e x))
    {R S : TestAlgebra L} (a : R ⟶ S) :
    (restrictLiftedIso e b h R).inv ≫ (restrictTestAlgebra F E).map (liftedMap b a) =
      realTestMap e ((restrictTestAlgebra ℝ L).map a) ≫ (restrictLiftedIso e b h S).inv := by
  let A := realTestOver e ((restrictTestAlgebra ℝ L).obj R)
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

variable {G : GroupScheme F} {H : GroupScheme ℝ}
  (compare : ∀ R : TestAlgebra ℝ, GroupPoints H R ≃* GroupPoints G (realTestOver e R))

private def extensionPointComparison
    (h : ∀ x : F, b (algebraMap F E x) = algebraMap ℝ L (e x)) (R : TestAlgebra L) :
    GroupPoints ((groupBaseChange ℝ L).obj H) R ≃*
      GroupPoints ((groupBaseChange F E).obj G) (liftedTest b R) :=
  (baseChangePointGroupEquiv L H R).trans <|
    (compare ((restrictTestAlgebra ℝ L).obj R)).trans <|
    ((((groupPointsFunctor F).obj G).mapIso (restrictLiftedIso e b h R).symm).groupIsoToMulEquiv).trans
      (baseChangePointGroupEquiv E G (liftedTest b R)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPointComparison_naturality
    (h : ∀ x : F, b (algebraMap F E x) = algebraMap ℝ L (e x))
    (hnat : ∀ {R S : TestAlgebra ℝ} (a : R ⟶ S) (p : GroupPoints H R),
      compare S (((groupPointsFunctor ℝ).obj H).map a p) =
        ((groupPointsFunctor F).obj G).map (realTestMap e a) (compare R p))
    {R S : TestAlgebra L} (a : R ⟶ S) (p : GroupPoints ((groupBaseChange ℝ L).obj H) R) :
    extensionPointComparison e b compare h S
        (((groupPointsFunctor L).obj ((groupBaseChange ℝ L).obj H)).map a p) =
      ((groupPointsFunctor E).obj ((groupBaseChange F E).obj G)).map (liftedMap b a)
        (extensionPointComparison e b compare h R p) := by
  apply (baseChangePointGroupEquiv E G (liftedTest b S)).injective
  rw [baseChangePointGroupEquiv_map]
  let U := (groupPointsFunctor F).obj G
  let R' := (restrictTestAlgebra ℝ L).obj R
  let S' := (restrictTestAlgebra ℝ L).obj S
  let a' := (restrictTestAlgebra ℝ L).map a
  let p' : GroupPoints H R' := baseChangePointGroupEquiv L H R p
  let iR := (restrictLiftedIso e b h R).inv
  let iS := (restrictLiftedIso e b h S).inv
  change (baseChangePointGroupEquiv E G (liftedTest b S))
      ((baseChangePointGroupEquiv E G (liftedTest b S)).symm
        (U.map iS (compare S' (baseChangePointGroupEquiv L H S
          (((groupPointsFunctor L).obj ((groupBaseChange ℝ L).obj H)).map a p))))) =
    U.map ((restrictTestAlgebra F E).map (liftedMap b a))
      ((baseChangePointGroupEquiv E G (liftedTest b R))
        ((baseChangePointGroupEquiv E G (liftedTest b R)).symm (U.map iR (compare R' p'))))
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    baseChangePointGroupEquiv_map, hnat]
  have hc := congrArg (fun f => U.map f (compare R' p')) (restrictLiftedIso_naturality e b h a)
  simpa only [Functor.map_comp, GrpCat.comp_apply] using hc.symm

end ExtensionComparison

section GeometricComparison

open Specs.GeometricRadicals (GeometricGroup)

private abbrev closureEquiv (e : F ≃+* ℝ) :
    AlgebraicClosure F ≃+* AlgebraicClosure ℝ :=
  IsAlgClosure.equivOfEquiv (AlgebraicClosure F) (AlgebraicClosure ℝ) e

/-- The natural point comparison extends to the actual geometric groups
using the algebraic closure equivalence induced by the base field equivalence. -/
private theorem geometricPointComparison
    (e : F ≃+* ℝ) (G : AffineAlgebraicGroup F) (H : AffineAlgebraicGroup ℝ)
    (compare : ∀ R : TestAlgebra ℝ, GroupPoints H.val R ≃* GroupPoints G.val (realTestOver e R))
    (hnat : ∀ {R S : TestAlgebra ℝ} (a : R ⟶ S) (p : GroupPoints H.val R),
      compare S (((groupPointsFunctor ℝ).obj H.val).map a p) =
        ((groupPointsFunctor F).obj G.val).map (realTestMap e a) (compare R p)) :
    ∃ q : ∀ R : TestAlgebra (AlgebraicClosure ℝ), GroupPoints (GeometricGroup H).val R ≃*
        GroupPoints (GeometricGroup G).val (liftedTest (closureEquiv e) R),
      ∀ {R S : TestAlgebra (AlgebraicClosure ℝ)} (a : R ⟶ S)
        (p : GroupPoints (GeometricGroup H).val R),
        q S (((groupPointsFunctor (AlgebraicClosure ℝ)).obj (GeometricGroup H).val).map a p) =
          ((groupPointsFunctor (AlgebraicClosure F)).obj (GeometricGroup G).val).map
            (liftedMap (closureEquiv e) a) (q R p) := by
  have hc := IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure F) (AlgebraicClosure ℝ) e
  exact ⟨extensionPointComparison e (closureEquiv e) compare hc,
    extensionPointComparison_naturality e (closureEquiv e) compare hc hnat⟩

end GeometricComparison

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

set_option maxRecDepth 4000 in
/-- Compare the coordinate algebras of affine schemes from their natural
point comparison on lifted test algebras. -/
private def coordinatesIsoOfPointComparison
    (q : ∀ R : TestAlgebra k₀, Points X R ≃ Points Y (liftedTest e R))
    (hnat : ∀ {R S : TestAlgebra k₀} (a : R ⟶ S) (p : Points X R),
      q S (mapPoints a p) = mapPoints (liftedMap e a) (q R p)) :
    transportedCoordinates e Q ≅ P.coordinates := by
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
  refine ⟨f, g, ?_, ?_⟩
  · have h := (hd (𝟙 A) g).symm
    rw [Category.id_comp] at h
    exact h.trans hg
  · apply (d A).injective
    rw [hd, hg, Category.id_comp]

include P Q in
private theorem connectedSpace_of_liftedPointComparison
    (q : ∀ R : TestAlgebra k₀, Points X R ≃ Points Y (liftedTest e R))
    (hnat : ∀ {R S : TestAlgebra k₀} (a : R ⟶ S) (p : Points X R),
      q S (mapPoints a p) = mapPoints (liftedMap e a) (q R p))
    (hY : ConnectedSpace Y.left) : ConnectedSpace X.left := by
  let i := coordinatesIsoOfPointComparison e P Q q hnat
  let d : Q.coordinates ≃+* P.coordinates :=
    (smallerAlgebraEquiv e Q.coordinates Q.finiteType).trans
      (CommAlgCat.algEquivOfIso i).toRingEquiv
  have hQ : IsIso Q.iso.hom.left := inferInstance
  have hP : IsIso P.iso.hom.left := inferInstance
  have hY' : ConnectedSpace (PrimeSpectrum Q.coordinates) :=
    Q.iso.hom.left.homeomorph.connectedSpace_iff.mpr hY
  have hX' : ConnectedSpace (PrimeSpectrum P.coordinates) :=
    (PrimeSpectrum.homeomorphOfRingEquiv d).connectedSpace_iff.mp hY'
  exact P.iso.hom.left.homeomorph.connectedSpace_iff.mp hX'

end ComparingCoordinateRings

section GeometricConnectedness

open Specs.GeometricRadicals (GeometricGroup)
open private connected_baseChange_iff from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected from LinearAlgebraicGroups.Solvable.WordDomainGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem geometricallyConnected_of_pointComparison
    (e : F ≃+* ℝ) (G : AffineAlgebraicGroup F) (H : AffineAlgebraicGroup ℝ)
    (compare : ∀ R : TestAlgebra ℝ, GroupPoints H.val R ≃* GroupPoints G.val (realTestOver e R))
    (hnat : ∀ {R S : TestAlgebra ℝ} (a : R ⟶ S) (p : GroupPoints H.val R),
      compare S (((groupPointsFunctor ℝ).obj H.val).map a p) =
        ((groupPointsFunctor F).obj G.val).map (realTestMap e a) (compare R p))
    (hG : GeometricallyConnected G.val.X.hom) : GeometricallyConnected H.val.X.hom := by
  let A := GeometricGroup G
  let B := GeometricGroup H
  obtain ⟨q, hq⟩ := geometricPointComparison e G H compare hnat
  have hA : ConnectedSpace A.val.X.left :=
    hG.geometrically_connectedSpace _ _ _
      (CategoryTheory.IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap F (AlgebraicClosure F)))
  let P := affinePresentation B.val.X B.property.1 B.property.2.1
  let Q := affinePresentation A.val.X A.property.1 A.property.2.1
  have hB : ConnectedSpace B.val.X.left :=
    connectedSpace_of_liftedPointComparison (closureEquiv e) P Q (fun R => (q R).toEquiv) hq hA
  letI : ConnectedSpace H.val.X.left := (connected_baseChange_iff (K := AlgebraicClosure ℝ) H).mp hB
  exact geometricallyConnected_of_connected H

end GeometricConnectedness

section Nontriviality

open CategoryTheory.Limits
open Specs.GeometricRadicals (GeometricGroup)
open private trivial_baseChange_iff from LinearAlgebraicGroups.Reductive.RadicalBaseChange

private theorem isZero_afterFieldExtension_iff {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : GroupScheme k) : IsZero ((groupBaseChange k K).obj G) ↔ IsZero G := by
  have ht (L : Type u) [Field L] (H : GroupScheme L) :
      IsZero H ↔ Nonempty (H ≅ Grp.trivial (SchemeOver L)) :=
    ⟨fun h => ⟨h.iso (Grp.isZero_trivial _)⟩,
      fun ⟨j⟩ => (Grp.isZero_trivial _).of_iso j⟩
  exact (ht K _).trans ((trivial_baseChange_iff G).trans (ht k _).symm)

private theorem isZero_geometricFieldExtension_iff
    {k K : Type u} [Field k] [Field K] [Algebra k K] (G : AffineAlgebraicGroup k) :
    IsZero (GeometricGroup (baseChangedAlgebraicGroup K G)).val ↔ IsZero (GeometricGroup G).val :=
  (isZero_afterFieldExtension_iff (K := AlgebraicClosure K) (baseChangedAlgebraicGroup K G).val).trans
    ((isZero_afterFieldExtension_iff (K := K) G.val).trans
      (isZero_afterFieldExtension_iff (K := AlgebraicClosure k) G.val).symm)

private theorem isZero_of_subsingleton_liftedPoints (e : F ≃+* k₀) (G : AffineAlgebraicGroup F)
    (hs : ∀ R : TestAlgebra k₀, Subsingleton (GroupPoints G.val (liftedTest e R))) :
    IsZero G.val := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Grp.hom_ext
  let P := affinePresentation G.val.X G.property.1 G.property.2.1
  apply hom_ext_of_liftedPoints e P
  intro R p
  exact (hs R).elim _ _

private theorem subsingleton_points_of_isZero (G : GroupScheme k₀) (hG : IsZero G)
    (R : TestAlgebra k₀) : Subsingleton (GroupPoints G R) := by
  let e := (Grp.forget _).mapIso (hG.iso (Grp.isZero_trivial _))
  refine ⟨fun p q => (cancel_mono e.hom).mp ?_⟩
  change p ≫ e.hom = q ≫ e.hom
  exact toUnit_unique _ _

private theorem nonzeroGeometricGroup_of_pointComparison
    (e : F ≃+* ℝ) (G : AffineAlgebraicGroup F) (H : AffineAlgebraicGroup ℝ)
    (compare : ∀ R : TestAlgebra ℝ, GroupPoints H.val R ≃* GroupPoints G.val (realTestOver e R))
    (hnat : ∀ {R S : TestAlgebra ℝ} (a : R ⟶ S) (p : GroupPoints H.val R),
      compare S (((groupPointsFunctor ℝ).obj H.val).map a p) =
        ((groupPointsFunctor F).obj G.val).map (realTestMap e a) (compare R p))
    (hG : ¬ IsZero (GeometricGroup G).val) : ¬ IsZero (GeometricGroup H).val := by
  intro h
  apply hG
  obtain ⟨q, _⟩ := geometricPointComparison e G H compare hnat
  apply isZero_of_subsingleton_liftedPoints (closureEquiv e) (GeometricGroup G)
  intro R
  have hR := subsingleton_points_of_isZero (GeometricGroup H).val h R
  exact ⟨fun x y => (q R).symm.injective (hR.elim _ _)⟩

end Nontriviality

open NumberField.InfinitePlace.Completion
open CategoryTheory.Limits (IsZero)
open Specs.AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open LieAlgebrasAndRepresentations (FiniteDynkinType)
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies

private theorem castMatrixEntry {m n : ℕ} (h : m = n)
    (x : Matrix.GeneralLinearGroup (Index.{u} m) F) (a b : Fin m) :
    (cast (congrArg (fun s => Matrix.GeneralLinearGroup (Index.{u} s) F) h) x)
        (ULift.up (Fin.cast h a)) (ULift.up (Fin.cast h b)) =
      x (ULift.up a) (ULift.up b) := by
  cases h
  rfl

/-- Transport of the affine real model, point functor, matrix topology and
contracting subgroups. It also carries geometric connectedness and
nontriviality of the geometric group. The parabolic comparison applies
when the real model is reductive and the original group is semisimple. -/
theorem realCompletionPointComparison {K : Type u} [Field K] [NumberField K]
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (w : NumberField.InfinitePlace K) (hw : w.IsReal) :
    let F := w.Completion
    let e := ringEquivRealOfIsReal hw
    let Gv := baseChangedAlgebraicGroup F G
    ∃ (H : AffineAlgebraicGroup ℝ) (j : MatrixRealization H)
      (compare : ∀ R : TestAlgebra ℝ, GroupPoints H.val R ≃* GroupPoints Gv.val (realTestOver e R))
      (q : PointsIn j ℝ ≃ₜ* PointsIn i F) (hs : j.size = i.size),
      Smooth H.val.X.hom ∧
      (GeometricallyConnected G.val.X.hom → GeometricallyConnected H.val.X.hom) ∧
      (¬ IsZero (GeometricGroup G).val → ¬ IsZero (GeometricGroup H).val) ∧
      (∀ {R S : TestAlgebra ℝ} (f : R ⟶ S) (p : GroupPoints H.val R),
        compare S (((groupPointsFunctor ℝ).obj H.val).map f p) =
          ((groupPointsFunctor F).obj Gv.val).map (realTestMap e f) (compare R p)) ∧
      (∀ p : PointsIn j ℝ,
        (show Points G.val.X (CommAlgCat.of K F) from q p).left =
          (baseChangePoint K F G.val.X (CommAlgCat.of F F)
            (((groupPointsFunctor F).obj Gv.val).map (completionTestMap e) (compare realTest p))).left) ∧
      (∀ (p : PointsIn j ℝ) (a b : Fin j.size),
        asMatrix j ℝ p (ULift.up a) (ULift.up b) =
          e (asMatrix i F (q p) (ULift.up (Fin.cast hs a)) (ULift.up (Fin.cast hs b)))) ∧
      (let ε := ((groupPointsFunctor F).obj Gv.val).map (completionTestMap e)
       ∀ p : GroupPoints H.val realTest,
         (p ∈ Subgroup.closure (cocharacterRadicalPoints H) ↔
           ε (compare realTest p) ∈ Subgroup.closure (cocharacterRadicalPoints Gv)) ∧
         (IsReductive H → IsSemisimple G →
           (p ∈ Subgroup.closure (parabolicRadicalPoints H) ↔
             ε (compare realTest p) ∈ Subgroup.closure (parabolicRadicalPoints Gv)))) := by
  let F := w.Completion
  let e := ringEquivRealOfIsReal hw
  let Gv := baseChangedAlgebraicGroup F G
  obtain ⟨h, iF, hsize, qF, hqF, hmF⟩ :=
    ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  change MatrixRealization Gv at iF
  let P := affinePresentation Gv.val.X Gv.property.1 Gv.property.2.1
  let Q := affinePresentation iF.ambient.val.X iF.ambient.property.1 iF.ambient.property.2.1
  let H := realGroupModel e P
  let j := realMatrixRealization e iF P Q
  let compare := realGroupPoints e P
  have he : Continuous e := (isometryEquivRealOfIsReal hw).continuous
  have hs : Continuous e.symm := (isometryEquivRealOfIsReal hw).symm.continuous
  let qv := realEvaluationHomeomorph e iF P Q he hs
  let q := qv.trans qF
  have hsize' : j.size = i.size := hsize
  have hnat {R S : TestAlgebra ℝ} (f : R ⟶ S) (p : GroupPoints H.val R) :
      compare S (((groupPointsFunctor ℝ).obj H.val).map f p) =
        ((groupPointsFunctor F).obj Gv.val).map (realTestMap e f) (compare R p) :=
    realGroupPoints_naturality e P f p
  refine ⟨H, j, compare, q, hsize', characteristicZeroSmoothness ℝ H, ?_, ?_, hnat, ?_, ?_, ?_⟩
  · intro hG
    have hGv : GeometricallyConnected Gv.val.X.hom :=
      MorphismProperty.of_isPullback (P := @GeometricallyConnected)
        (CategoryTheory.IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap K F)) hG
    exact geometricallyConnected_of_pointComparison e Gv H compare hnat hGv
  · intro hG
    have hGv := fun hzero => hG ((isZero_geometricFieldExtension_iff (K := F) G).mp hzero)
    exact nonzeroGeometricGroup_of_pointComparison e Gv H compare hnat hGv
  · intro p
    change (show Points G.val.X (CommAlgCat.of K F) from qF (realEvaluation e P p)).left = _
    exact (hqF (realEvaluation e P p)).trans
      (congrArg (fun x : GroupPoints Gv.val (CommAlgCat.of F F) =>
        (baseChangePoint K F G.val.X (CommAlgCat.of F F) x).left)
        (realEvaluation_apply e P p))
  · intro p a b
    have hsmall := realMatrixRealization_entries e iF P Q p
    have hb := hmF (qv p)
    change asMatrix j ℝ p (ULift.up a) (ULift.up b) =
      e (asMatrix i F (qF (qv p)) (ULift.up (Fin.cast hsize a)) (ULift.up (Fin.cast hsize b)))
    calc
      _ = e (asMatrix iF F (qv p) (ULift.up a) (ULift.up b)) :=
        congrArg (fun x : Matrix.GeneralLinearGroup (Index.{0} j.size) ℝ =>
          x (ULift.up a) (ULift.up b)) hsmall
      _ = _ := by
        rw [← hb]
        exact congrArg e (castMatrixEntry hsize (asMatrix iF F (qv p)) a b).symm

  · intro ev p
    have hr := realEvaluation_contractingClosure e P p
    rw [realEvaluation_apply e P p] at hr
    refine ⟨hr, ?_⟩
    intro hH hG
    have hGv : IsSemisimple Gv :=
      (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F) G hG.1 hG.2.1).mpr hG
    rw [parabolicRadicalPoints_eq_cocharacterRadicalPoints H j hH,
      parabolicRadicalPoints_eq_cocharacterRadicalPoints Gv iF (reductive_of_semisimple Gv hGv)]
    exact hr

section GeometricScalarExtension

open private groupBaseChangeTower from LinearAlgebraicGroups.Reductive.RadicalBaseChange

/-- The geometric group of a scalar extension identifies with the scalar
extension of the original geometric group to the common algebraically
closed field. -/
theorem geometricScalarExtensionIso {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) :
    ∃ a : Algebra (AlgebraicClosure k) (AlgebraicClosure K),
      letI := a
      IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K) ∧
        Nonempty ((baseChangedAlgebraicGroup (AlgebraicClosure K) (GeometricGroup G)).val ≅
          (GeometricGroup (baseChangedAlgebraicGroup K G)).val) := by
  let E := AlgebraicClosure k
  let L := AlgebraicClosure K
  let f : E →ₐ[k] L := IsAlgClosed.lift
  let a : Algebra E L := f.toRingHom.toAlgebra
  letI := a
  have h : IsScalarTower k E L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      exact (f.commutes x).symm)
  letI := h
  exact ⟨a, h, ⟨((groupBaseChangeTower (K := E) L).app G.val).symm ≪≫
    (groupBaseChangeTower (K := K) L).app G.val⟩⟩

end GeometricScalarExtension

/-- Assemble the original bridge from the two geometric transport
statements and the point comparison for the actual real place. -/
theorem realCompletionTransport_of_geometricTransport
    (extendGeometry :
      ∀ {K : Type u} [Field K] [NumberField K] (G : AffineAlgebraicGroup K)
        (w : NumberField.InfinitePlace K), w.IsReal →
        ∀ t : FiniteDynkinType, (t = .E6 ∨ t = .E7 ∨ t = .E8) →
          IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasAbsoluteType G t →
          let Gv := baseChangedAlgebraicGroup w.Completion G
          IsAbsolutelyAlmostSimple Gv ∧ GeometricallySimplyConnected Gv ∧ HasAbsoluteType Gv t)
    (transportGeometry :
      ∀ {F : Type u} [Field F] (e : F ≃+* ℝ) (G : AffineAlgebraicGroup F)
        (H : AffineAlgebraicGroup ℝ)
        (compare : ∀ R : TestAlgebra ℝ, GroupPoints H.val R ≃* GroupPoints G.val (realTestOver e R)),
        (∀ {R S : TestAlgebra ℝ} (a : R ⟶ S) (p : GroupPoints H.val R),
          compare S (((groupPointsFunctor ℝ).obj H.val).map a p) =
            ((groupPointsFunctor F).obj G.val).map (realTestMap e a) (compare R p)) →
        ∀ t : FiniteDynkinType, (t = .E6 ∨ t = .E7 ∨ t = .E8) →
          IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasAbsoluteType G t →
          IsAbsolutelyAlmostSimple H ∧ GeometricallySimplyConnected H ∧ HasAbsoluteType H t) :
    RealCompletionTransport.{u} := by
  intro K _ _ G i hG hsc t ht htype w hw
  let Gv := baseChangedAlgebraicGroup w.Completion G
  obtain ⟨hGv, hscv, htypev⟩ := extendGeometry G w hw t ht hG hsc htype
  obtain ⟨H, j, c, q, hs, _, _, _, hnat, hpoints, hmatrix, hradicals⟩ :=
    realCompletionPointComparison G i w hw
  obtain ⟨hH, hscH, htH⟩ :=
    transportGeometry (ringEquivRealOfIsReal hw) Gv H c hnat t ht hGv hscv htypev
  refine ⟨H, j, c, q, hs, hH, hscH, htH, hnat, hpoints, hmatrix, ?_⟩
  dsimp only
  intro p
  exact ⟨(hradicals p).2 (reductive_of_semisimple H hH.1) hG.1, (hradicals p).1⟩

/-- Transport the geometric hypotheses, the matrix topology, and both radical
subgroups at the actual real completion. -/
theorem realCompletionTransport : RealCompletionTransport.{u} := by
  apply realCompletionTransport_of_geometricTransport
  · exact ExceptionalCompletionGeometry.realCompletionGeometricExtension.{u}
  · intro F _ e G H compare hnat t ht hG hsc htype
    exact ExceptionalRealModelGeometry.realModelGeometry e G H compare hnat hG hsc t ht htype

end LinearAlgebraicGroups.Arithmetic.ExceptionalRealCompletionTransport
