import Specs.LinearAlgebraicGroups.Descent.ExactLifting
import LinearAlgebraicGroups.Flag.TorsorObstruction
import LinearAlgebraicGroups.Descent.SmoothTorsors
import LinearAlgebraicGroups.Descent.Lang
import LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Etale.StandardEtale
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Descent.ExactLifting

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme projectSection)
open Specs.Fppf Specs.TorsorObstruction Specs.SmoothTorsors Specs.ExactLifting
open NonabelianCohomology
open LinearAlgebraicGroups.TorsorObstruction (fibreTorsor)

open private schemeExtensionUniversal from LinearAlgebraicGroups.Flag.TorsorObstruction

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev affineSubgroup {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (H : ClosedSubgroup G.val) : AffineAlgebraicGroup k := by
  letI : IsAffine G.val.X.left := G.property.1
  letI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  letI : QuasiCompact G.val.X.hom := G.property.2.2
  letI : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  have h : H.inclusion.hom.hom.left ≫ G.val.X.hom = H.group.X.hom :=
    Over.w H.inclusion.hom.hom
  refine ⟨H.group, isAffine_of_isAffineHom H.inclusion.hom.hom.left, ?_, ?_⟩
  · rw [← h]
    infer_instance
  · rw [← h]
    infer_instance

private theorem projectRange {k : Type u} [Field k] {G : GroupScheme k}
    (H : ClosedSubgroup G) :
    Set.range (fun g : fieldBase k ⟶ G.X ↦ projectSection H g) =
      Set.range (rationalCosetMap H) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk g, rfl⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨g, rfl⟩ := Quotient.mk_surjective c
    exact ⟨g, rfl⟩

private theorem fibreCocycle_formula {k S : Type u} [Field k] [Field S] [Algebra k S]
    {G : GroupScheme k} (H : ClosedSubgroup G) {x : RationalPoints H}
    {p : FibreSection H x (fieldExtensionTest k S)} {a : GaloisCocycle (S := S) H.group}
    (ha : IsCocycleOf (fibreTorsor H x) p a) (σ : S ≃ₐ[k] S) :
    let g : NonabelianCohomology.Points k S G.X := p.val.down
    a σ ≫ H.inclusion.hom.hom = g⁻¹ * pointAction k S G.X σ g := by
  let g : NonabelianCohomology.Points k S G.X := p.val.down
  have h : pointAction k S G.X σ g = g * (a σ ≫ H.inclusion.hom.hom) :=
    congrArg (fun q : FibreSection H x (fieldExtensionTest k S) ↦ q.val.down) (ha σ)
  change a σ ≫ H.inclusion.hom.hom = g⁻¹ * pointAction k S G.X σ g
  rw [h, inv_mul_cancel_left]

/-- Passing the fppf exact sequence through the smooth-torsor classification
identifies the last map with postcomposition of cocycles. -/
theorem galoisExactness : GaloisExactness.{u} := by
  intro k S _ _ _ _ G H hG hH
  let A := affineSubgroup G H
  obtain ⟨cH, hnH, hclassH⟩ := SmoothTorsors.classification (S := S) A hH
  obtain ⟨cG, hnG, hclassG⟩ := SmoothTorsors.classification (S := S) G hG
  obtain ⟨d, e, hd, he, _, hdn, hen, hr₁, hr₂, horbit⟩ :=
    LinearAlgebraicGroups.TorsorObstruction.pointedExactness H
  have hD (x : RationalPoints H) : d x = Quotient.mk _ (fibreTorsor H x) := by
    obtain ⟨t, ht⟩ := hd x
    exact ht
  let δ : RationalPoints H → groupH1 k H.group.X S := cH ∘ d
  let E : groupH1 k H.group.X S → groupH1 k G.val.X S := fun a ↦ cG (e (cH.symm a))
  have hc (t : H1fppf k H.group) : E (cH t) = cG (e t) := by simp [E]
  refine ⟨δ, E, cH, ?_, fun x ↦ ⟨d x, hd x, rfl⟩,
    fun P p a ha ↦ (hclassH P).2.2 p a ha, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨t, ht⟩ := cH.surjective (galoisClass a)
    obtain ⟨P, rfl⟩ := Quotient.mk_surjective t
    obtain ⟨p, b, hb⟩ := (hclassH P).2.1
    have hbclass : galoisClass b = galoisClass a := ((hclassH P).2.2 p b hb).symm.trans ht
    let Q := Fppf.extendStructureGroup H.inclusion P
    have hQ := Fppf.extendStructureGroup_spec H.inclusion P
    obtain ⟨f, hf⟩ := (schemeExtensionUniversal H hQ).1
    have hfb : IsCocycleOf Q (f.app _ p) (mapCocycle H.inclusion b) := by
      intro σ
      change Q.val.sheaf.obj.map (fieldExtensionAut k S σ).op (f.app _ p) = _
      rw [← f.naturality_apply]
      change f.app _ (P.val.res (fieldExtensionAut k S σ) p) = _
      rw [hb σ]
      exact hf p ⟨b σ⟩
    have heq : e (Quotient.mk _ P) = Quotient.mk _ Q := he P Q hQ
    calc
      E (galoisClass a) = cG (e (Quotient.mk _ P)) := (congrArg E ht).symm.trans (hc _)
      _ = cG (Quotient.mk _ Q) := congrArg cG heq
      _ = galoisClass (mapCocycle H.inclusion b) := (hclassG Q).2.2 _ _ hfb
      _ = _ := ?_
    apply Quotient.sound
    obtain ⟨z, hz⟩ := Quotient.exact hbclass
    refine ⟨z ≫ H.inclusion.hom.hom, ?_⟩
    intro σ
    change a σ ≫ H.inclusion.hom.hom =
      (z ≫ H.inclusion.hom.hom)⁻¹ * (b σ ≫ H.inclusion.hom.hom) *
        pointAction k S G.val.X σ (z ≫ H.inclusion.hom.hom)
    rw [show a σ = _ from hz σ, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    rw [show pointAction k S H.group.X σ z ≫ H.inclusion.hom.hom =
      pointAction k S G.val.X σ (z ≫ H.inclusion.hom.hom) from Category.assoc _ _ _]
  · exact (congrArg cH hdn).trans (hnH (fieldGroupSectionsAreSheaf H.group))
  · calc
      E (groupBasepoint k H.group.X S) = E (cH (fieldNeutralClass H.group)) :=
        congrArg E (hnH (fieldGroupSectionsAreSheaf H.group)).symm
      _ = cG (e (fieldNeutralClass H.group)) := hc _
      _ = groupBasepoint k G.val.X S := (congrArg cG hen).trans (hnG _)
  · rw [projectRange H, hr₁]
    ext x
    change d x = fieldNeutralClass H.group ↔ cH (d x) = groupBasepoint k H.group.X S
    rw [← hnH (fieldGroupSectionsAreSheaf H.group)]
    exact cH.injective.eq_iff.symm
  · ext a
    obtain ⟨t, rfl⟩ := cH.surjective a
    change (∃ x, cH (d x) = cH t) ↔ E (cH t) = groupBasepoint k G.val.X S
    rw [hc, ← hnG (fieldGroupSectionsAreSheaf G.val)]
    simp only [Equiv.apply_eq_iff_eq]
    exact Set.ext_iff.mp hr₂ t
  · intro x y
    exact cH.injective.eq_iff.trans (horbit x y)
  · intro x
    let P := fibreTorsor H x
    refine ⟨SmoothTorsors.geometricPoint (S := S) A P hH, ?_⟩
    intro p
    let p' : P.val.Section (fieldExtensionTest k S) := p
    obtain ⟨a, ha⟩ := SmoothTorsors.pointCocycle A P p'
    exact ⟨a, (congrArg cH (hD x)).trans ((hclassH P).2.2 p' a ha),
      fun σ ↦ fibreCocycle_formula H (p := p) ha σ⟩

/-- The fibre is a torsor under a connected group, so Lang makes its class neutral. -/
theorem finiteFieldLifting : FiniteFieldLifting.{u} := by
  intro k _ _ G H _ _ hconn x
  let A := affineSubgroup G H
  let : LocallyOfFiniteType H.group.X.hom := A.property.2.1
  let : QuasiCompact H.group.X.hom := A.property.2.2
  let := hconn
  obtain ⟨d, _, hd, _, _, _, _, hr, _, _⟩ :=
    LinearAlgebraicGroups.TorsorObstruction.pointedExactness H
  obtain ⟨hp, hdx⟩ := hd x
  have h : d x = fieldNeutralClass H.group :=
    hdx.trans (langFppfTorsor k H.group (fieldGroupSectionsAreSheaf H.group)
      ⟨quotientFibreAction H x, hp⟩)
  have hx : x ∈ Set.range (rationalCosetMap H) := by
    rw [hr]
    exact h
  rw [← projectRange H] at hx
  exact hx

section Squares

open CategoryTheory.Limits Polynomial LaurentPolynomial
open LinearAlgebraicGroups.Specs (rightCosetPresheaf rightQuotientSheaf schemeFppfSheaf fppfOver)
open StandardGroups (multiplicativeGroup multiplicativeGroupPointsIso)

open private laurentEvaluation laurentEvaluation_T
  from LinearAlgebraicGroups.Affine.StandardGroups
open private unityGroup unityGroupPoints unityGroupPoints_coord rootCoordinate_natural
  from LinearAlgebraicGroups.Descent.SmoothTorsors

variable {k : Type u} [Field k]

private abbrev gm (k : Type u) [Field k] := (multiplicativeGroup k).val
private abbrev laurent (k : Type u) [Field k] := LaurentPolynomial k
private abbrev affineTest (k : Type u) [Field k] (R : Type u) [CommRing R] [Algebra k R] :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k R))
private abbrev affineMap {R B : Type u} [CommRing R] [CommRing B] [Algebra k R] [Algebra k B]
    (f : R →ₐ[k] B) : affineTest k B ⟶ affineTest k R :=
  (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op

private abbrev gammaAdj (k : Type u) [Field k] := algΓAlgSpecAdjunction (CommRingCat.of k)

private def affineCoord (R : CommAlgCat.{u} k) :
    ((algSpec (CommRingCat.of k)).obj (op R) ⟶ (gm k).X) ≃* Rˣ :=
  Iso.groupIsoToMulEquiv ((multiplicativeGroupPointsIso k).app R)

private theorem affineCoord_natural {R B : CommAlgCat.{u} k}
    (f : R ⟶ B) (g : (algSpec (CommRingCat.of k)).obj (op R) ⟶ (gm k).X) :
    affineCoord B ((algSpec (CommRingCat.of k)).map f.op ≫ g) =
      Units.map f.hom.toMonoidHom (affineCoord R g) := by
  have h := congrArg (fun j ↦ j g) ((multiplicativeGroupPointsIso k).hom.naturality f)
  exact h

private theorem affineCoord_map {R : Type u} [CommRing R] [Algebra k R]
    (f : laurent k →ₐ[k] R) :
    (affineCoord (CommAlgCat.of k R) (affineMap f) : R) = f (LaurentPolynomial.T 1) := by
  let := StandardGroups.multiplicativeHopf k
  let e := (hopfSpecPointIso (CommHopfAlgCat.of k (laurent k))).app (CommAlgCat.of k R)
  have hm : e.hom (WithConv.toConv f) = affineMap f := by
    apply Over.OverMorphism.ext
    rfl
  let val (φ : WithConv (laurent k →ₐ[k] R)) : R :=
    φ.ofConv (LaurentPolynomial.isUnit_T (R := k) 1).unit.val
  have h : e.inv (e.hom (WithConv.toConv f)) = WithConv.toConv f :=
    e.hom_inv_id_apply _
  calc
    _ = (affineCoord (CommAlgCat.of k R) (e.hom (WithConv.toConv f))).val :=
      congrArg (fun g ↦ (affineCoord (CommAlgCat.of k R) g).val) hm.symm
    _ = val (e.inv (e.hom (WithConv.toConv f))) := rfl
    _ = f (LaurentPolynomial.T 1) :=
      (congrArg val h).trans (congrArg f (IsUnit.unit_spec _))

private def precomposeGamma (T : SchemeOver k) :
    ((algSpec (CommRingCat.of k)).obj ((algΓ (CommRingCat.of k)).obj T) ⟶ (gm k).X) ≃*
      (T ⟶ (gm k).X) := by
  letI R := CommRingCat.of k
  let A := op (CommAlgCat.of k (laurent k))
  let e := ((algSpec.fullyFaithful (R := R)).homEquiv
    (X := (algΓ R).obj T) (Y := A)).symm.trans ((gammaAdj k).homEquiv T A)
  have h (g : (algSpec R).obj ((algΓ R).obj T) ⟶ (gm k).X) :
      e g = (gammaAdj k).unit.app T ≫ g := by
    change (gammaAdj k).homEquiv T A (algSpec.fullyFaithful.preimage g) = _
    rw [Adjunction.homEquiv_unit, Functor.FullyFaithful.map_preimage]
  let f : ((algSpec R).obj ((algΓ R).obj T) ⟶ (gm k).X) →* (T ⟶ (gm k).X) :=
    { toFun := fun g ↦ (gammaAdj k).unit.app T ≫ g
      map_one' := MonObj.comp_one _
      map_mul' := MonObj.comp_mul _ }
  refine MulEquiv.ofBijective f ?_
  change Function.Bijective (fun g : (algSpec R).obj ((algΓ R).obj T) ⟶ (gm k).X ↦
    (gammaAdj k).unit.app T ≫ g)
  rw [← funext h]
  exact e.bijective

private def globalCoord (T : SchemeOver k) : (T ⟶ (gm k).X) ≃* (testFunctions T)ˣ :=
  (precomposeGamma T).symm.trans (affineCoord (((algΓ (CommRingCat.of k)).obj T).unop))

private theorem globalCoord_natural {T U : SchemeOver k} (f : U ⟶ T) (g : T ⟶ (gm k).X) :
    globalCoord U (f ≫ g) = restrictUnit f (globalCoord T g) := by
  have h : (precomposeGamma U).symm (f ≫ g) =
      (algSpec (CommRingCat.of k)).map ((algΓ (CommRingCat.of k)).map f) ≫
        (precomposeGamma T).symm g := by
    apply (precomposeGamma U).injective
    rw [MulEquiv.apply_symm_apply]
    change f ≫ g = (gammaAdj k).unit.app U ≫ _ ≫ (precomposeGamma T).symm g
    have hf := (gammaAdj k).unit.naturality f
    change f ≫ (gammaAdj k).unit.app T =
      (gammaAdj k).unit.app U ≫ (algSpec (CommRingCat.of k)).map ((algΓ (CommRingCat.of k)).map f) at hf
    rw [← Category.assoc, ← hf, Category.assoc]
    exact congrArg (f ≫ ·) ((precomposeGamma T).apply_symm_apply g).symm
  change affineCoord _ ((precomposeGamma U).symm (f ≫ g)) = _
  rw [h]
  exact affineCoord_natural ((algΓ (CommRingCat.of k)).map f).unop _

private def gammaSpecAlgEquiv (R : Type u) [CommRing R] [Algebra k R] :
    R ≃ₐ[k] testFunctions (affineTest k R) := by
  let f := ((gammaAdj k).counit.app (op (CommAlgCat.of k R))).unop
  letI : (algSpec (CommRingCat.of k)).Full :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).full
  letI : (algSpec (CommRingCat.of k)).Faithful :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).faithful
  haveI : IsIso ((gammaAdj k).counit.app (op (CommAlgCat.of k R))) :=
    Adjunction.instIsIsoAppCounitOfFullOfFaithful
      (R := algSpec (CommRingCat.of k)) (gammaAdj k) _
  haveI : IsIso f := by dsimp [f]; infer_instance
  exact AlgEquiv.ofBijective f.hom (ConcreteCategory.bijective_of_isIso f)

private theorem globalCoord_affine {R : Type u} [CommRing R] [Algebra k R]
    (g : affineTest k R ⟶ (gm k).X) :
    globalCoord (affineTest k R) g =
      Units.map (gammaSpecAlgEquiv R).toMonoidHom (affineCoord (CommAlgCat.of k R) g) := by
  have h : (precomposeGamma (affineTest k R)).symm g =
      (algSpec (CommRingCat.of k)).map
        ((gammaAdj k).counit.app (op (CommAlgCat.of k R))) ≫ g := by
    apply (precomposeGamma (affineTest k R)).injective
    rw [MulEquiv.apply_symm_apply]
    change g = (gammaAdj k).unit.app _ ≫ _ ≫ g
    have ht := (gammaAdj k).right_triangle_components (op (CommAlgCat.of k R))
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g) ht).trans (Category.id_comp g))).symm
  change affineCoord _ ((precomposeGamma (affineTest k R)).symm g) = _
  rw [h]
  exact affineCoord_natural ((gammaAdj k).counit.app (op (CommAlgCat.of k R))).unop g

private def squareMap (k : Type u) [Field k] : (gm k).X ⟶ (gm k).X :=
  (𝟙 (gm k).X) * (𝟙 (gm k).X)

private theorem squareMap_coord {T : SchemeOver k} (g : T ⟶ (gm k).X) :
    globalCoord T (g ≫ squareMap k) = (globalCoord T g) ^ 2 := by
  simp [squareMap, MonObj.comp_mul, pow_two]

private abbrev muTwo (k : Type u) [Field k] := unityGroup k 2

private def rootPointHom (T : SchemeOver k) :
    (T ⟶ (muTwo k).X) →* (T ⟶ (gm k).X) :=
  (globalCoord T).symm.toMonoidHom.comp ((rootsOfUnity 2 (testFunctions T)).subtype.comp
    (unityGroupPoints 2 T).toMonoidHom)

private theorem rootPointHom_coord {T : SchemeOver k} (x : T ⟶ (muTwo k).X) :
    globalCoord T (rootPointHom T x) = (unityGroupPoints 2 T x).val :=
  (globalCoord T).apply_symm_apply _

private def rootPointMap (k : Type u) [Field k] : yonedaGrp.obj (muTwo k) ⟶ yonedaGrp.obj (gm k) where
  app T := GrpCat.ofHom (rootPointHom T.unop)
  naturality T U g := by
    apply GrpCat.ext
    intro x
    change rootPointHom U.unop (g.unop ≫ x) = g.unop ≫ rootPointHom T.unop x
    apply (globalCoord U.unop).injective
    rw [globalCoord_natural, rootPointHom_coord, rootPointHom_coord]
    apply Units.ext
    change ((unityGroupPoints 2 U.unop (g.unop ≫ x)).val : testFunctions U.unop) =
      ((algΓ (CommRingCat.of k)).map g.unop).unop.hom
        ((unityGroupPoints 2 T.unop x).val : testFunctions T.unop)
    rw [unityGroupPoints_coord, unityGroupPoints_coord]
    exact rootCoordinate_natural g.unop x

private def rootInclusion (k : Type u) [Field k] : muTwo k ⟶ gm k :=
  yonedaGrpFullyFaithful.preimage (rootPointMap k)

private theorem rootInclusion_coord {T : SchemeOver k} (g : T ⟶ (muTwo k).X) :
    globalCoord T (g ≫ (rootInclusion k).hom.hom) = (unityGroupPoints 2 T g).val := by
  have h := congrArg (fun f : yonedaGrp.obj (muTwo k) ⟶ yonedaGrp.obj (gm k) ↦ f.app (op T) g)
    (yonedaGrpFullyFaithful.map_preimage (rootPointMap k))
  change g ≫ (rootInclusion k).hom.hom = rootPointHom T g at h
  rw [h, rootPointHom_coord]

private theorem rootInclusion_kernel {T : SchemeOver k} (g : T ⟶ (gm k).X) :
    (∃ h : T ⟶ (muTwo k).X, h ≫ (rootInclusion k).hom.hom = g) ↔
      (globalCoord T g) ^ 2 = 1 := by
  constructor
  · rintro ⟨h, rfl⟩
    rw [rootInclusion_coord]
    exact (unityGroupPoints 2 T h).property
  · intro h
    refine ⟨(unityGroupPoints 2 T).symm ⟨globalCoord T g, h⟩, ?_⟩
    apply (globalCoord T).injective
    rw [rootInclusion_coord, MulEquiv.apply_symm_apply]

private abbrev squarePolynomial {R : Type u} [CommRing R] (a : R) : R[X] :=
  X ^ 2 - Polynomial.C a

private theorem adjoinedRoot_sq {R : Type u} [CommRing R] (a : R) :
    AdjoinRoot.root (squarePolynomial a) ^ 2 =
      algebraMap R (AdjoinRoot (squarePolynomial a)) a := by
  have h := AdjoinRoot.aeval_eq (f := squarePolynomial a) (squarePolynomial a)
  rw [AdjoinRoot.mk_self] at h
  simpa [squarePolynomial, sub_eq_zero] using h

private def muTwoCoordinateMap (k : Type u) [Field k] :
    laurent k →ₐ[k] AdjoinRoot (squarePolynomial (1 : k)) :=
  laurentEvaluation (((isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
    (by rw [adjoinedRoot_sq, map_one]; exact isUnit_one)).unit)

private theorem muTwoCoordinateMap_T :
    muTwoCoordinateMap k (LaurentPolynomial.T 1) =
      AdjoinRoot.root (squarePolynomial (1 : k)) := by
  rw [muTwoCoordinateMap, laurentEvaluation_T, zpow_one, IsUnit.unit_spec]

private theorem rootInclusion_affine :
    (rootInclusion k).hom.hom = affineMap (muTwoCoordinateMap k) := by
  let B := AdjoinRoot (squarePolynomial (1 : k))
  apply (globalCoord (affineTest k B)).injective
  apply Units.ext
  have h := rootInclusion_coord (k := k) (𝟙 (muTwo k).X)
  rw [Category.id_comp] at h
  let D := op (CommAlgCat.of k B)
  have hroot : rootCoordinate (𝟙 (muTwo k).X) =
      (gammaSpecAlgEquiv (k := k) B).toAlgHom (AdjoinRoot.root (squarePolynomial (1 : k))) :=
    congrArg (fun z : (algΓ (CommRingCat.of k)).obj (affineTest k B) ⟶ D ↦
      z.unop.hom (AdjoinRoot.root (squarePolynomial (1 : k))))
      ((gammaAdj k).homEquiv_symm_id D)
  have hmap :=
    (affineCoord_map (muTwoCoordinateMap k)).trans (muTwoCoordinateMap_T (k := k))
  calc
    _ = rootCoordinate (𝟙 (muTwo k).X) :=
      (congrArg Units.val h).trans (unityGroupPoints_coord 2 _ _)
    _ = _ := hroot
    _ = _ := (congrArg (gammaSpecAlgEquiv (k := k) B).toAlgHom hmap).symm.trans
      (congrArg Units.val (globalCoord_affine (affineMap (muTwoCoordinateMap k)))).symm

private theorem muTwoCoordinateMap_surjective : Function.Surjective (muTwoCoordinateMap k) := by
  have h : (muTwoCoordinateMap k).comp Polynomial.toLaurentAlg =
      AdjoinRoot.mkₐ (squarePolynomial (1 : k)) := by
    apply Polynomial.algHom_ext
    change muTwoCoordinateMap k (Polynomial.toLaurent Polynomial.X) = _
    rw [Polynomial.toLaurent_X, muTwoCoordinateMap_T]
    rfl
  intro x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective (g := squarePolynomial (1 : k)) x
  exact ⟨Polynomial.toLaurent p, DFunLike.congr_fun h p⟩

private def squareRootsSubgroup (k : Type u) [Field k] : ClosedSubgroup (gm k) where
  group := muTwo k
  inclusion := rootInclusion k
  isClosedImmersion := by
    rw [rootInclusion_affine]
    exact IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (muTwoCoordinateMap k).toRingHom) muTwoCoordinateMap_surjective

private theorem gm_smooth (k : Type u) [Field k] : Smooth (gm k).X.hom := by
  have : Algebra.Smooth k[X] (laurent k) := Algebra.Smooth.of_isLocalization_Away X
  have : Algebra.Smooth k k[X] := ⟨inferInstance, inferInstance⟩
  have : IsScalarTower k k[X] (laurent k) := IsScalarTower.of_algebraMap_eq
    (fun a ↦ (Polynomial.toLaurent_C a).symm)
  have hs : Algebra.Smooth k (laurent k) := Algebra.Smooth.comp k k[X] (laurent k)
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (laurent k))))
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).2 (RingHom.smooth_algebraMap.mpr hs)

private theorem muTwo_smooth (h : (2 : k) ≠ 0) : Smooth (muTwo k).X.hom := by
  let f := squarePolynomial (1 : k)
  have hs : f.Separable := (X_pow_sub_C_separable_iff (by decide) one_ne_zero).mpr h
  obtain ⟨a, b, hab⟩ := hs
  let P : StandardEtalePair k :=
    ⟨f, monic_X_pow_sub_C _ (by decide), 1, ⟨b, a, 0, by simpa only [pow_zero, mul_comm, add_comm] using hab⟩⟩
  have hunit : Submonoid.powers (AdjoinRoot.mk P.f P.g) ≤ IsUnit.submonoid (AdjoinRoot f) := by
    rintro x ⟨n, rfl⟩
    simp [P]
  let e : P.Ring ≃ₐ[k] AdjoinRoot f := P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnits (AdjoinRoot f) _ hunit).symm.restrictScalars k)
  have : Algebra.Etale k (AdjoinRoot f) := Algebra.Etale.of_equiv e
  have hsmooth : Algebra.Smooth k (AdjoinRoot f) := inferInstance
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (AdjoinRoot f))))
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).2 (RingHom.smooth_algebraMap.mpr hsmooth)

set_option backward.isDefEq.respectTransparency true

private theorem squarePolynomial_fppf {R : Type u} [CommRing R] [Nontrivial R] (t : R) :
    IsFppf (Spec.map (CommRingCat.ofHom (algebraMap R (AdjoinRoot (squarePolynomial t))))) := by
  let B := AdjoinRoot (squarePolynomial t)
  have hmonic : (squarePolynomial t).Monic := monic_X_pow_sub_C t (by decide : (2 : ℕ) ≠ 0)
  have freeB : Module.Free R B := hmonic.free_adjoinRoot
  have nontrivialB : Nontrivial B := (AdjoinRoot.nontrivial_iff_of_monic hmonic).2 (by
    rw [Polynomial.degree_X_pow_sub_C (by decide : 0 < 2)]
    decide)
  have hflat : (algebraMap R B).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2 (inferInstance : Module.FaithfullyFlat R B)
  have hfin : (algebraMap R B).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.2 (inferInstance : Algebra.FinitePresentation R B)
  let f := CommRingCat.ofHom (algebraMap R B)
  exact ⟨((flat_and_surjective_SpecMap_iff f).2 hflat).1,
    ((flat_and_surjective_SpecMap_iff f).2 hflat).2,
    (LocallyOfFinitePresentation.SpecMap_iff f).2 hfin⟩

private theorem squareMap_cover (k : Type u) [Field k] :
    ∃ (V : SchemeOver k) (π r : V ⟶ (gm k).X),
      IsFppf π.left ∧ r ≫ squareMap k = π := by
  let A := laurent k
  let t : A := LaurentPolynomial.T 1
  let f := squarePolynomial t
  let B := AdjoinRoot f
  let baseChange : A →ₐ[k] B := IsScalarTower.toAlgHom k A B
  have hroot : IsUnit (AdjoinRoot.root f) := (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
    (by rw [adjoinedRoot_sq]; exact (LaurentPolynomial.isUnit_T 1).map (algebraMap A B))
  let v : A →ₐ[k] B := laurentEvaluation hroot.unit
  let p : affineTest k B ⟶ (gm k).X := affineMap v
  let q : affineTest k B ⟶ (gm k).X := affineMap baseChange
  have hfppf : IsFppf q.left := squarePolynomial_fppf t
  refine ⟨affineTest k B, q, p, hfppf, ?_⟩
  have hq : p ≫ squareMap k = p ^ 2 := by
    simp only [squareMap, MonObj.comp_mul, Category.comp_id, pow_two]
  rw [hq]
  apply (affineCoord (CommAlgCat.of k B)).injective
  rw [map_pow]
  apply Units.ext
  have hp : (affineCoord (CommAlgCat.of k B) p).val = AdjoinRoot.root f := by
    refine (affineCoord_map v).trans ?_
    change laurentEvaluation hroot.unit (LaurentPolynomial.T 1) = _
    rw [laurentEvaluation_T, zpow_one, IsUnit.unit_spec]
  have hq' : (affineCoord (CommAlgCat.of k B) q).val = algebraMap A B t :=
    affineCoord_map baseChange
  exact (congrArg (· ^ 2) hp).trans ((adjoinedRoot_sq t).trans hq'.symm)

private theorem singletonFppf {T U : SchemeOver k} (f : U ⟶ T) (hf : IsFppf f.left) :
    Sieve.generate (Presieve.singleton f) ∈ fppfOver k T := by
  obtain ⟨hflat, hsurj, hfp⟩ := hf
  change Sieve.overEquiv T (Sieve.generate (Presieve.singleton f)) ∈ Scheme.fppfTopology T.left
  apply Scheme.fppfTopology.superset_covering _ (Precoverage.generate_mem_toGrothendieck
    f.left.singleton_mem_fppfPrecoverage)
  rw [Sieve.overEquiv_generate]
  apply (Sieve.generate_le_iff _ _).2
  intro V g hg
  cases hg
  exact Sieve.le_generate _ _ _ ⟨U, f, 𝟙 _, Presieve.singleton_self f, by simp⟩

private theorem squareCoset_eq {T : SchemeOver k} (g h : T ⟶ (gm k).X) :
    g ≫ squareMap k = h ≫ squareMap k ↔
      ∃ a : T ⟶ (muTwo k).X, a ≫ (rootInclusion k).hom.hom = g⁻¹ * h := by
  rw [rootInclusion_kernel]
  constructor
  · intro he
    have hsq := congrArg (globalCoord T) he
    rw [squareMap_coord, squareMap_coord] at hsq
    rw [map_mul, map_inv, mul_pow, inv_pow, inv_mul_eq_one, hsq]
  · intro he
    rw [map_mul, map_inv, mul_pow, inv_pow, inv_mul_eq_one] at he
    apply (globalCoord T).injective
    rw [squareMap_coord, squareMap_coord, he]

private def squareOnCosets (k : Type u) [Field k] :
    rightCosetPresheaf (squareRootsSubgroup k) ⟶ (schemeFppfSheaf (gm k).X).obj where
  app T := ↾fun c ↦ Quotient.liftOn c.down (fun g ↦ ULift.up (g ≫ squareMap k)) (by
    intro g h e
    exact congrArg ULift.up ((squareCoset_eq g h).2
      (QuotientGroup.leftRel_apply.mp e)))
  naturality T U f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨c⟩
    induction c using QuotientGroup.induction_on with
    | H g =>
      apply ULift.ext
      exact Category.assoc _ _ _ |>.symm

private theorem squareOnCosets_localInjective (k : Type u) [Field k] :
    Presheaf.IsLocallyInjective (fppfOver k) (squareOnCosets k) := by
  apply Presheaf.isLocallyInjective_of_injective
  intro T c d he
  obtain ⟨c⟩ := c
  obtain ⟨d⟩ := d
  obtain ⟨g, rfl⟩ := Quotient.mk_surjective c
  obtain ⟨h, rfl⟩ := Quotient.mk_surjective d
  apply ULift.ext
  exact Quotient.sound (QuotientGroup.leftRel_apply.mpr
    ((squareCoset_eq g h).1 (congrArg ULift.down he)))

private theorem squareOnCosets_localSurjective (k : Type u) [Field k] :
    Presheaf.IsLocallySurjective (fppfOver k) (squareOnCosets k) := by
  obtain ⟨V, π, r, hπ, hr⟩ := squareMap_cover k
  constructor
  intro T y
  apply (fppfOver k).superset_covering ?_
    ((fppfOver k).pullback_stable y.down (singletonFppf π hπ))
  intro U f hf
  rcases hf with ⟨W, b, a, hb, h⟩
  cases hb
  refine ⟨⟨QuotientGroup.mk (b ≫ r)⟩, ULift.ext ?_⟩
  change (b ≫ r) ≫ squareMap k = f ≫ y.down
  rw [Category.assoc, hr]
  exact h

private def squareQuotientHom (k : Type u) [Field k] :
    rightQuotientSheaf (squareRootsSubgroup k) ⟶ schemeFppfSheaf (gm k).X :=
  ⟨sheafifyLift (fppfOver k) (squareOnCosets k) (schemeFppfSheaf (gm k).X).property⟩

private theorem squareQuotient_comm (k : Type u) [Field k] :
    toSheafify (fppfOver k) (rightCosetPresheaf (squareRootsSubgroup k)) ≫
        (squareQuotientHom k).hom = squareOnCosets k :=
  toSheafify_sheafifyLift _ _ _

private def squareQuotientIso (k : Type u) [Field k] :
    rightQuotientSheaf (squareRootsSubgroup k) ≅ schemeFppfSheaf (gm k).X := by
  have : IsIso (squareQuotientHom k) := by
    apply (Sheaf.isLocallyBijective_iff_isIso _).1
    constructor
    · apply (Presheaf.comp_isLocallyInjective_iff (fppfOver k)
        (toSheafify _ (rightCosetPresheaf (squareRootsSubgroup k))) (squareQuotientHom k).hom).1
      rw [squareQuotient_comm]
      exact squareOnCosets_localInjective k
    · apply (Presheaf.comp_isLocallySurjective_iff (fppfOver k)
        (toSheafify _ (rightCosetPresheaf (squareRootsSubgroup k))) (squareQuotientHom k).hom).1
      rw [squareQuotient_comm]
      exact squareOnCosets_localSurjective k
  exact asIso (squareQuotientHom k)

private theorem squareQuotientIso_proj {T : SchemeOver k} (g : T ⟶ (gm k).X) :
    (squareQuotientIso k).hom.hom.app (op T) (projectSection (squareRootsSubgroup k) g) =
      ULift.up (g ≫ squareMap k) :=
  congrArg (fun f ↦ f.app (op T) (ULift.up (QuotientGroup.mk g))) (squareQuotient_comm k)

private def fieldFunctions (k : Type u) [Field k] : testFunctions (fieldBase k) ≃ₐ[k] k := by
  let α := Scheme.ΓSpecIso (CommRingCat.of k)
  refine { __ := α.commRingCatIsoToRingEquiv, commutes' := fun a ↦ ?_ }
  change α.hom ((α.inv ≫ Scheme.Γ.map ((𝟙 (Spec (CommRingCat.of k))).op)) a) = a
  have hid : Scheme.Γ.map ((𝟙 (Spec (CommRingCat.of k))).op) = 𝟙 _ :=
    (congrArg Scheme.Γ.map (show (𝟙 (Spec (CommRingCat.of k))).op =
      𝟙 (op (Spec (CommRingCat.of k))) from op_id)).trans (Scheme.Γ.map_id _)
  have hcomp := (congrArg (α.inv ≫ ·) hid).trans (Category.comp_id α.inv)
  exact (congrArg (fun f ↦ α.hom (f a)) hcomp).trans (α.inv_hom_id_apply a)

private def rationalUnit (k : Type u) [Field k] : (fieldBase k ⟶ (gm k).X) ≃* kˣ :=
  (globalCoord (fieldBase k)).trans (Units.mapEquiv (fieldFunctions k).toMulEquiv)

private theorem rationalUnit_square (g : fieldBase k ⟶ (gm k).X) :
    rationalUnit k (g ≫ squareMap k) = rationalUnit k g ^ 2 := by
  have h : g ≫ squareMap k = g ^ 2 := by
    simp only [squareMap, MonObj.comp_mul, Category.comp_id, pow_two]
  exact (congrArg (rationalUnit k) h).trans (map_pow (rationalUnit k) g 2)

private def rationalSquareEquiv (k : Type u) [Field k] :
    RationalPoints (squareRootsSubgroup k) ≃ (fieldBase k ⟶ (gm k).X) :=
  (asIso ((squareQuotientIso k).hom.hom.app (op (fieldBase k)))).toEquiv.trans Equiv.ulift

private theorem rationalSquareEquiv_proj (g : fieldBase k ⟶ (gm k).X) :
    rationalSquareEquiv k (projectSection (squareRootsSubgroup k) g) = g ≫ squareMap k := by
  exact congrArg (fun z : ULift (fieldBase k ⟶ (gm k).X) ↦ z.down) (squareQuotientIso_proj g)

private theorem nonsquareQuotientPoint (a : kˣ) (ha : ¬IsSquare (a : k)) :
    ∃ x : RationalPoints (squareRootsSubgroup k),
      rationalUnit k (rationalSquareEquiv k x) = a ∧
      ∀ g : fieldBase k ⟶ (gm k).X, projectSection (squareRootsSubgroup k) g ≠ x := by
  let e := (rationalSquareEquiv k).trans (rationalUnit k).toEquiv
  let x := e.symm a
  have hx : e x = a := e.apply_symm_apply a
  refine ⟨x, hx, ?_⟩
  intro g hg
  have hp : e (projectSection (squareRootsSubgroup k) g) = rationalUnit k g ^ 2 :=
    (congrArg (rationalUnit k) (rationalSquareEquiv_proj g)).trans (rationalUnit_square g)
  have hsq := hp.symm.trans ((congrArg e hg).trans hx)
  have hval : (a : k) = (rationalUnit k g).val * (rationalUnit k g).val :=
    (congrArg Units.val hsq.symm).trans (pow_two _)
  exact ha ⟨(rationalUnit k g).val, hval⟩

/-- Over a finite field of odd order, squaring on the multiplicative group
gives a quotient by a smooth subgroup with rational points that fail to lift. -/
theorem nonsquareCounterexample : NonsquareCounterexample.{u} := by
  intro k _ _ hk
  have hc : ringChar k ≠ 2 := by
    intro h
    have hmod := Nat.odd_iff.mp hk
    rw [FiniteField.even_card_of_char_two h] at hmod
    contradiction
  have h₂ : (2 : k) ≠ 0 := by
    intro h
    have hd : ringChar k ∣ 2 := ringChar.dvd h
    exact hc ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left CharP.ringChar_ne_one)
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hc
  have hne : a ≠ 0 := fun he ↦ ha ⟨0, by simp [he]⟩
  let unit := Units.mk0 a hne
  have hSmooth := muTwo_smooth h₂
  have hDisconnected : ¬ ConnectedSpace (squareRootsSubgroup k).group.X.left := by
    intro hConnected
    obtain ⟨x, _, hx⟩ := nonsquareQuotientPoint unit ha
    obtain ⟨g, hg⟩ := finiteFieldLifting (multiplicativeGroup k) (squareRootsSubgroup k)
      (gm_smooth k) hSmooth hConnected x
    exact hx g hg
  exact ⟨multiplicativeGroup k, squareRootsSubgroup k, globalCoord, fieldFunctions k,
    squareMap k, squareQuotientIso k, gm_smooth k, hSmooth, hDisconnected, globalCoord_natural,
    fun _ g ↦ rootInclusion_kernel g, fun _ g ↦ squareMap_coord g,
    fun _ g ↦ squareQuotientIso_proj g, ⟨unit, ha⟩, nonsquareQuotientPoint⟩

end Squares

end

end LinearAlgebraicGroups.Descent.ExactLifting
