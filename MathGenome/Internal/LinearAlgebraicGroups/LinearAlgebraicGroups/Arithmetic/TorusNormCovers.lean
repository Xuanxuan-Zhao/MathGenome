import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TorusNormCovers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Algebra.TensorProduct Coalgebra
open scoped TensorProduct CategoryTheory.MonObj

universe u

noncomputable section

namespace LinearAlgebraicGroups.Arithmetic.TorusNormCovers

open LinearAlgebraicGroups.Descent
open Specs.TorusNormCovers (PrincipalOpen TorusCoversByProducts)
open Specs.GeometricRadicals (IsTorus)
open WeilRestriction (tensorMap extendScalars extendedUnits normPolynomial)

open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private groupLikeIso from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private polynomialPoints normPolynomial_eval openNormPoints from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction

attribute [local instance] Algebra.TensorProduct.rightAlgebra
set_option backward.isDefEq.respectTransparency false

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

private def coefficientAction (s : Gal(L/k)) (R : TestAlgebra k) :
    R ⊗[k] L →ₐ[k] R ⊗[k] L :=
  Algebra.TensorProduct.map (AlgHom.id k R) s.toAlgHom

private theorem coefficientAction_swap (s : Gal(L/k)) (R : TestAlgebra k) (x : R ⊗[k] L) :
    Algebra.TensorProduct.comm k R L (coefficientAction s R x) =
      (SemilinearAction.scalarExtension (k := k) (K := L) R).act s
        (Algebra.TensorProduct.comm k R L x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r l => rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

variable [FiniteDimensional k L] [IsGalois k L]

private theorem coefficientAction_fixed_iff (R : TestAlgebra k) (x : R ⊗[k] L) :
    (∀ s : Gal(L/k), coefficientAction s R x = x) ↔
      ∃ r : R, (includeLeft : R →ₐ[k] R ⊗[k] L) r = x := by
  let c := Algebra.TensorProduct.comm k R L
  constructor
  · intro h
    let a : (SemilinearAction.scalarExtension (k := k) (K := L) R).fixed :=
      ⟨c x, fun s => by rw [← coefficientAction_swap, h s]⟩
    obtain ⟨r, hr⟩ := (SemilinearAction.scalarExtension_bijective (k := k) (K := L) R).2 a
    exact ⟨r, c.injective (congrArg Subtype.val hr)⟩
  · rintro ⟨r, rfl⟩ s
    change r ⊗ₜ[k] s 1 = r ⊗ₜ[k] 1
    rw [map_one]

private theorem includeLeft_injective (R : TestAlgebra k) :
    Function.Injective (includeLeft : R →ₐ[k] R ⊗[k] L) := by
  intro a b h
  apply (SemilinearAction.scalarExtension_bijective (k := k) (K := L) R).1
  exact Subtype.ext (congrArg (Algebra.TensorProduct.comm k R L) h)


section Splitting

open LinearAlgebraicGroups.CharacterDescent
open Specs.CharacterDescent (GeometricCharacters StandardLattice IsDiagonalizable)
open Specs.DiagonalizableGroups (groupAlgebra)

private theorem finiteSplit {k : Type u} [Field k] [CharZero k]
    (T : AffineAlgebraicGroup k) (hT : IsTorus T.val) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
      (_ : FiniteDimensional k L) (_ : IsGalois k L) (m : ℕ),
      Nonempty ((groupBaseChange k L).obj T.val ≅
        (StandardGroups.multiplicativePowerGroup L (ULift.{u} (Fin m))).val) := by
  let K := AlgebraicClosure k
  obtain ⟨A₀, ⟨eT₀⟩⟩ := (essImage_hopfSpec (R := CommRingCat.of k)).mpr T.property.1
  let A : HopfAlgebraCategory k := A₀.unop
  let eT : specGroup A ≅ T.val := eT₀
  have hA : Specs.CharacterDescent.IsTorus A := by
    apply (torusOnSchemes A).mpr
    obtain ⟨E, _, _, _, m, ⟨e⟩⟩ := hT
    exact ⟨E, inferInstance, inferInstance, inferInstance, m,
      ⟨(groupBaseChange k E).mapIso eT ≪≫ e⟩⟩
  have hM := torusIsMultiplicativeType A hA
  obtain ⟨L, hL, hG, hD⟩ := finiteGaloisSplitting (K := K) A hM
  obtain ⟨m, ⟨eM⟩⟩ := ((torusAndSplitCriteria (K := K) A hM).1.mp hA)
  obtain ⟨M, ⟨d⟩⟩ := hD
  let g : M.obj ≃* StandardLattice.{u} m :=
    (monomialCharacterEquiv (M := M.obj) L) |>.trans (groupLikeIso d) |>.trans
      (MulEquiv.ofBijective (baseChangeCharacterMap K (extendedHopf L A))
        (baseChangeCharacterMap_bijective K _ ⟨M, ⟨d⟩⟩)) |>.trans
      (groupLikeIso (extendedHopfTower K A)) |>.trans eM
  let d' : groupAlgebra L (StandardLattice.{u} m) ≅ extendedHopf L A :=
    CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv L L g.symm) ≪≫ d
  obtain ⟨e⟩ := standardSplitTorus (k := L) m
  exact ⟨L, inferInstance, inferInstance, hL, hG, m,
    ⟨(groupBaseChange k L).mapIso eT.symm ≪≫ (extendedGroupIso L A).symm ≪≫
      (hopfSpec (CommRingCat.of L)).mapIso d'.op ≪≫ e⟩⟩

end Splitting

private abbrev tensorTest (R : TestAlgebra k) : TestAlgebra k :=
  CommAlgCat.of k (R ⊗[k] L)

private def extendTestMap {R S : TestAlgebra k} (f : R ⟶ S) :
    tensorTest (L := L) R ⟶ tensorTest (L := L) S :=
  CommAlgCat.ofHom (Algebra.TensorProduct.map f.hom (AlgHom.id k L))

private def tensorInclusion (R : TestAlgebra k) : R ⟶ tensorTest (L := L) R :=
  CommAlgCat.ofHom includeLeft

private def conjugation (s : Gal(L/k)) (R : TestAlgebra k) :
    tensorTest (L := L) R ⟶ tensorTest (L := L) R :=
  CommAlgCat.ofHom (coefficientAction s R)

private def specifiedScalars (R : Type u) [CommRing R] [Algebra k R] [Algebra L R]
    [IsScalarTower k L R] :
    (restrictTestAlgebra k L).obj (CommAlgCat.of L R) ≅ CommAlgCat.of k R where
  hom := (CommAlgCat.homEquivCommRingCat _ _).symm
    ⟨CommRingCat.ofHom (RingHom.id R),
      RingHom.ext fun x => (IsScalarTower.algebraMap_apply k L R x).symm⟩
  inv := (CommAlgCat.homEquivCommRingCat _ _).symm
    ⟨CommRingCat.ofHom (RingHom.id R),
      RingHom.ext (IsScalarTower.algebraMap_apply k L R)⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

private abbrev torusPoints (T : GroupScheme k) := groupPointsFunctor k |>.obj T

private abbrev pointsHom (T : GroupScheme k) {R S : TestAlgebra k} (a : R ⟶ S) :
    Points T.X R →* Points T.X S :=
  ((torusPoints T).map a).hom

private def baseChangedPoints (T : GroupScheme k) (R : Type u)
    [CommRing R] [Algebra k R] [Algebra L R] [IsScalarTower k L R] :
    Points ((groupBaseChange k L).obj T).X (CommAlgCat.of L R) ≃*
      Points T.X (CommAlgCat.of k R) :=
  (baseChangePointGroupEquiv L T (CommAlgCat.of L R)).trans
    ((torusPoints T).mapIso (specifiedScalars (k := k) (L := L) R)).groupIsoToMulEquiv

private def splitCoordinates {m : ℕ} {T : GroupScheme k}
    (e : (groupBaseChange k L).obj T ≅
      (StandardGroups.multiplicativePowerGroup L (ULift.{u} (Fin m))).val)
    (R : Type u) [CommRing R] [Algebra k R] [Algebra L R] [IsScalarTower k L R] :
    Points T.X (CommAlgCat.of k R) ≃* (ULift.{u} (Fin m) → Rˣ) :=
  (baseChangedPoints (L := L) T R).symm.trans
    (((groupPointsFunctor L).mapIso e ≪≫
      StandardGroups.multiplicativePowerGroupPointsIso L (ULift.{u} (Fin m))).app (CommAlgCat.of L R)).groupIsoToMulEquiv

private theorem mapPoints_comp {k : Type u} [Field k]
    {X : SchemeOver k} {R S U : TestAlgebra k}
    (a : R ⟶ S) (b : S ⟶ U) (p : Points X R) :
    mapPoints b (mapPoints a p) = mapPoints (a ≫ b) p := by
  have hop : (a ≫ b).op = b.op ≫ a.op := rfl
  simp only [mapPoints, hop, Functor.map_comp, Category.assoc]

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem specifiedScalars_tensor_natural {R S : TestAlgebra k} (a : R ⟶ S) :
    (restrictTestAlgebra k L).map ((extendScalars k L).map a) ≫
        (specifiedScalars (k := k) (L := L) (S ⊗[k] L)).hom =
      (specifiedScalars (k := k) (L := L) (R ⊗[k] L)).hom ≫ extendTestMap a := by
  rfl

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem baseChangedPoints_tensor_natural (T : GroupScheme k) {R S : TestAlgebra k}
    (a : R ⟶ S) (x : Points ((groupBaseChange k L).obj T).X ((extendScalars k L).obj R)) :
    baseChangedPoints (L := L) T (S ⊗[k] L) (mapPoints ((extendScalars k L).map a) x) =
      mapPoints (extendTestMap a) (baseChangedPoints (L := L) T (R ⊗[k] L) x) := by
  let jR := specifiedScalars (k := k) (L := L) (R ⊗[k] L)
  let jS := specifiedScalars (k := k) (L := L) (S ⊗[k] L)
  let aL := (extendScalars k L).map a
  let R' := (extendScalars k L).obj R
  let S' := (extendScalars k L).obj S
  change mapPoints jS.hom (baseChangePoint k L T.X S' (mapPoints aL x)) =
    mapPoints (extendTestMap a) (mapPoints jR.hom (baseChangePoint k L T.X R' x))
  have h := baseChangePointsNaturality k L T.X aL x
  rw [h, mapPoints_comp, mapPoints_comp, specifiedScalars_tensor_natural (L := L) a]

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem splitCoordinates_tensor_natural {m : ℕ} {T : GroupScheme k}
    (e : (groupBaseChange k L).obj T ≅
      (StandardGroups.multiplicativePowerGroup L (ULift.{u} (Fin m))).val)
    {R S : TestAlgebra k} (a : R ⟶ S) (p : Points T.X (tensorTest (L := L) R))
    (i : ULift.{u} (Fin m)) :
    splitCoordinates e (S ⊗[k] L) (mapPoints (extendTestMap a) p) i =
      Units.map (tensorMap k L a.hom).toMonoidHom (splitCoordinates e (R ⊗[k] L) p i) := by
  let aL := (extendScalars k L).map a
  let R' := (extendScalars k L).obj R
  let S' := (extendScalars k L).obj S
  let x : Points ((groupBaseChange k L).obj T).X R' :=
    (baseChangedPoints (L := L) T (R ⊗[k] L)).symm p
  have h : (baseChangedPoints (L := L) T (R ⊗[k] L)) x = p := MulEquiv.apply_symm_apply _ _
  have hx : (baseChangedPoints (L := L) T (S ⊗[k] L)).symm
      (mapPoints (extendTestMap a) p) = mapPoints aL x := by
    apply (baseChangedPoints (L := L) T (S ⊗[k] L)).injective
    rw [MulEquiv.apply_symm_apply, baseChangedPoints_tensor_natural, h]
  let d := (groupPointsFunctor L).mapIso e ≪≫
    StandardGroups.multiplicativePowerGroupPointsIso L (ULift.{u} (Fin m))
  have hd := d.hom.naturality_apply aL x
  change d.hom.app S' (mapPoints aL x) =
    (fun j : ULift.{u} (Fin m) => Units.map (tensorMap k L a.hom).toMonoidHom (d.hom.app R' x j)) at hd
  change d.hom.app S' ((baseChangedPoints (L := L) T (S ⊗[k] L)).symm
      (mapPoints (extendTestMap a) p)) i =
    Units.map (tensorMap k L a.hom).toMonoidHom (d.hom.app R' x i)
  rw [hx]
  exact congrArg (fun v : ULift.{u} (Fin m) → (S ⊗[k] L)ˣ => v i) hd

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem conjugation_comp (R : TestAlgebra k) (s t : Gal(L/k)) :
    conjugation s R ≫ conjugation t R = conjugation (t * s) R := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change coefficientAction t R (coefficientAction s R x) = coefficientAction (t * s) R x
  induction x using TensorProduct.inductionOn with
  | tmul r l => rfl
  | add x y hx hy => simp [hx, hy]

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem inclusion_conjugation (R : TestAlgebra k) (s : Gal(L/k)) :
    tensorInclusion (L := L) R ≫ conjugation s R = tensorInclusion R := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change x ⊗ₜ[k] s 1 = x ⊗ₜ[k] 1
  rw [map_one]

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem inclusion_natural {R S : TestAlgebra k} (a : R ⟶ S) :
    tensorInclusion (L := L) R ≫ extendTestMap a = a ≫ tensorInclusion S := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  rfl

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem conjugation_natural {R S : TestAlgebra k} (a : R ⟶ S) (s : Gal(L/k)) :
    conjugation s R ≫ extendTestMap a = extendTestMap a ≫ conjugation s S := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change extendTestMap a (coefficientAction s R x) =
    coefficientAction s S (extendTestMap (L := L) a x)
  induction x using TensorProduct.inductionOn with
  | tmul r l => rfl
  | add x y hx hy => simp [hx, hy]

private theorem inclusionPoints_injective {X : SchemeOver k} (hX : IsAffine X.left)
    (R : TestAlgebra k) : Function.Injective
      (mapPoints (X := X) (tensorInclusion (L := L) R)) := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr hX
  let d := WeilRestriction.spectrumPoints A.unop X e
  intro p q hpq
  apply (d.app R).toEquiv.symm.injective
  change (d.inv.app R p : A.unop ⟶ R) = d.inv.app R q
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  apply includeLeft_injective (L := L) R
  have h := d.inv.naturality_apply (tensorInclusion (L := L) R) p
  have h' := d.inv.naturality_apply (tensorInclusion (L := L) R) q
  change d.inv.app _ (mapPoints _ p) = _ at h
  change d.inv.app _ (mapPoints _ q) = _ at h'
  rw [hpq] at h
  exact congrArg (fun f : A.unop ⟶ tensorTest (L := L) R => f x) (h.symm.trans h')

private theorem exists_descendedPoint {X : SchemeOver k} (hX : IsAffine X.left)
    (R : TestAlgebra k) (p : Points X (tensorTest (L := L) R))
    (hp : ∀ s : Gal(L/k), mapPoints (conjugation s R) p = p) :
    ∃ q : Points X R, mapPoints (tensorInclusion (L := L) R) q = p := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr hX
  let d := WeilRestriction.spectrumPoints A.unop X e
  let f : A.unop ⟶ tensorTest (L := L) R := d.inv.app _ p
  have hf (x : A.unop) (s : Gal(L/k)) : coefficientAction s R (f x) = f x := by
    have h := d.inv.naturality_apply (conjugation s R) p
    change d.inv.app _ (mapPoints _ p) = f ≫ conjugation s R at h
    rw [hp s] at h
    exact congrArg (fun g : A.unop ⟶ tensorTest (L := L) R => g x) h.symm
  choose g hg using fun x => (coefficientAction_fixed_iff R (f x)).mp (hf x)
  let j : A.unop →ₐ[k] R :=
    { toFun := g
      map_one' := (includeLeft_injective (L := L) R) (by rw [hg, map_one, map_one])
      map_zero' := (includeLeft_injective (L := L) R) (by rw [hg, map_zero, map_zero])
      map_mul' := fun x y => (includeLeft_injective (L := L) R) (by simp only [map_mul, hg])
      map_add' := fun x y => (includeLeft_injective (L := L) R) (by simp only [map_add, hg])
      commutes' := fun x => (includeLeft_injective (L := L) R) (by
        rw [hg, f.hom.commutes, includeLeft.commutes]) }
  refine ⟨d.hom.app R (CommAlgCat.ofHom j), ?_⟩
  change (WeilRestriction.schemePoints k X).map _ _ = _
  rw [← d.hom.naturality_apply]
  have hj : CommAlgCat.ofHom j ≫ tensorInclusion (L := L) R = f := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact hg x
  change d.hom.app _ (CommAlgCat.ofHom j ≫ tensorInclusion (L := L) R) = p
  rw [hj]
  exact (d.app _).toEquiv.apply_symm_apply p

section Norm

variable {T : AffineAlgebraicGroup k} {m : ℕ}
variable (e : (groupBaseChange k L).obj T.val ≅
  (StandardGroups.multiplicativePowerGroup L (ULift.{u} (Fin m))).val)

private abbrev extendedPointCommGroup (R : TestAlgebra k) :
    CommGroup (Points T.val.X (tensorTest (L := L) R)) :=
  { (inferInstance : Group (Points T.val.X (tensorTest (L := L) R))) with
    mul_comm := fun x y => (splitCoordinates e (R ⊗[k] L)).injective (by
      rw [map_mul, map_mul, mul_comm]) }

private def conjugateProduct (R : TestAlgebra k) (x : Points T.val.X (tensorTest (L := L) R)) :
    Points T.val.X (tensorTest (L := L) R) := by
  let := extendedPointCommGroup e R
  classical
  exact ∏ s : Gal(L/k), mapPoints (conjugation s R) x

omit [IsGalois k L] in
private theorem conjugateProduct_fixed (R : TestAlgebra k)
    (x : Points T.val.X (tensorTest (L := L) R)) (t : Gal(L/k)) :
    mapPoints (conjugation t R) (conjugateProduct e R x) = conjugateProduct e R x := by
  let := extendedPointCommGroup e R
  classical
  unfold conjugateProduct
  change pointsHom T.val (conjugation t R) (∏ s : Gal(L/k), mapPoints (conjugation s R) x) = _
  rw [map_prod]
  change (∏ s : Gal(L/k), mapPoints (conjugation t R) (mapPoints (conjugation s R) x)) =
    ∏ s : Gal(L/k), mapPoints (conjugation s R) x
  simp only [mapPoints_comp, conjugation_comp]
  exact Fintype.prod_equiv (Equiv.mulLeft t) _ _ (fun _ => rfl)

private def normPoint (R : TestAlgebra k) (x : Points T.val.X (tensorTest (L := L) R)) :
    Points T.val.X R :=
  (exists_descendedPoint T.property.1 R (conjugateProduct e R x)
    (conjugateProduct_fixed e R x)).choose

private theorem normPoint_spec (R : TestAlgebra k) (x : Points T.val.X (tensorTest (L := L) R)) :
    mapPoints (tensorInclusion (L := L) R) (normPoint e R x) = conjugateProduct e R x :=
  (exists_descendedPoint T.property.1 R (conjugateProduct e R x)
    (conjugateProduct_fixed e R x)).choose_spec

private theorem normPoint_natural {R S : TestAlgebra k} (a : R ⟶ S)
    (x : Points T.val.X (tensorTest (L := L) R)) :
    normPoint e S (mapPoints (extendTestMap a) x) = mapPoints a (normPoint e R x) := by
  apply inclusionPoints_injective (L := L) T.property.1 S
  rw [normPoint_spec, mapPoints_comp, ← inclusion_natural, ← mapPoints_comp, normPoint_spec]
  let := extendedPointCommGroup e R
  let := extendedPointCommGroup e S
  classical
  unfold conjugateProduct
  change _ = pointsHom T.val (extendTestMap a) (∏ s : Gal(L/k), mapPoints (conjugation s R) x)
  rw [map_prod]
  change (∏ s : Gal(L/k), mapPoints (conjugation s S) (mapPoints (extendTestMap a) x)) =
    ∏ s : Gal(L/k), mapPoints (extendTestMap a) (mapPoints (conjugation s R) x)
  simp only [mapPoints_comp, conjugation_natural]

private theorem normPoint_diagonal (R : TestAlgebra k) (x : Points T.val.X R) :
    normPoint e R (mapPoints (tensorInclusion (L := L) R) x) =
      x ^ Fintype.card (Gal(L/k)) := by
  apply inclusionPoints_injective (L := L) T.property.1 R
  rw [normPoint_spec]
  let := extendedPointCommGroup e R
  classical
  rw [conjugateProduct]
  change _ = pointsHom T.val (tensorInclusion (L := L) R) (x ^ _)
  rw [map_pow]
  change (∏ s : Gal(L/k), mapPoints (conjugation s R) (mapPoints (tensorInclusion R) x)) =
    (mapPoints (tensorInclusion (L := L) R) x) ^ _
  simp only [mapPoints_comp, inclusion_conjugation, Finset.prod_const, Finset.card_univ]

end Norm


section Cover

variable {d : ℕ} (b : Module.Basis (ULift.{u} (Fin d)) k L)

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem normPolynomial_ne_zero : normPolynomial b ≠ 0 := by
  let R := CommAlgCat.of k k
  let d := polynomialPoints b R
  let a := d.symm 1
  have ha : IsUnit (a (normPolynomial b)) := (normPolynomial_eval b R a).mpr (by
    change IsUnit (d (d.symm 1))
    rw [Equiv.apply_symm_apply]
    exact isUnit_one)
  intro h
  rw [h, map_zero] at ha
  exact not_isUnit_zero ha

private abbrev unitOpen := PrincipalOpen (normPolynomial b)

private def unitOpenPointsIso :
    pointsFunctor (unitOpen b) ≅ extendedUnits k L ⋙ forget GrpCat :=
  openNormPoints b

private def openUnits (R : TestAlgebra k) :
    Points (unitOpen b) R ≃ (R ⊗[k] L)ˣ :=
  ((unitOpenPointsIso b).app R).toEquiv

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem openUnits_natural {R S : TestAlgebra k} (a : R ⟶ S) (x : Points (unitOpen b) R) :
    openUnits b S (mapPoints a x) = Units.map (tensorMap k L a.hom).toMonoidHom (openUnits b R x) := by
  have h := (unitOpenPointsIso b).hom.naturality_apply a x
  exact h

variable {T : AffineAlgebraicGroup k} {m : ℕ}
variable (e : (groupBaseChange k L).obj T.val ≅
  (StandardGroups.multiplicativePowerGroup L (ULift.{u} (Fin m))).val)

private abbrev coverSource (m : ℕ) := ∏ᶜ fun _ : Fin m => unitOpen b

private def coveringPoints (R : TestAlgebra k) (x : Points (coverSource b m) R) :
    Points T.val.X (tensorTest (L := L) R) :=
  (splitCoordinates e (R ⊗[k] L)).symm fun i => openUnits b R (x ≫ Pi.π _ i.down)

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem coveringPoints_surjective (R : TestAlgebra k) :
    Function.Surjective (coveringPoints b e R) := by
  intro x
  let y (i : Fin m) : Points (unitOpen b) R :=
    (openUnits b R).symm (splitCoordinates e (R ⊗[k] L) x ⟨i⟩)
  refine ⟨Pi.lift y, (splitCoordinates e (R ⊗[k] L)).injective ?_⟩
  rw [coveringPoints, MulEquiv.apply_symm_apply]
  funext i
  simp [y]

omit [FiniteDimensional k L] [IsGalois k L] in
private theorem coveringPoints_natural {R S : TestAlgebra k} (a : R ⟶ S)
    (x : Points (coverSource b m) R) :
    coveringPoints b e S (mapPoints a x) = mapPoints (extendTestMap a) (coveringPoints b e R x) := by
  apply (splitCoordinates e (S ⊗[k] L)).injective
  funext i
  rw [splitCoordinates_tensor_natural]
  simp only [coveringPoints, MulEquiv.apply_symm_apply]
  have h := openUnits_natural b a (x ≫ Pi.π _ i.down)
  simpa only [mapPoints, Category.assoc] using h

private def productCoordinates (m : ℕ) : (TestAlgebra k)ᵒᵖ :=
  ∏ᶜ fun _ : Fin m => op (CommAlgCat.of k (WeilRestriction.NormCoordinates b))

private def productSpectrum : (testSpec k).obj (productCoordinates b m) ≅ coverSource b m :=
  let A : Fin m → (TestAlgebra k)ᵒᵖ := fun _ =>
    op (CommAlgCat.of k (WeilRestriction.NormCoordinates b))
  letI : PreservesLimitsOfSize.{0, 0} (testSpec k) :=
    @AlgebraicGeometry.preservesLimitsOfSize_algSpec.{0, 0, u} (CommRingCat.of k)
  preservesLimitIso (testSpec k) (Discrete.functor A) ≪≫
    HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete A (testSpec k))

private def morphismOfPointMap {X Y : SchemeOver k} {A : (TestAlgebra k)ᵒᵖ}
    (j : (testSpec k).obj A ≅ X) (g : ∀ R : TestAlgebra k, Points X R → Points Y R) :
    X ⟶ Y :=
  j.inv ≫ g A.unop j.hom

private theorem morphismOfPointMap_apply {X Y : SchemeOver k} {A : (TestAlgebra k)ᵒᵖ}
    (j : (testSpec k).obj A ≅ X) (g : ∀ R : TestAlgebra k, Points X R → Points Y R)
    (hg : ∀ {R S : TestAlgebra k} (a : R ⟶ S) (x : Points X R),
      g S (mapPoints a x) = mapPoints a (g R x))
    (R : TestAlgebra k) (x : Points X R) :
    x ≫ morphismOfPointMap j g = g R x := by
  let u := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (x ≫ j.inv)
  let a := u.unop
  have hu : (testSpec k).map a.op = x ≫ j.inv :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  have hx : mapPoints a j.hom = x := by
    rw [mapPoints, hu, Category.assoc, j.inv_hom_id, Category.comp_id]
  calc
    x ≫ morphismOfPointMap j g = mapPoints a (g A.unop j.hom) := by
      rw [mapPoints, hu, Category.assoc]
      rfl
    _ = g R x := by rw [← hg, hx]

private def coveringMorphism : coverSource b m ⟶ T.val.X :=
  morphismOfPointMap (productSpectrum (m := m) b)
    (fun R x => normPoint e R (coveringPoints b e R x))

private theorem coveringMorphism_apply (R : TestAlgebra k) (x : Points (coverSource b m) R) :
    x ≫ coveringMorphism b e = normPoint e R (coveringPoints b e R x) := by
  apply morphismOfPointMap_apply
  intro R₁ R₂ a y
  rw [coveringPoints_natural, normPoint_natural]

private theorem unitPower_surjective (E : Type u) [Field E] [IsAlgClosed E]
    {n : ℕ} (hn : 0 < n) : Function.Surjective (fun v : Eˣ => v ^ n) := by
  intro u
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (u : E) hn
  have hne : v ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt hn)] at hv
    exact u.ne_zero hv.symm
  exact ⟨Units.mk0 v hne, Units.ext (by simpa using hv)⟩

include e in
omit [FiniteDimensional k L] in
private theorem torusPower_surjective (E : Type u) [Field E] [Algebra k E] [IsAlgClosed E]
    {n : ℕ} (hn : 0 < n) :
    Function.Surjective (fun x : Points T.val.X (CommAlgCat.of k E) => x ^ n) := by
  let j : L →ₐ[k] E := IsAlgClosed.lift
  let : Algebra L E := j.toRingHom.toAlgebra
  let : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  let c := splitCoordinates e E
  intro x
  choose y hy using fun i => unitPower_surjective E hn (c x i)
  refine ⟨c.symm y, c.injective ?_⟩
  rw [map_pow, MulEquiv.apply_symm_apply]
  exact funext hy

include e in
private theorem normPoint_surjective (E : Type u) [Field E] [Algebra k E] [IsAlgClosed E] :
    Function.Surjective (normPoint e (CommAlgCat.of k E)) := by
  classical
  intro x
  obtain ⟨y, hy⟩ := torusPower_surjective e E (n := Fintype.card (Gal(L/k))) Fintype.card_pos x
  exact ⟨mapPoints (tensorInclusion (L := L) (CommAlgCat.of k E)) y,
    (normPoint_diagonal e (CommAlgCat.of k E) y).trans hy⟩

private theorem coveringMorphism_surjective (E : Type u) [Field E] [Algebra k E] [IsAlgClosed E] :
    Function.Surjective (fun x : Points (coverSource b m) (CommAlgCat.of k E) =>
      x ≫ coveringMorphism b e) := by
  let R := CommAlgCat.of k E
  have h : (fun x : Points (coverSource b m) R => x ≫ coveringMorphism b e) =
      normPoint e R ∘ coveringPoints b e R := funext (coveringMorphism_apply b e R)
  exact h.symm ▸ (normPoint_surjective e E).comp (coveringPoints_surjective b e R)

include e in
private theorem exists_coveringMorphism :
    ∃ f : coverSource b m ⟶ T.val.X,
      ∀ (E : Type u) [Field E] [Algebra k E] [IsAlgClosed E],
        Function.Surjective (fun x : Points (coverSource b m) (CommAlgCat.of k E) => x ≫ f) :=
  ⟨coveringMorphism b e, coveringMorphism_surjective b e⟩

end Cover

omit [IsGalois k L] in
private theorem exists_liftedBasis :
    ∃ d : ℕ, Nonempty (Module.Basis (ULift.{u} (Fin d)) k L) :=
  ⟨Module.finrank k L, ⟨(Module.finBasis k L).reindex Equiv.ulift.symm⟩⟩

/-- The norm for a finite Galois splitting field gives the required cover by principal opens. -/
theorem torusCoversByProducts : TorusCoversByProducts.{u} := by
  intro k _ _ T hT
  obtain ⟨L, _, _, _, _, m, ⟨e⟩⟩ := finiteSplit T hT
  obtain ⟨d, ⟨b⟩⟩ := exists_liftedBasis (k := k) (L := L)
  obtain ⟨f, hf⟩ := exists_coveringMorphism b e
  exact ⟨m, fun _ => d, fun _ => normPolynomial b, fun _ => normPolynomial_ne_zero b, f, hf⟩

end LinearAlgebraicGroups.Arithmetic.TorusNormCovers
