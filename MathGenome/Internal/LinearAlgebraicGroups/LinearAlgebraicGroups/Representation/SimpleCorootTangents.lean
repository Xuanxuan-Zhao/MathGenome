import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SimpleCorootTangents
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Flat.TorsionFree

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Representation.SimpleCorootTangents

open _root_.LinearAlgebraicGroups.Specs
open Specs.SimpleCorootTangents
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter StandardLattice)
open Specs.DiagonalizableGroups (IntegerCharacters characterValuedPoints groupAlgebra groupAlgebraMap)
open Specs.GeometricRadicals (IsSplitTorus)
open CocharacterDynamics (cocharacterPoint unitPoint unitCoordinates mapPoints_cocharacterPoint)
open LinearAlgebraicGroups.DiagonalizableGroups (groupAlgebraPointsIso)

open private splitPresentation cocharactersOfIso latticeCoordinates homToDual integerExponent
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private pointsIso_spec pointsIso_precompose from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private unitPointHom unitPointHom_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private differential_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private point_liftST_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
open private semisimple_iff_corootFullRank
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000

variable {k : Type u} [Field k] {T : GroupScheme k}

private abbrev dualAlgebra (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)

private def firstOrderUnit (a : k) : (DualNumber k)ˣ :=
  ⟨⟨1, a⟩, ⟨1, -a⟩, TrivSqZeroExt.ext (one_mul _) (by simp),
    TrivSqZeroExt.ext (one_mul _) (by simp)⟩

private def firstOrderUnits : k →+ Additive (DualNumber k)ˣ where
  toFun a := Additive.ofMul (firstOrderUnit a)
  map_zero' := by
    apply Units.ext
    exact TrivSqZeroExt.ext rfl rfl
  map_add' a b := by
    apply Units.ext
    exact TrivSqZeroExt.ext (one_mul _).symm (by
      change a + b = 1 * b + a * 1
      simp [add_comm])

private theorem infinitesimalUnit_eq : infinitesimalUnit k = firstOrderUnit (1 : k) := by
  apply Units.ext
  rw [show (infinitesimalUnit k).val = 1 + DualNumber.eps from IsUnit.unit_spec _]
  exact TrivSqZeroExt.ext (by simp [firstOrderUnit]) (by simp [firstOrderUnit])

private theorem infinitesimalUnit_zpow (n : ℤ) :
    ((infinitesimalUnit k ^ n).val).snd = (n : k) := by
  have h := (firstOrderUnits (k := k)).map_zsmul n (1 : k)
  change firstOrderUnit (n • (1 : k)) = firstOrderUnit (1 : k) ^ n at h
  rw [infinitesimalUnit_eq, ← h, zsmul_one]
  rfl

private def cocharacterTangent (c : Cocharacter T) : Lie k T :=
  ⟨cocharacterPoint c (dualAlgebra k) (infinitesimalUnit k), by
    change mapPoints (dualReduction k) (cocharacterPoint c (dualAlgebra k) (infinitesimalUnit k)) = 1
    rw [mapPoints_cocharacterPoint]
    have h : Units.map (dualReduction k).hom.toMonoidHom (infinitesimalUnit k) = 1 := by
      rw [infinitesimalUnit_eq]
      apply Units.ext
      rfl
    rw [h]
    unfold cocharacterPoint
    rw [← unitPointHom_apply, map_one, map_one]⟩

section Coordinates

variable {M : Type u} [CommGroup M]
  (E : (groupPointsFunctor k).obj T ≅ characterValuedPoints k M)

private def pointCoordinates (R : TestAlgebra k) : GroupPoints T R ≃* (M →* Rˣ) :=
  (E.app R).groupIsoToMulEquiv

private theorem pointCoordinates_injective (R : TestAlgebra k) :
    Function.Injective (pointCoordinates E R) :=
  (pointCoordinates E R).injective

private theorem pointCoordinates_surjective (R : TestAlgebra k) :
    Function.Surjective (pointCoordinates E R) :=
  (pointCoordinates E R).surjective

private theorem pointCoordinates_mul (R : TestAlgebra k) (p q : GroupPoints T R) (m : M) :
    pointCoordinates E R (p * q) m = pointCoordinates E R p m * pointCoordinates E R q m := by
  rw [map_mul, MonoidHom.mul_apply]

private theorem pointCoordinates_natural {R S : TestAlgebra k} (a : R ⟶ S)
    (p : GroupPoints T R) (m : M) :
    pointCoordinates E S (mapPoints a p) m =
      Units.map a.hom.toMonoidHom (pointCoordinates E R p m) := by
  have h := NatTrans.naturality_apply E.hom a p
  change pointCoordinates E S (mapPoints a p) =
    (Units.map a.hom.toMonoidHom).comp (pointCoordinates E R p) at h
  exact DFunLike.congr_fun h m

private theorem tangentCoordinate_fst (p : Lie k T) (m : M) :
    (pointCoordinates E (dualAlgebra k) p.toMul.val m).val.fst = 1 := by
  have h := pointCoordinates_natural E (dualReduction k) p.toMul.val m
  rw [show mapPoints (dualReduction k) p.toMul.val = 1 from p.toMul.property,
    map_one] at h
  exact (congrArg Units.val h).symm

private def tangentFunctional (p : Lie k T) : Additive M →ₗ[ℤ] k :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun m ↦ (pointCoordinates E (dualAlgebra k) p.toMul.val m.toMul).val.snd
      map_zero' := by
        change (pointCoordinates E (dualAlgebra k) p.toMul.val 1).val.snd = 0
        rw [map_one]
        rfl
      map_add' := by
        intro m n
        change (pointCoordinates E (dualAlgebra k) p.toMul.val (m.toMul * n.toMul)).val.snd = _
        rw [map_mul]
        change (pointCoordinates E (dualAlgebra k) p.toMul.val m.toMul).val.fst *
            (pointCoordinates E (dualAlgebra k) p.toMul.val n.toMul).val.snd +
          (pointCoordinates E (dualAlgebra k) p.toMul.val m.toMul).val.snd *
            (pointCoordinates E (dualAlgebra k) p.toMul.val n.toMul).val.fst = _
        rw [tangentCoordinate_fst, tangentCoordinate_fst, one_mul, mul_one, add_comm] }

private def tangentLinearEquiv (t : IdentityLieStructure T) :
    letI := t.lieRing
    letI := t.lieAlgebra
    Lie k T ≃ₗ[k] (Additive M →ₗ[ℤ] k) := by
  letI := t.lieRing
  letI := t.lieAlgebra
  let L : Lie k T →ₗ[k] (Additive M →ₗ[ℤ] k) :=
    { toFun := tangentFunctional E
      map_add' := by
        intro p q
        have h := congrArg (fun g : AddGroup (PointKernel T) => g.toAdd.add p q) t.group_law
        apply LinearMap.ext
        intro m
        refine (congrArg (fun x => tangentFunctional E x m) h).trans ?_
        change (pointCoordinates E (dualAlgebra k) (p.toMul.val * q.toMul.val) m.toMul).val.snd = _
        rw [pointCoordinates_mul]
        change (pointCoordinates E (dualAlgebra k) p.toMul.val m.toMul).val.fst *
            (pointCoordinates E (dualAlgebra k) q.toMul.val m.toMul).val.snd +
          (pointCoordinates E (dualAlgebra k) p.toMul.val m.toMul).val.snd *
            (pointCoordinates E (dualAlgebra k) q.toMul.val m.toMul).val.fst = _
        rw [tangentCoordinate_fst, tangentCoordinate_fst, one_mul, mul_one, add_comm]
        rfl
      map_smul' := by
        intro a p
        have h := congrFun (congrFun t.scalar_law a) p
        apply LinearMap.ext
        intro m
        refine (congrArg (fun x => tangentFunctional E x m) h).trans ?_
        change (pointCoordinates E (dualAlgebra k)
          (mapPoints (CommAlgCat.ofHom (dualNumberScale a)) p.toMul.val) m.toMul).val.snd = _
        rw [pointCoordinates_natural]
        change (dualNumberScale a _).snd = _
        rw [dualNumberScale, TrivSqZeroExt.snd_map]
        rfl }
  apply LinearEquiv.ofBijective L
  constructor
  · intro p q h
    apply Subtype.ext
    apply pointCoordinates_injective E (dualAlgebra k)
    apply MonoidHom.ext
    intro m
    apply Units.ext
    apply TrivSqZeroExt.ext
    · exact (tangentCoordinate_fst E p m).trans (tangentCoordinate_fst E q m).symm
    · exact LinearMap.congr_fun h (Additive.ofMul m)
  · intro f
    let a : M →* (DualNumber k)ˣ :=
      { toFun := fun m ↦ firstOrderUnit (f (Additive.ofMul m))
        map_one' := by
          change firstOrderUnit (f 0) = 1
          rw [map_zero]
          exact firstOrderUnits.map_zero
        map_mul' := fun m n ↦ by
          change firstOrderUnit (f (Additive.ofMul m + Additive.ofMul n)) = _
          rw [map_add]
          exact firstOrderUnits.map_add _ _ }
    obtain ⟨p, hp⟩ := pointCoordinates_surjective E (dualAlgebra k) a
    have hr : reduceTangentPoints T p = 1 := by
      apply pointCoordinates_injective E (CommAlgCat.of k k)
      rw [map_one]
      apply MonoidHom.ext
      intro m
      apply Units.ext
      change (pointCoordinates E _ (mapPoints (dualReduction k) p) m).val = 1
      rw [pointCoordinates_natural, hp]
      rfl
    refine ⟨⟨p, hr⟩, ?_⟩
    apply LinearMap.ext
    intro m
    change (pointCoordinates E (dualAlgebra k) p m.toMul).val.snd = f m
    rw [hp]
    rfl

end Coordinates

private theorem unitPoint_exponent (R : TestAlgebra k) (v : Rˣ) (n : IntegerCharacters.{u}) :
    (pointCoordinates (groupAlgebraPointsIso k IntegerCharacters) R (unitPoint R v) n) =
      v ^ integerExponent n := by
  apply Units.ext
  have h := pointsIso_spec IntegerCharacters R (unitCoordinates R v) n
  change (pointCoordinates (groupAlgebraPointsIso k IntegerCharacters) R (unitPoint R v) n).val = _ at h
  rw [h, unitCoordinates, MonoidAlgebra.lift_single, one_smul]
  rfl

/-- A split torus has the canonical scalar-extension comparison from cocharacters. -/
theorem scalarExtension : ScalarExtension.{u} := by
  intro k _ T _ hT t
  letI := t.lieRing
  letI := t.lieAlgebra
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} r
  obtain ⟨_, cochar, _, hcochar, _⟩ :=
    LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) r
  let d : Additive (Cocharacter T) ≃ₗ[ℤ] Module.Dual ℤ (Additive M) :=
    ((cochar.trans (cocharactersOfIso i)).toAdditive.toIntLinearEquiv.symm).trans (homToDual M)
  let E : (groupPointsFunctor k).obj T ≅ characterValuedPoints k M :=
    ((groupPointsFunctor k).mapIso i).symm ≪≫ groupAlgebraPointsIso k M
  let b := (Pi.basisFun ℤ (Fin r)).map (latticeCoordinates r).symm
  let B := (b.dualBasis.map d.symm).baseChange k
  let e : (k ⊗[ℤ] Additive (Cocharacter T)) ≃ₗ[k] Lie k T :=
    B.equivFun ≪≫ₗ b.constr k ≪≫ₗ (tangentLinearEquiv E t).symm
  have hcoords (f : M →* IntegerCharacters.{u}) (m : M) :
      tangentFunctional E (cocharacterTangent ((cocharactersOfIso i) (cochar f)))
        (Additive.ofMul m) = (integerExponent (f m) : k) := by
    change (pointCoordinates E (dualAlgebra k)
      (cocharacterPoint (cochar f ≫ i.hom) (dualAlgebra k) (infinitesimalUnit k)) m).val.snd = _
    have hc :
        pointCoordinates E (dualAlgebra k)
          (cocharacterPoint (cochar f ≫ i.hom) (dualAlgebra k) (infinitesimalUnit k)) =
        pointCoordinates (groupAlgebraPointsIso k M) (dualAlgebra k)
          (cocharacterPoint (cochar f) (dualAlgebra k) (infinitesimalUnit k)) := by
      change (E.hom.app _).hom
          (((groupPointsFunctor k).map (cochar f ≫ i.hom)).app _ (unitPoint _ _)) = _
      rw [Functor.map_comp, NatTrans.comp_app]
      change (pointCoordinates (groupAlgebraPointsIso k M) _) _
        = pointCoordinates (groupAlgebraPointsIso k M) _ _
      congr 1
      exact ConcreteCategory.congr_hom (((groupPointsFunctor k).mapIso i).app (dualAlgebra k)).hom_inv_id _
    rw [hc, hcochar f]
    unfold cocharacterPoint
    rw [show pointCoordinates (groupAlgebraPointsIso k M) (dualAlgebra k)
        (((groupPointsFunctor k).map (specGroupMap (groupAlgebraMap k f))).app (dualAlgebra k)
          (unitPoint (dualAlgebra k) (infinitesimalUnit k))) m =
        pointCoordinates (groupAlgebraPointsIso k IntegerCharacters) (dualAlgebra k)
          (unitPoint (dualAlgebra k) (infinitesimalUnit k)) (f m)
      from pointsIso_precompose f (dualAlgebra k) _ m, unitPoint_exponent, infinitesimalUnit_zpow]
  refine ⟨e, fun c ↦ ?_⟩
  have ht : e (1 ⊗ₜ[ℤ] Additive.ofMul c) = cocharacterTangent c := by
    obtain ⟨f, rfl⟩ := (cochar.trans (cocharactersOfIso i)).surjective c
    apply (tangentLinearEquiv E t).injective
    apply (b.constr k).symm.injective
    let c := (cochar.trans (cocharactersOfIso i)) f
    let x : k ⊗[ℤ] Additive (Cocharacter T) := 1 ⊗ₜ[ℤ] Additive.ofMul c
    have he : (tangentLinearEquiv E t) (e x) = b.constr k (B.equivFun x) :=
      (tangentLinearEquiv E t).apply_symm_apply _
    have he' : (b.constr k).symm ((tangentLinearEquiv E t) (e x)) = B.equivFun x :=
      (congrArg (b.constr k).symm he).trans ((b.constr k).symm_apply_apply _)
    funext j
    refine (congrFun he' j).trans ?_
    change B.repr x j = tangentFunctional E (cocharacterTangent c) (Additive.ofMul (b j).toMul)
    have hj := hcoords f (b j).toMul
    refine Eq.trans ?_ hj.symm
    change B.repr (1 ⊗ₜ[ℤ] Additive.ofMul c) j = (integerExponent (f (b j).toMul) : k)
    rw [Module.Basis.baseChange_repr_tmul, zsmul_one]
    change (b.dualBasis.repr (d (Additive.ofMul c)) j : k) = _
    rw [Module.Basis.dualBasis_repr]
    have hd : d (Additive.ofMul c) = homToDual M (Additive.ofMul f) :=
      congrArg (homToDual M) ((cochar.trans (cocharactersOfIso i)).toAdditive.toIntLinearEquiv.symm_apply_apply _)
    rw [hd]
    rfl
  exact congrArg (fun x : Lie k T => x.toMul.val) ht

/-- The simple indices of the attached datum label precisely the
simple root family used for representation weights. -/
private def simpleRootEquiv {P : Specs.Pinning.SplitBorelPair k} (D : Specs.Pinning.AttachedDatum P) :
    letI := D.comm
    Specs.RootWeightAction.SimpleRoot P.T P.B ≃ D.base.support := by
  letI := D.comm
  exact
    { toFun := fun α ↦ ⟨α.val, (D.simple_iff _).mpr α.property⟩
      invFun := fun α ↦ ⟨α.val, (D.simple_iff _).mp α.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- Integral generation and the tangent basis use the same actual simple coroots. -/
theorem basisAndLattice : BasisAndLattice.{u} := by
  classical
  intro k _ _ P hG D t
  letI := D.comm
  letI := t.lieRing
  letI := t.lieAlgebra
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  let Y := Additive (Cocharacter P.T.group)
  let Q := D.datum.rootDatum
  let e := simpleRootEquiv D
  let f := fun α : Specs.RootWeightAction.SimpleRoot P.T P.B ↦ Q.coroot α.val
  have hspan : Submodule.span ℤ (Set.range f) = Specs.SimplyConnectedLattice.corootLattice D := by
    have hr : Set.range f = Q.coroot '' (D.base.support : Set _) := by
      ext y
      constructor
      · rintro ⟨α, rfl⟩
        exact ⟨α.val, (e α).property, rfl⟩
      · rintro ⟨α, hα, rfl⟩
        exact ⟨e.symm ⟨α, hα⟩, rfl⟩
    rw [hr]
    exact D.base.span_int_coroot_support
  have hi : LinearIndependent ℤ f := D.base.linearIndepOn_coroot.comp e e.injective
  letI := Fintype.ofEquiv D.base.support e.symm
  have hc : Fintype.card (Specs.RootWeightAction.SimpleRoot P.T P.B) = Module.finrank ℤ Y := by
    rw [← finrank_span_eq_card hi, hspan]
    exact (semisimple_iff_corootFullRank P D).mp hG
  let v := fun α ↦ (1 : k) ⊗ₜ[ℤ] f α
  have hv : LinearIndependent k v := Module.Flat.linearIndependent_one_tmul hi
  have hs : Submodule.span k (Set.range v) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank' (hc.trans (Module.finrank_baseChange (R := k) (S := ℤ) (M' := Y)).symm)
  obtain ⟨lift, hlift⟩ := scalarExtension P.T.group P.split t
  let b := (Module.Basis.mk hv (ge_of_eq hs)).map lift
  refine ⟨hspan, b, fun α ↦ ?_⟩
  rw [show b α = lift (1 ⊗ₜ[ℤ] f α) by simp [b, v]]
  exact hlift (Additive.toMul (f α))

/-- Torus points commute over every test algebra, and a closed immersion
is injective on the identity tangent kernels. -/
theorem lieEmbedding : LieEmbedding.{u} := by
  intro k _ G T hT t s
  letI := t.lieRing
  letI := t.lieAlgebra
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : IsAffine G.val.X.left := G.property.1
  letI := T.isClosedImmersion
  letI : IsAffine T.group.X.left := isAffine_of_isAffineHom T.inclusion.hom.hom.left
  obtain ⟨hcomm, _⟩ := RootData.CharacterPairing.perfectCharacterPairing T.group hT
  letI := hcomm
  refine ⟨?_, ?_⟩
  · intro x y
    have hc : InfinitesimalCommutator.commutator ((groupPointsFunctor k).obj T.group) x y = 1 := by
      let R := CommAlgCat.of k (InfinitesimalCommutator.TwoVariables k)
      let a : Points T.group.X R :=
        mapPoints (CommAlgCat.ofHom (InfinitesimalCommutator.liftS k)) x.toMul.val
      let b : Points T.group.X R :=
        mapPoints (CommAlgCat.ofHom (InfinitesimalCommutator.liftT k)) y.toMul.val
      change a * b * a⁻¹ * b⁻¹ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm a b)
    have hb : t.lieRing.toBracket.bracket x y = (0 : PointKernel T.group) := by
      apply Subtype.ext
      apply point_liftST_injective T.group
      exact (t.commutator_law x y).trans (hc.trans (map_one _).symm)
    exact hb
  · obtain ⟨a, ha⟩ := identityDifferentialLieHom k T.group G.val T.inclusion t s
    haveI : Mono T.inclusion.hom.hom :=
      (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono T.inclusion.hom.hom.left))
    exact ⟨a, fun x y h ↦ differential_injective T.inclusion ((ha x).symm.trans (h.trans (ha y))), ha⟩

end

end LinearAlgebraicGroups.Representation.SimpleCorootTangents
