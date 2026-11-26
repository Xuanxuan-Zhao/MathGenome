import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.ParabolicLineWeights
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ChevalleyLine
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Orthogonality
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PrimitiveLine
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Batteries.Tactic.OpenPrivate

open CategoryTheory AlgebraicGeometry Opposite WithConv
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj Kronecker TensorProduct
open CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

universe u

namespace LinearAlgebraicGroups.Representation.ParabolicLineWeights

open LinearAlgebraicGroups.Specs
open Specs.CharacterDescent (Character)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue)
open Specs.RootWeightAction (Representation IsPrimitive act extendVector
  mem_fixedSpace mem_weightSpace)
open Specs.ParabolicLineWeights

noncomputable section

variable {k I J : Type u} [Field k] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {G : AffineAlgebraicGroup k} {T B : ClosedSubgroup G.val}
variable {U : ClosedSubgroup B.group}

open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open LinearAlgebraicGroups.CocharacterDynamics (unitPoint)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

open private unitPointHom unitPointHom_apply unitEquiv unitEquiv_unitPoint gm_baseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

open private pointsIso_spec
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private characterValue_mul characterValue_one act_one act_mul act_extend_natural weylTransport
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction

private theorem characterValue_unit {H : GroupScheme k} (χ : Character H)
    (R : TestAlgebra k) (t : GroupPoints H R) :
    characterValue χ R t = (unitEquiv R (t ≫ χ.hom.hom) : R) := by
  let A := groupAlgebra k IntegerCharacters
  let e := hopfSpecPointIso A
  let z : GroupPoints (specGroup A) R := t ≫ χ.hom.hom
  let x := e.inv.app R z
  have hx : e.hom.app R x = z := (e.app R).inv_hom_id_apply z
  change _ = (unitEquiv R z : R)
  rw [← hx]
  have hf : ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      (t ≫ χ.hom.hom)).unop.hom = x.ofConv := by
    have hx' : (testSpec k).map (CommAlgCat.ofHom x.ofConv).op = t ≫ χ.hom.hom := hx
    rw [← hx', Functor.FullyFaithful.preimage_map]
    rfl
  change _ = _
  unfold characterValue
  dsimp only
  rw [hf]
  exact (pointsIso_spec IntegerCharacters R x.ofConv integerGenerator).symm

private theorem characterValue_restrict {H L : GroupScheme k} (f : H ⟶ L)
    (χ : Character L) (R : TestAlgebra k) (t : GroupPoints H R) :
    characterValue (f ≫ χ) R t = characterValue χ R (t ≫ f.hom.hom) := by
  simp only [characterValue_unit]
  congr 2

private def tensorMatrices (R : TestAlgebra k) :
    Matrix.GeneralLinearGroup I R × Matrix.GeneralLinearGroup J R →*
      Matrix.GeneralLinearGroup (I × J) R :=
  (Units.map
    { toFun := fun p : Matrix I I R × Matrix J J R ↦ p.1 ⊗ₖ p.2
      map_one' := Matrix.one_kronecker_one
      map_mul' := fun a b ↦ Matrix.mul_kronecker_mul a.1 b.1 a.2 b.2 }).comp
    (MulEquiv.prodUnits (M := Matrix I I R) (N := Matrix J J R)).symm.toMonoidHom

/-- Tensor product of the two rational actions in the product basis. -/
private def tensorRepresentation (ρ : Representation G.val I) (σ : Representation G.val J) :
    Representation G.val (I × J) where
  app R := GrpCat.ofHom ((tensorMatrices R).comp ((ρ.app R).hom.prod (σ.app R).hom))
  naturality R S a := by
    apply GrpCat.ext
    intro g
    have hρ := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ρ.naturality a)) g
    have hσ := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (σ.naturality a)) g
    apply Units.ext
    ext ij ij'
    change (ρ.app S (mapPoints a g)).val ij.1 ij'.1 *
        (σ.app S (mapPoints a g)).val ij.2 ij'.2 =
      a.hom ((ρ.app R g).val ij.1 ij'.1 * (σ.app R g).val ij.2 ij'.2)
    rw [map_mul]
    congr 1
    · exact congrArg (fun m : Matrix.GeneralLinearGroup I S ↦ m.val ij.1 ij'.1) hρ
    · exact congrArg (fun m : Matrix.GeneralLinearGroup J S ↦ m.val ij.2 ij'.2) hσ

private theorem act_tensor (ρ : Representation G.val I) (σ : Representation G.val J)
    (R : TestAlgebra k) (g : GroupPoints G.val R) (v : I → R) (w : J → R) (ij : I × J) :
    act (tensorRepresentation ρ σ) R g (fun h ↦ v h.1 * w h.2) ij =
      act ρ R g v ij.1 * act σ R g w ij.2 := by
  change ∑ h : I × J, ((ρ.app R g).val ij.1 h.1 * (σ.app R g).val ij.2 h.2) *
      (v h.1 * w h.2) =
    (∑ i : I, (ρ.app R g).val ij.1 i * v i) * ∑ j : J, (σ.app R g).val ij.2 j * w j
  rw [Finset.sum_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

private theorem primitive_tensor (ρ : Representation G.val I) (σ : Representation G.val J)
    {χ ψ : Character T.group} {v : I → k} {w : J → k}
    (hv : IsPrimitive ρ T B U χ v) (hw : IsPrimitive σ T B U ψ w) :
    IsPrimitive (tensorRepresentation ρ σ) T B U (χ * ψ) (fun ij ↦ v ij.1 * w ij.2) := by
  have extend_tensor (R : TestAlgebra k) :
      extendVector R (fun ij : I × J ↦ v ij.1 * w ij.2) =
        fun ij ↦ extendVector R v ij.1 * extendVector R w ij.2 :=
    funext fun ij ↦ map_mul (algebraMap k R) _ _
  refine ⟨?_, mem_fixedSpace.mpr ?_, mem_weightSpace.mpr ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv.1
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := Function.ne_iff.mp hw.1
    exact fun h ↦ mul_ne_zero hi hj (congrFun h (i, j))
  · intro R g
    funext ij
    rw [extend_tensor]
    rw [act_tensor ρ σ R (g ≫ (U.inclusion ≫ B.inclusion).hom.hom)
      (extendVector R v) (extendVector R w) ij]
    rw [mem_fixedSpace.mp hv.2.1, mem_fixedSpace.mp hw.2.1]
  · intro R t
    funext ij
    rw [extend_tensor]
    rw [act_tensor ρ σ R (t ≫ T.inclusion.hom.hom)
      (extendVector R v) (extendVector R w) ij]
    rw [mem_weightSpace.mp hv.2.2, mem_weightSpace.mp hw.2.2]
    simp only [characterValue_mul, Pi.smul_apply, smul_eq_mul]
    ac_rfl

private def trivialRepresentation : Representation G.val (ULift.{u} Unit) where
  app _ := GrpCat.ofHom 1
  naturality R S a := by
    apply GrpCat.ext
    intro g
    change (1 : Matrix.GeneralLinearGroup (ULift.{u} Unit) S) = (StandardGroups.generalLinearPoints
      k (ULift.{u} Unit)).map a 1
    exact ((StandardGroups.generalLinearPoints k (ULift.{u} Unit)).map a).hom.map_one.symm

private theorem primitive_trivial :
    IsPrimitive (trivialRepresentation (G := G)) T B U 1 (fun _ ↦ 1) := by
  have one_action (R : TestAlgebra k) (g : Points G.val.X R) :
      act (trivialRepresentation (G := G)) R g
        (extendVector R (fun _ ↦ 1)) = extendVector R (fun _ ↦ 1) :=
    Matrix.one_mulVec _
  refine ⟨fun h ↦ one_ne_zero (congrFun h ⟨()⟩), mem_fixedSpace.mpr ?_,
    mem_weightSpace.mpr ?_⟩
  · intro R g
    exact one_action R _
  · intro R t
    rw [one_action, characterValue_one, one_smul]

private def HasPrimitive (χ : Character T.group) : Prop :=
  ∃ (L : Type u) (_ : Fintype L) (_ : DecidableEq L)
    (ρ : Representation G.val L) (v : L → k), IsPrimitive ρ T B U χ v

private theorem hasPrimitive_one : HasPrimitive (U := U) (T := T) 1 :=
  ⟨_, inferInstance, inferInstance, trivialRepresentation, _, primitive_trivial⟩

private theorem hasPrimitive_mul {χ ψ : Character T.group}
    (hχ : HasPrimitive (U := U) χ) (hψ : HasPrimitive (U := U) ψ) :
    HasPrimitive (U := U) (χ * ψ) := by
  obtain ⟨L, fL, dL, ρ, v, hv⟩ := hχ
  obtain ⟨M, fM, dM, σ, w, hw⟩ := hψ
  exact ⟨L × M, inferInstance, inferInstance, tensorRepresentation ρ σ,
    _, primitive_tensor ρ σ hv hw⟩

private theorem hasPrimitive_prod {A : Type*} (s : Finset A)
    (χ : A → Character T.group) (h : ∀ i ∈ s, HasPrimitive (U := U) (χ i)) :
    HasPrimitive (U := U) (∏ i ∈ s, χ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (hasPrimitive_one (U := U) (T := T))
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact hasPrimitive_mul (h i (Finset.mem_insert_self _ _))
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

private theorem hasPrimitive_pow {χ : Character T.group} (h : HasPrimitive (U := U) χ) (n : ℕ) :
    HasPrimitive (U := U) (χ ^ n) := by
  induction n with
  | zero => simpa using (hasPrimitive_one (U := U) (T := T))
  | succ n ih =>
    rw [pow_succ]
    exact hasPrimitive_mul ih h

omit [Fintype I] [DecidableEq I] in
private theorem scalar_unique {v : I → k} (hv : v ≠ 0) (R : TestAlgebra k)
    {a b : R} (h : a • extendVector R v = b • extendVector R v) : a = b := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
  have eq := congrFun h i
  change a * algebraMap k R (v i) = b * algebraMap k R (v i) at eq
  apply (IsUnit.mul_left_inj (hi.isUnit.map (algebraMap k R))).mp
  exact eq

private def lineScalar {P : ClosedSubgroup G.val} {ρ : Representation G.val I}
    {v : I → k} (hv : v ≠ 0) (hP : HasLineStabilizer ρ v P)
    (R : TestAlgebra k) : GroupPoints P.group R →* Rˣ where
  toFun p := Classical.choose ((hP R (p ≫ P.inclusion.hom.hom)).mpr ⟨p, rfl⟩)
  map_one' := by
    apply Units.ext
    apply scalar_unique hv R
    have eq := Classical.choose_spec ((hP R ((1 : GroupPoints P.group R) ≫
      P.inclusion.hom.hom)).mpr ⟨1, rfl⟩)
    refine eq.symm.trans ?_
    rw [MonObj.one_comp, act_one, Units.val_one, one_smul]
  map_mul' p q := by
    apply Units.ext
    apply scalar_unique hv R
    let s (p : GroupPoints P.group R) :=
      Classical.choose ((hP R (p ≫ P.inclusion.hom.hom)).mpr ⟨p, rfl⟩)
    have hs (p : GroupPoints P.group R) : act ρ R (p ≫ P.inclusion.hom.hom) (extendVector R v) =
        (s p : R) • extendVector R v :=
      Classical.choose_spec ((hP R (p ≫ P.inclusion.hom.hom)).mpr ⟨p, rfl⟩)
    change (s (p * q) : R) • extendVector R v = (↑(s p * s q) : R) • extendVector R v
    refine (hs (p * q)).symm.trans ?_
    have hact : act ρ R ((p * q) ≫ P.inclusion.hom.hom) (extendVector R v) =
        act ρ R (p ≫ P.inclusion.hom.hom) (act ρ R (q ≫ P.inclusion.hom.hom)
          (extendVector R v)) := by
      rw [MonObj.mul_comp, act_mul]
    rw [hact, hs q]
    let M := RootWeightAction.actLinear ρ R (p ≫ P.inclusion.hom.hom)
    change M ((s q : R) • extendVector R v) = (↑(s p * s q) : R) • extendVector R v
    have hp : M (extendVector R v) = (s p : R) • extendVector R v := hs p
    rw [M.map_smul, hp, smul_smul, mul_comm]
    rfl

private theorem lineScalar_apply {P : ClosedSubgroup G.val} {ρ : Representation G.val I}
    {v : I → k} (hv : v ≠ 0) (hP : HasLineStabilizer ρ v P)
    (R : TestAlgebra k) (p : GroupPoints P.group R) :
    act ρ R (p ≫ P.inclusion.hom.hom) (extendVector R v) =
      (lineScalar hv hP R p : R) • extendVector R v :=
  Classical.choose_spec ((hP R (p ≫ P.inclusion.hom.hom)).mpr ⟨p, rfl⟩)

private theorem lineScalar_natural {P : ClosedSubgroup G.val} {ρ : Representation G.val I}
    {v : I → k} (hv : v ≠ 0) (hP : HasLineStabilizer ρ v P)
    {R S : TestAlgebra k} (a : R ⟶ S) (p : GroupPoints P.group R) :
    lineScalar hv hP S (mapPoints a p) =
        Units.map a.hom.toMonoidHom (lineScalar hv hP R p) := by
  apply Units.ext
  apply scalar_unique hv S
  rw [← lineScalar_apply hv hP S (mapPoints a p)]
  funext i
  have he : act ρ S (mapPoints a p ≫ P.inclusion.hom.hom) (extendVector S v) i =
    a.hom (act ρ R (p ≫ P.inclusion.hom.hom) (extendVector R v) i) := by
    have hmap : mapPoints a (p ≫ P.inclusion.hom.hom) =
        mapPoints a p ≫ P.inclusion.hom.hom := (Category.assoc _ _ _).symm
    rw [← hmap, act_extend_natural]
  rw [he, lineScalar_apply hv hP R p, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    map_mul]
  change _ = a.hom _ * algebraMap k S (v i)
  rw [show extendVector R v i = algebraMap k R (v i) from rfl, a.hom.commutes]

private theorem lineCharacter {P : ClosedSubgroup G.val} {ρ : Representation G.val I}
    {v : I → k} (hv : v ≠ 0) (hP : HasLineStabilizer ρ v P) :
    ∃ χ : Character P.group,
      ∀ (R : TestAlgebra k) (p : GroupPoints P.group R),
        act ρ R (p ≫ P.inclusion.hom.hom) (extendVector R v) =
          characterValue χ R p • extendVector R v := by
  let E : AffineAlgebraicGroup k := closedSubgroupAlgebraicGroup P
  let A := groupAlgebra k IntegerCharacters
  let φ : (groupPointsFunctor k).obj P.group ⟶ (groupPointsFunctor k).obj (specGroup A) :=
    { app := fun R ↦ GrpCat.ofHom ((unitPointHom R).comp (lineScalar hv hP R))
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro p
        change unitPointHom S (lineScalar hv hP S (mapPoints a p)) =
          mapPoints a (unitPointHom R (lineScalar hv hP R p))
        rw [lineScalar_natural hv hP, unitPointHom_apply, unitPointHom_apply]
        exact (LinearAlgebraicGroups.CocharacterDynamics.mapPoints_unitPoint a
          (lineScalar hv hP R p)).symm }
  let e := LinearAlgebraicGroups.groupHomEquiv P.group (specGroup A) E.property.1
  let χ := e.symm φ
  refine ⟨χ, fun R p ↦ ?_⟩
  have he : p ≫ χ.hom.hom = unitPoint R (lineScalar hv hP R p) := by
    have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom
      (congrArg (fun f ↦ f.app R) (e.apply_symm_apply φ))) p
    change p ≫ χ.hom.hom = unitPointHom R (lineScalar hv hP R p) at h
    rwa [unitPointHom_apply] at h
  rw [lineScalar_apply hv hP R p, characterValue_unit, he, unitEquiv_unitPoint]

open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.SchemeDerivedGroup (IsSubgroupOf)

private theorem integerCharacters_fg : Group.FG (IntegerCharacters.{u}) :=
  let e : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
  Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

private theorem multiplicativeGroup_isOfMultiplicativeType :
    (CharacterDescent.multiplicativeTypeSpecFunctor k).essImage
      (Specs.DiagonalizableGroups.diagonalGroup (k := k) IntegerCharacters) := by
  let S := Specs.DiagonalizableGroups.diagonalGroup (k := k) IntegerCharacters
  let M : Specs.DiagonalizableGroups.FGAbelianGroup.{u} :=
    ⟨CommGrpCat.of IntegerCharacters, integerCharacters_fg⟩
  obtain ⟨e, _⟩ := gm_baseChange k k
  exact (LinearAlgebraicGroups.CharacterDescent.multiplicativeTypeGroupCriterion S).mpr
    ⟨k, inferInstance, inferInstance, inferInstance, M, ⟨e.symm⟩⟩

private theorem primitive_of_line {P : ClosedSubgroup G.val} {ρ : Representation G.val I}
    {v : I → k} (hv : v ≠ 0) (hP : HasLineStabilizer ρ v P)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U)
    (hTB : IsSubgroupOf T B) (hBP : IsSubgroupOf B P) :
    ∃ χ : Character T.group, IsPrimitive ρ T B U χ v := by
  obtain ⟨j, hj⟩ := hTB
  obtain ⟨l, hl⟩ := hBP
  obtain ⟨χ, hχ⟩ := lineCharacter hv hP
  let e : U.group ⟶ P.group := U.inclusion ≫ l
  let D := Specs.DiagonalizableGroups.diagonalGroup (k := k) IntegerCharacters
  let A := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup B) U
  let f : A.val ⟶ D.val := e ≫ χ
  have hzero : e ≫ χ = 0 :=
    LinearAlgebraicGroups.Unipotent.homFromUnipotentToMultiplicativeType
      A D f hU.2.1 multiplicativeGroup_isOfMultiplicativeType
  refine ⟨(j ≫ l) ≫ χ, hv, mem_fixedSpace.mpr ?_, mem_weightSpace.mpr ?_⟩
  · intro R g
    have hg : (g ≫ e.hom.hom) ≫ P.inclusion.hom.hom =
        g ≫ (U.inclusion ≫ B.inclusion).hom.hom := by
      have he : e ≫ P.inclusion = U.inclusion ≫ B.inclusion := by
        dsimp only [e]
        rw [Category.assoc, hl]
      rw [Category.assoc]
      exact congrArg (fun f : U.group ⟶ G.val ↦ g ≫ f.hom.hom) he
    have hval : characterValue χ R (g ≫ e.hom.hom) = 1 := by
      rw [← characterValue_restrict, hzero]
      exact characterValue_one R g
    simpa only [hg, hval, one_smul] using hχ R (g ≫ e.hom.hom)
  · intro R t
    have ht : (t ≫ (j ≫ l).hom.hom) ≫ P.inclusion.hom.hom =
        t ≫ T.inclusion.hom.hom := by
      have he : (j ≫ l) ≫ P.inclusion = T.inclusion := by rw [Category.assoc, hl, hj]
      rw [Category.assoc]
      exact congrArg (fun f : T.group ⟶ G.val ↦ t ≫ f.hom.hom) he
    simpa only [ht, characterValue_restrict] using hχ R (t ≫ (j ≫ l).hom.hom)

open private coordinateLine_iff_unit from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ChevalleyLine

private theorem exists_line_stabilizer (P : ClosedSubgroup G.val) :
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
      (ρ : Representation G.val I) (v : I → k), v ≠ 0 ∧ HasLineStabilizer ρ v P := by
  classical
  obtain ⟨I, fI, dI, i, L, e, f, h⟩ := LinearAlgebraicGroups.chevalleyLine k G P
  let ρ := (groupPointsFunctor k).map f ≫ e.hom
  let v : I → k := Pi.single i 1
  refine ⟨I, fI, dI, ρ, v, ?_, ?_⟩
  · intro hz
    simpa [v] using congrFun hz i
  · intro R g
    rw [← h R g, coordinateLine_iff_unit]
    have he : extendVector R v = Pi.single i (1 : R) := by
      funext j
      by_cases hj : j = i <;> simp [v, extendVector, hj]
    rw [he]
    have heval (a : Rˣ) (j : I) :
        act ρ R g (Pi.single i (1 : R)) j = ((a : R) • Pi.single i (1 : R)) j ↔
          (ρ.app R g).val j i = if j = i then (a : R) else 0 := by
      by_cases hj : j = i <;> simp [RootWeightAction.act, hj, Matrix.mulVec_single]
    simp only [funext_iff, heval, ρ, NatTrans.comp_app, GrpCat.comp_apply]

open Specs.AbstractPairing (Datum Root)
open Specs.BruhatOrbitParametrization (IsRepresentative)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.DatumAndWeyl (Identification)
open Specs.GeometricRadicals (IsSplitTorus IsReductive)
open Specs.RootWeightAction (weightSpace IsDominant SimpleRoot)
open Specs.SimpleRoots (evaluate IsBaseFor)
open Specs.StandardParabolicLevi (StandardParabolic HasFace parabolicWeylGroup)
open Specs.StandardParabolics (HasWeylIndices)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.CharacterDescent (Cocharacter)
open private simple_in_parabolicWeylGroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolics

section RootDatum

variable [IsCommMonObj T.group.X] {D : Datum T}
variable {b : D.rootDatum.Base}

private theorem reflection_fixes_iff (a : Root T) (x : Additive (Character T.group)) :
    (RootPairing.weylGroup.ofIdx D.rootDatum a).val.weightEquiv x = x ↔
      D.rootDatum.coroot' a x = 0 := by
  letI := D.freeCharacters
  change (RootPairing.Equiv.reflection D.rootDatum a).weightEquiv x = x ↔ _
  rw [RootPairing.Equiv.reflection_weightEquiv, RootPairing.reflection_apply, sub_eq_self,
    smul_eq_zero]
  exact or_iff_left (D.rootDatum.ne_zero a)

private theorem omitted_reflection_not_mem {c : Cocharacter T.group} (i : b.support)
    (h : HasFace b (omittedSimpleRoot b i) c) :
    RootPairing.weylGroup.ofIdx D.rootDatum i.val ∉
      parabolicWeylGroup D (omittedSimpleRoot b i) := by
  intro hi
  exact ((simple_in_parabolicWeylGroup h i.property).mp hi).2 (Set.mem_singleton i.val)

private theorem baseSimpleRoot {c : Cocharacter T.group} (hpos : positiveRoots T c = subgroupRoots T B)
    (hb : IsBaseFor D.rootDatum (evaluate D c) b) (a : Root T) :
    a ∈ b.support ↔ ∃ x : SimpleRoot T B, x.val = a := by
  have roots (r : Root T) :
      r ∈ Specs.SimpleRoots.positive D.rootDatum (evaluate D c) ↔ r ∈ subgroupRoots T B := by
    rw [← hpos]
    change 0 < D.rootDatum.toLinearMap (D.rootDatum.root r) (Additive.ofMul c) ↔ _
    rw [D.root_eq, D.pairing_eq]
    rfl
  rw [hb.simple_iff a, roots]
  simp only [roots, D.root_eq]
  constructor
  · rintro ⟨ha, hind⟩
    exact ⟨⟨a, ha, hind⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.property

private theorem rationalCorootPairing_character (a : Root T) (χ : Character T.group) :
    rationalCorootPairing D a (rationalCharacter χ) =
      (D.rootDatum.coroot' a (Additive.ofMul χ) : ℚ) := by
  simp [rationalCorootPairing, rationalCharacter, Algebra.smul_def]

private theorem rationalCharacter_injective (D : Datum T) :
    Function.Injective (rationalCharacter (T := T)) := by
  letI := D.freeCharacters
  let b := Module.Free.chooseBasis ℤ (Additive (Character T.group))
  intro χ ψ h
  apply b.repr.injective
  ext i
  have he := congrArg (fun x ↦ (b.baseChange ℚ).repr x i) h
  change b.repr (Additive.ofMul χ) i = b.repr (Additive.ofMul ψ) i
  simp only [rationalCharacter, Module.Basis.baseChange_repr_tmul,
    ← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul, mul_one] at he
  exact Int.cast_injective he

omit [IsCommMonObj T.group.X] in
private theorem rationalCharacter_pow (χ : Character T.group) (m : ℕ) :
    rationalCharacter (χ ^ m) = (m : ℚ) • rationalCharacter χ := by
  change ((TensorProduct.mk ℤ ℚ _) 1) (m • Additive.ofMul χ) = _
  rw [map_nsmul, Nat.cast_smul_eq_nsmul]
  rfl

omit [IsCommMonObj T.group.X] in
private theorem rationalCharacter_prod {A : Type*} (s : Finset A) (χ : A → Character T.group) :
    rationalCharacter (∏ i ∈ s, χ i) = ∑ i ∈ s, rationalCharacter (χ i) := by
  unfold rationalCharacter
  rw [ofMul_prod]
  exact map_sum ((TensorProduct.mk ℤ ℚ (Additive (Character T.group))) 1) _ _

open scoped Classical in
/-- Once the coroots separate rational characters, the normalized weights of
the parabolic lines form the fundamental system and their tensor products give
the required integral multiples of each dominant weight. -/
private theorem weights_and_tensor_powers
    (P : b.support → ClosedSubgroup G.val)
    (L : ∀ i : b.support, ParabolicLine (T := T) U (P i))
    (hsep : ∀ x, (∀ j : b.support, rationalCorootPairing D j.val x = 0) → x = 0)
    (d : b.support → ℕ) (hpair : ∀ i j : b.support, D.rootDatum.coroot' j.val (Additive.ofMul (L i).weight) =
      if i = j then (d i : ℤ) else 0)
    (lam : Character T.group)
    (hlam : ∀ j : b.support, 0 ≤ D.rootDatum.coroot' j.val (Additive.ofMul lam))
    (m : ℕ) (hm : ∀ j, d j ∣ m) :
    HasPrimitive (U := U) (lam ^ m) := by
  classical
  let a (i : b.support) := (D.rootDatum.coroot' i.val (Additive.ofMul lam)).toNat
  have ha (i : b.support) :
      (a i : ℤ) = D.rootDatum.coroot' i.val (Additive.ofMul lam) :=
    Int.toNat_of_nonneg (hlam i)
  let ex (i : b.support) := m / d i * a i
  let χ (i : b.support) := (L i).weight ^ ex i
  have hp : HasPrimitive (U := U) (∏ i : b.support, χ i) := by
    apply hasPrimitive_prod Finset.univ χ
    intro i _
    letI := (L i).finite
    letI := (L i).decidable
    exact hasPrimitive_pow ⟨(L i).index, (L i).finite, (L i).decidable, (L i).representation,
      (L i).vector, (L i).primitive⟩ (ex i)
  suffices (∏ i : b.support, χ i) = lam ^ m by rwa [this] at hp
  apply rationalCharacter_injective D
  apply sub_eq_zero.mp
  apply hsep
  intro j
  rw [map_sub, rationalCharacter_prod, map_sum,
    rationalCharacter_pow, (rationalCorootPairing D j.val).map_smul, rationalCorootPairing_character]
  have hterm (i : b.support) :
      rationalCorootPairing D j.val (rationalCharacter (χ i)) =
        (ex i : ℚ) • ((if i = j then (d i : ℤ) else 0 : ℤ) : ℚ) := by
    dsimp only [χ]
    rw [rationalCharacter_pow, (rationalCorootPairing D j.val).map_smul,
      rationalCorootPairing_character, hpair]
  simp only [hterm]
  have hsum : (∑ i : b.support, (ex i : ℚ) • ((if i = j then (d i : ℤ) else 0 : ℤ) : ℚ)) =
      (ex j : ℚ) * (d j : ℚ) := by
    rw [Finset.sum_eq_single j]
    · simp [smul_eq_mul]
    · intro i _ hne
      simp [hne]
    · simp
  rw [hsum, sub_eq_zero, smul_eq_mul, ← ha]
  have hex : ex j * d j = m * a j := by
    change (m / d j * a j) * d j = m * a j
    rw [mul_right_comm, Nat.div_mul_cancel (hm j)]
  exact_mod_cast hex

open scoped Classical in
private theorem normalized_weights (P : b.support → ClosedSubgroup G.val)
    (L : ∀ i : b.support, ParabolicLine (T := T) U (P i))
    (d : b.support → ℕ) (hd : ∀ i, 0 < d i)
    (hpair : ∀ i j : b.support, D.rootDatum.coroot' j.val (Additive.ofMul (L i).weight) =
      if i = j then (d i : ℤ) else 0) :
    ∃ ω : b.support → RationalCharacters T,
      (∀ i j, rationalCorootPairing D j.val (ω i) = if i = j then 1 else 0) ∧
      ∀ i, rationalCharacter (L i).weight = (d i : ℚ) • ω i := by
  let ω i := (d i : ℚ)⁻¹ • rationalCharacter (L i).weight
  have hne (i : b.support) : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
  refine ⟨ω, fun i j ↦ ?_, fun i ↦ (smul_inv_smul₀ (hne i) _).symm⟩
  change rationalCorootPairing D j.val ((d i : ℚ)⁻¹ • rationalCharacter (L i).weight) = _
  rw [(rationalCorootPairing D j.val).map_smul, rationalCorootPairing_character, hpair]
  by_cases h : i = j
  · subst j
    simp [smul_eq_mul, hne i]
  · simp [h]

end RootDatum

open Specs.CyclicHighestWeight (orbitSpan)
open Specs.PrimitiveLine (IsEquivariant)
open Specs.RootWeightAction (DominanceLE)
open private orbit_properties fromCoaction toCoaction inclusion_equivariant
  act_eq_scalar_iff stable_map orbit_stable from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PrimitiveLine
open private affineBaseTerminal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint

private theorem equivariant_scalar_iff {ρ : Representation G.val I} {σ : Representation G.val J}
    {f : (I → k) →ₗ[k] (J → k)} (hf : IsEquivariant ρ σ f)
    (hi : Function.Injective f) (R : TestAlgebra k) (g : GroupPoints G.val R)
    (x : I → k) (a : R) :
    act ρ R g (extendVector R x) = a • extendVector R x ↔
      act σ R g (extendVector R (f x)) = a • extendVector R (f x) := by
  refine (act_eq_scalar_iff ρ R g x a).trans
    (Iff.trans ?_ (act_eq_scalar_iff σ R g (f x) a).symm)
  constructor
  · intro h ℓ
    rw [← hf, h ℓ, map_smul]
  · intro h ℓ
    apply hi
    rw [hf, h ℓ, map_smul]

/-- Restrict a Chevalley line to its cyclic submodule, retaining its stabilizer
on all test algebras. -/
private theorem exists_cyclic_parabolic_line (P : ClosedSubgroup G.val)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U)
    (hTB : IsSubgroupOf T B) (hBP : IsSubgroupOf B P)
    (htop : ∀ {L : Type u} [Fintype L] [DecidableEq L] (τ : Representation G.val L)
      (χ : Character T.group) (v : L → k), IsPrimitive τ T B U χ v →
      orbitSpan τ (𝟙 G.val.X) v = ⊤ → weightSpace τ T χ = Submodule.span k {v}) :
    Nonempty (ParabolicLine (T := T) U P) := by
  classical
  obtain ⟨I, fI, dI, ρ, v, hv, hP⟩ := exists_line_stabilizer P
  obtain ⟨χ, hχ⟩ := primitive_of_line hv hP hU hTB hBP
  let A₀ : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  let A := coordinateHopf A₀
  let e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val :=
    hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso
      ((affineGroupInclusion k).mapIso (coordinateHopfSpecIso A₀))
  have hC : Specs.CyclicHighestWeight.CoactionComparison.{u} :=
    LinearAlgebraicGroups.Representation.CyclicHighestWeight.cyclicHighestWeight.1
  let C := orbitSpan ρ (𝟙 G.val.X) v
  obtain ⟨hmem, hsub, _⟩ := orbit_properties hC ρ A e v
  obtain ⟨δ, hδ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction
    (toCoaction e (Pi.basisFun k I) ρ) C).mp hsub
  let L := ULift.{u} (Fin (Module.finrank k C))
  let b : Module.Basis L k C := (Module.finBasis k C).reindex Equiv.ulift.symm
  let σ := fromCoaction e b δ
  let f := C.subtype.comp b.equivFun.symm.toLinearMap
  let x := b.equivFun ⟨v, hmem⟩
  have hx : f x = v := by simp [f, x]
  have he : IsEquivariant σ ρ f := inclusion_equivariant e ρ C b δ hδ
  have hi : Function.Injective f := Subtype.val_injective.comp b.equivFun.symm.injective
  have hscalar (R : TestAlgebra k) (g : GroupPoints G.val R) (a : R) :=
    equivariant_scalar_iff he hi R g x a
  simp only [hx] at hscalar
  have hprim : IsPrimitive σ T B U χ x := by
    refine ⟨fun h ↦ hv (hx.symm.trans (h ▸ f.map_zero)), mem_fixedSpace.mpr ?_,
      mem_weightSpace.mpr ?_⟩
    · intro R g
      simpa only [one_smul] using (hscalar R _ 1).mpr
        (by simpa only [one_smul] using mem_fixedSpace.mp hχ.2.1 R g)
    · intro R t
      exact (hscalar R _ _).mpr (mem_weightSpace.mp hχ.2.2 R t)
  have hgen : orbitSpan σ (𝟙 G.val.X) x = ⊤ := by
    let N := orbitSpan σ (𝟙 G.val.X) x
    have hxN := (orbit_properties hC σ A e x).1
    have hvN : v ∈ N.map f := Submodule.mem_map.mpr ⟨x, hxN, hx⟩
    have hle : C ≤ N.map f := (stable_map he N (orbit_stable hC σ A e x)) v hvN
    apply top_unique
    intro z _
    have hz : f z ∈ C := (b.equivFun.symm z).property
    obtain ⟨z', hz', heq⟩ := Submodule.mem_map.mp (hle hz)
    exact hi heq ▸ hz'
  refine ⟨⟨L, inferInstance, inferInstance, σ, x, χ, hprim, hgen, htop σ χ x hprim hgen, ?_⟩⟩
  intro R g
  exact (exists_congr fun a : Rˣ ↦ hscalar R g (a : R)).trans (hP R g)

section Pairings

variable [IsCommMonObj T.group.X] {D : Datum T} {b : D.rootDatum.Base}

/-- The action of a representative on the highest line detects exactly the
vanishing of the corresponding simple-coroot pairing. -/
private theorem simple_coroot_of_line (W : Identification D) (hT : IsSplitTorus T.group)
    {c : Cocharacter T.group}
    (hpositive : ∀ a : SimpleRoot T B, 0 < evaluate D c (Additive.ofMul a.val.val))
    (P : ClosedSubgroup G.val) (ρ : Representation G.val I) (χ : Character T.group) (v : I → k)
    (hv : IsPrimitive ρ T B U χ v) (hline : weightSpace ρ T χ = Submodule.span k {v})
    (hmax : ∀ nu, nu ≠ χ → weightSpace ρ T nu ≠ ⊥ → DominanceLE T B nu χ)
    (i : b.support) (hroot : 0 < evaluate D c (D.rootDatum.root i.val))
    (n : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X)
    (hn : IsRepresentative W (RootPairing.weylGroup.ofIdx D.rootDatum i.val) n)
    (hP : HasLineStabilizer ρ v P) :
    0 ≤ D.rootDatum.coroot' i.val (Additive.ofMul χ) ∧
      (D.rootDatum.coroot' i.val (Additive.ofMul χ) = 0 ↔
        n ≫ W.normalizer.inclusion.hom.hom ∈ SubgroupSections P (𝟙_ (SchemeOver k))) := by
  classical
  let K := CommAlgCat.of k k
  let e : (testSpec k).obj (op K) ≅ 𝟙_ (SchemeOver k) :=
    (affineBaseTerminal k).uniqueUpToIso (isTerminalTensorUnit (C := SchemeOver k))
  let s := RootPairing.weylGroup.ofIdx D.rootDatum i.val
  let nK : GroupPoints W.normalizer.group K := e.hom ≫ n
  let g : GroupPoints G.val K := nK ≫ W.normalizer.inclusion.hom.hom
  have hnK : nK ≫ W.quotient.hom.hom =
      toUnit _ ≫ W.image.constantGroup.sectionPoint (W.labelEquiv s) := by
    change (e.hom ≫ n) ≫ W.quotient.hom.hom =
      toUnit ((testSpec k).obj (op K)) ≫ W.image.constantGroup.sectionPoint (W.labelEquiv s)
    have he : e.hom = toUnit ((testSpec k).obj (op K)) := Subsingleton.elim _ _
    have hn' : n ≫ W.quotient.hom.hom = W.image.constantGroup.sectionPoint (W.labelEquiv s) := hn
    rw [Category.assoc, hn', he]
  let nu : Character T.group := (W.labelEquiv s).val χ
  obtain ⟨F, hF⟩ := weylTransport ρ W s nK hnK χ
  let y := F ⟨v, hv.2.2⟩
  have hy : (y : I → k) = act ρ K g v := hF _
  have hy0 : (y : I → k) ≠ 0 := by
    intro h
    have hz : y = F 0 := by
      rw [map_zero]
      exact Subtype.ext h
    exact hv.1 (congrArg Subtype.val (F.injective hz))
  have hnu : Additive.ofMul nu = s.val.weightEquiv (Additive.ofMul χ) :=
    (W.characterAction s χ).symm
  have hfix : D.rootDatum.coroot' i.val (Additive.ofMul χ) = 0 ↔ nu = χ := by
    rw [← reflection_fixes_iff i.val, ← hnu]
    exact Additive.ofMul.injective.eq_iff
  have hext (x : I → k) : extendVector K x = x := by
    funext j
    exact RingHom.id_apply (x j)
  have hdetect : (∃ p : Points P.group.X K, p ≫ P.inclusion.hom.hom = g) ↔
      n ≫ W.normalizer.inclusion.hom.hom ∈ SubgroupSections P (𝟙_ (SchemeOver k)) := by
    change (∃ p : Points P.group.X K, p ≫ P.inclusion.hom.hom = g) ↔
      ∃ p : 𝟙_ (SchemeOver k) ⟶ P.group.X,
        p ≫ P.inclusion.hom.hom = n ≫ W.normalizer.inclusion.hom.hom
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨e.inv ≫ p, ?_⟩
      rw [Category.assoc, hp]
      change e.inv ≫ (e.hom ≫ n) ≫ W.normalizer.inclusion.hom.hom = _
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · rintro ⟨p, hp⟩
      refine ⟨e.hom ≫ p, ?_⟩
      change (e.hom ≫ p) ≫ P.inclusion.hom.hom =
        (e.hom ≫ n) ≫ W.normalizer.inclusion.hom.hom
      simpa only [Category.assoc] using congrArg (e.hom ≫ ·) hp
  have hscalar : nu = χ ↔
      ∃ a : Kˣ, act ρ K g (extendVector K v) = (a : K) • extendVector K v := by
    rw [hext, ← hy]
    constructor
    · intro h
      have hm : (y : I → k) ∈ weightSpace ρ T χ :=
        (congrArg (fun a : Character T.group ↦ (y : I → k) ∈ weightSpace ρ T a) h).mp y.property
      rw [hline, Submodule.mem_span_singleton] at hm
      obtain ⟨a, ha⟩ := hm
      have ha0 : a ≠ 0 := fun hz ↦ hy0 (by simpa only [hz, zero_smul] using ha.symm)
      exact ⟨Units.mk0 a ha0, ha.symm⟩
    · rintro ⟨a, ha⟩
      have hnuv : v ∈ weightSpace ρ T nu := by
        have H := (weightSpace ρ T nu).smul_mem (↑(a⁻¹) : k) y.property
        rw [ha, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at H
        exact H
      exact LinearAlgebraicGroups.RootData.CharacterPairing.characterValuesDetectCharacters hT
        (fun R t ↦ scalar_unique hv.1 R
          ((mem_weightSpace.mp hnuv R t).symm.trans (mem_weightSpace.mp hv.2.2 R t)))
  refine ⟨?_, hfix.trans (hscalar.trans ((hP K g).trans hdetect))⟩
  by_cases h : nu = χ
  · rw [hfix.mpr h]
  · let f := evaluate D c
    have hybot : weightSpace ρ T nu ≠ ⊥ :=
      (Submodule.ne_bot_iff _).mpr ⟨y, y.property, hy0⟩
    obtain ⟨m, hm⟩ := hmax nu h hybot
    have horder : 0 ≤ f (Additive.ofMul χ) - f (Additive.ofMul nu) := by
      have hm' := congrArg f hm
      change f (Additive.ofMul χ - Additive.ofMul nu) = _ at hm'
      simp only [map_sub, Finsupp.sum, map_sum, map_nsmul] at hm'
      rw [hm']
      exact Finset.sum_nonneg fun j _ ↦ nsmul_nonneg (hpositive j).le _
    have hnu' : f (Additive.ofMul nu) = f (Additive.ofMul χ) -
        D.rootDatum.coroot' i.val (Additive.ofMul χ) * f (D.rootDatum.root i.val) := by
      rw [hnu]
      change f ((RootPairing.Equiv.reflection D.rootDatum i.val).weightEquiv (Additive.ofMul χ)) = _
      rw [RootPairing.Equiv.reflection_weightEquiv, RootPairing.reflection_apply,
        map_sub, map_zsmul, zsmul_eq_mul]
      rfl
    rw [hnu', sub_sub_cancel] at horder
    exact (mul_nonneg_iff_of_pos_right hroot).mp horder

end Pairings

open Specs.CharacterPairing (pairing adjointWeightSpace)
open Specs.GeometricRadicals (IsSemisimple GeometricGroup geometricSolvableRadical)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open LinearAlgebraicGroups.CocharacterDynamics (lieImage)
open private limitLie_weightSpans isIso_of_closedImmersion_of_differential
  connected_of_geometricallyConnected pairing_one pairing_inv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private adjointWeightsInternal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private centralizes_baseChange fieldSpecMap_surjective centralizes_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private centralizes_precomposeIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private centralizes_comp_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterDynamics
open private solvable_iff_sections rationalSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private trivial_of_subgroup_of_trivial from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag

/-- A cocharacter annihilated by all roots has its entire image in the center. -/
private theorem central_of_root_pairing_eq_zero (hG : IsReductive G) (hT : IsSplitTorus T.group)
    (c : Cocharacter T.group) (hc : ∀ α : Root T, pairing T.group α.val c = 0)
    (Y : SchemeOver k) (g : Y ⟶ G.val.X) : Centralizes (c ≫ T.inclusion) g := by
  classical
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  obtain ⟨L⟩ := LinearAlgebraicGroups.CocharacterDynamics.existsLimitDecomposition G (c ≫ T.inclusion)
  let s := LinearAlgebraicGroups.identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  let W (χ : Character T.group) := adjointWeightSpace T χ s
  have htop : (⨆ χ, W χ) = ⊤ := (adjointWeightsInternal G T hT s).submodule_iSup_eq_top
  let zeroWeight := {χ : Character T.group // pairing T.group χ c = 0}
  have hspan : (⨆ χ : zeroWeight, W χ.val) = ⊤ := by
    apply top_unique
    rw [← htop]
    apply iSup_le
    intro χ
    by_cases h : pairing T.group χ c = 0
    · exact le_iSup (fun j : zeroWeight ↦ W j.val) ⟨χ, h⟩
    · have hw : W χ = ⊥ := by
        by_contra hne
        have hχ : χ ≠ 1 := fun he ↦ h (he.symm ▸ pairing_one T.group hT c)
        exact h (hc ⟨χ, (LinearAlgebraicGroups.RootData.CharacterPairing.absoluteRootWeights
          T s χ).mpr ⟨hχ, hne⟩⟩)
      rw [hw]
      exact bot_le
  have hsurj : Function.Surjective (mapPointKernel L.centralizer.inclusion) := by
    intro v
    change v ∈ lieImage L.centralizer
    rw [(limitLie_weightSpans G T hT c L s).2]
    change v ∈ ⨆ χ : zeroWeight, W χ.val
    rw [hspan]
    exact Submodule.mem_top
  letI : IsIso L.centralizer.inclusion := isIso_of_closedImmersion_of_differential
    (A := closedSubgroupAlgebraicGroup L.centralizer) (B := G) L.centralizer.inclusion
    L.centralizer.isClosedImmersion
    (LinearAlgebraicGroups.CocharacterDynamics.limitSubgroupsSmooth G _ L).2.2
    (connected_of_geometricallyConnected
      (LinearAlgebraicGroups.CocharacterDynamics.geometricallyConnectedLimitSubgroups G _ L).2.2)
    hG.1 (connected_of_geometricallyConnected hG.2.1) hsurj
  have hi := congrArg (fun f : G.val ⟶ G.val ↦ f.hom.hom)
    (IsIso.inv_hom_id L.centralizer.inclusion)
  apply (L.centralizer_points Y g).mpr
  refine ⟨g ≫ (inv L.centralizer.inclusion).hom.hom, ?_⟩
  rw [Category.assoc]
  exact (congrArg (g ≫ ·) hi).trans (Category.comp_id g)

/-- The image of a central cocharacter lies in the geometric solvable radical.
This uses its smooth reduced image over the algebraic closure. -/
private theorem central_cocharacter_eq_zero (hG : IsSemisimple G) (c : Cocharacter G.val)
    (hc : ∀ (Y : SchemeOver k) (g : Y ⟶ G.val.X), Centralizes c g) : c = 0 := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  letI : Group.FG (IntegerCharacters.{u}) := integerCharacters_fg
  let S := Specs.DiagonalizableGroups.diagonalGroup K IntegerCharacters
  obtain ⟨e, _⟩ := gm_baseChange k K
  let f : S.val ⟶ (GeometricGroup G).val := e.hom ≫ F.map c
  obtain ⟨A, p, i, hfactor, _, _⟩ := LinearAlgebraicGroups.schemeImageFactorization S (GeometricGroup G) f
  let N : ClosedSubgroup (GeometricGroup G).val := ⟨A.val, i, hfactor.2.2.2.2.2⟩
  letI : Flat p.hom.hom.left := hfactor.2.1
  letI : Surjective p.hom.hom.left := hfactor.2.2.1
  have hcentral (Y : SchemeOver K) (g : Y ⟶ (GeometricGroup G).val.X) : Centralizes i g := by
    apply (centralizes_comp_iff p i g).mp
    rw [hfactor.1]
    apply (centralizes_precomposeIso e (F.map c) g).mpr
    exact (centralizes_baseChange K c g).mpr (hc _ _)
  have commuteWithImage (Y : SchemeOver K) (g : Y ⟶ (GeometricGroup G).val.X)
      (s : Y ⟶ A.val.X) : Commute g (s ≫ i.hom.hom) := by
    simpa only [Category.id_comp] using (centralizes_iff i g).mp (hcentral Y g) Y (𝟙 Y) s
  have hn : IsNormalSubgroup i := by
    refine ⟨snd _ _, ?_⟩
    unfold subgroupConjugation
    rw [(commuteWithImage _ (fst _ _) (snd _ _)).eq, mul_inv_cancel_right]
  letI := S.property.1
  letI := A.property.1
  letI := A.property.2.1
  let d : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
  let l := (AddMonoidAlgebra.toMultiplicativeAlgEquiv K K ℤ).trans (MonoidAlgebra.domCongr K K d)
  letI : IsDomain (MonoidAlgebra K IntegerCharacters.{u}) :=
    MulEquiv.isDomain (AddMonoidAlgebra K ℤ) l.symm.toRingEquiv.toMulEquiv
  letI : IsReduced S.val.X.left := inferInstanceAs
    (IsReduced (Spec (CommRingCat.of (MonoidAlgebra K IntegerCharacters))))
  letI : ConnectedSpace S.val.X.left := inferInstanceAs
    (ConnectedSpace (PrimeSpectrum (MonoidAlgebra K IntegerCharacters)))
  have hinj : Function.Injective p.hom.hom.left.appTop.hom :=
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine _).mp
      ⟨inferInstance, inferInstance⟩).injective
  letI : _root_.IsReduced (↑Γ(A.val.X.left, ⊤)) :=
    isReduced_of_injective p.hom.hom.left.appTop.hom hinj
  have hsm : Smooth A.val.X.hom := LinearAlgebraicGroups.smoothOfReducedOverPerfectField
    K A.val (isReduced_of_isAffine_isReduced _)
  have hconn : ConnectedSpace A.val.X.left :=
    (show Function.Surjective p.hom.hom.left from Scheme.Hom.surjective _).connectedSpace
      p.hom.hom.left.continuous
  have hsolv : Specs.SchemeDerivedGroup.IsSolvable A.val := by
    apply (solvable_iff_sections A hsm hconn).mpr
    letI : Mono i.hom.hom := by
      haveI := N.isClosedImmersion
      exact Over.mono_of_mono_left _
    letI : IsMulCommutative (rationalSections A.val) := ⟨⟨fun a b ↦ by
      apply (cancel_mono i.hom.hom).mp
      simp only [MonObj.mul_comp]
      exact (commuteWithImage _ (a ≫ i.hom.hom) b).eq
    ⟩⟩
    infer_instance
  have hN : IsSubgroupOf N (geometricSolvableRadical G) :=
    (LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G).2.2
      N ⟨hsm, hconn, hn⟩ hsolv
  obtain ⟨eN⟩ := trivial_of_subgroup_of_trivial hN hG.2.2
  have hp : p = 0 := ((Grp.isZero_trivial (SchemeOver K)).isTerminal.ofIso eN.symm).hom_ext _ _
  have hf : f = 0 := by rw [← hfactor.1, hp, Limits.zero_comp]
  have hFc : F.map c = 0 := by
    apply (cancel_epi e.hom).mp
    rw [Limits.comp_zero]
    exact hf
  letI : Surjective (fieldSpecMap k K) := fieldSpecMap_surjective K
  letI : Flat (fieldSpecMap k K) := by
    rw [Flat.SpecMap_iff]
    let : Algebra k K := (CommRingCat.ofHom (algebraMap k K)).hom.toAlgebra
    exact Module.Flat.of_free (R := k) (M := K)
  letI : QuasiCompact (fieldSpecMap k K) := inferInstanceAs (QuasiCompact (Spec.map _))
  have ff : (baseChange k K).Faithful := inferInstance
  apply Grp.hom_ext
  apply ff.map_injective
  change (F.map c).hom.hom = (baseChange k K).map (1 : _ ⟶ G.val.X)
  simp only [hFc, (baseChange k K).map_one]
  rfl

section SemisimpleWeights

variable [IsCommMonObj T.group.X] {D : Datum T} {b : D.rootDatum.Base}

/-- The simple roots detect cocharacters because a semisimple group has no
nontrivial smooth connected central torus. -/
private theorem cocharacter_eq_zero_of_simple_roots (hG : IsReductive G)
    (hss : IsSemisimple G) (hT : IsSplitTorus T.group) (y : Additive (Cocharacter T.group))
    (hy : ∀ j : b.support, D.rootDatum.toLinearMap (D.rootDatum.root j.val) y = 0) : y = 0 := by
  let c : Cocharacter T.group := Additive.toMul y
  have hc (α : Root T) : pairing T.group α.val c = 0 := by
    rw [← D.pairing_eq, ← D.root_eq]
    change D.rootDatum.toLinearMap.flip y (D.rootDatum.root α) = 0
    have hspan : Submodule.span ℤ (D.rootDatum.root '' (b.support : Set (Root T))) ≤
        LinearMap.ker (D.rootDatum.toLinearMap.flip y) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      exact hy ⟨j, hj⟩
    exact hspan (b.root_mem_span_int α)
  have hs : c ≫ T.inclusion = 0 := central_cocharacter_eq_zero hss _
    (central_of_root_pairing_eq_zero hG hT c hc)
  haveI : Mono T.inclusion := by
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
    haveI : IsClosedImmersion (F.map T.inclusion) := T.isClosedImmersion
    exact F.mono_of_mono_map inferInstance
  have hz : c = 0 := (cancel_mono T.inclusion).mp (by simpa only [Limits.zero_comp] using hs)
  exact congrArg Additive.ofMul (show c = 1 from hz)

end SemisimpleWeights

open scoped nonZeroDivisors in
/-- If the simple roots detect integral cocharacters, their coroots form a
basis after rationalization and therefore separate rational characters. -/
private theorem coroots_separate {Idx X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Finite ℤ X]
    [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootDatum Idx X Y) (b : P.Base)
    (hroot : ∀ y : Y, (∀ j : b.support, P.toLinearMap (P.root j.val) y = 0) → y = 0)
    (x : ℚ ⊗[ℤ] X)
    (hx : ∀ j : b.support,
      (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap.comp
        ((P.toLinearMap.flip (P.coroot j.val)).baseChange ℚ) x = 0) : x = 0 := by
  classical
  let f : Y →ₗ[ℤ] (b.support → ℤ) := LinearMap.pi fun j ↦ P.toLinearMap (P.root j.val)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    exact hroot y (fun j ↦ congrFun (LinearMap.mem_ker.mp hy) j)
  have hle : Module.finrank ℤ Y ≤ Fintype.card b.support := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_le_finrank_of_injective hf
  let c (j : b.support) : ℚ ⊗[ℤ] Y := (1 : ℚ) ⊗ₜ[ℤ] P.coroot j.val
  have hc : LinearIndependent ℚ c :=
    b.linearIndepOn_coroot.of_isLocalizedModule ℚ ℤ⁰ (TensorProduct.mk ℤ ℚ Y 1)
  have hcard : Fintype.card b.support = Module.finrank ℚ (ℚ ⊗[ℤ] Y) := by
    apply le_antisymm hc.fintype_card_le_finrank
    simpa only [Module.finrank_baseChange] using hle
  let e : ℚ ⊗[ℤ] Y ≃ₗ[ℚ] Module.Dual ℚ (ℚ ⊗[ℤ] X) :=
    (P.toLinearMap.flip.toPerfPair.baseChange ℤ ℚ).trans
      (TensorProduct.isBaseChange ℤ X ℚ).toDualBaseChange
  let g : (ℚ ⊗[ℤ] Y) →ₗ[ℚ] ℚ := (Module.Dual.eval ℚ (ℚ ⊗[ℤ] X) x).comp e.toLinearMap
  have hzero (j : b.support) : g (c j) = 0 := by
    have he : e (c j) = (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap.comp
        ((P.toLinearMap.flip (P.coroot j.val)).baseChange ℚ) := by
      apply (TensorProduct.isBaseChange ℤ X ℚ).algHom_ext
      intro z
      change ((TensorProduct.isBaseChange ℤ X ℚ).toDualBaseChange
          (1 ⊗ₜ[ℤ] P.toLinearMap.flip (P.coroot j.val))) (1 ⊗ₜ[ℤ] z) = _
      simpa [Algebra.smul_def] using (IsBaseChange.toDualBaseChange_tmul
        (TensorProduct.isBaseChange ℤ X ℚ) (1 : ℚ) (P.toLinearMap.flip (P.coroot j.val)) z)
    exact (congrArg (fun l : Module.Dual ℚ (ℚ ⊗[ℤ] X) ↦ l x) he).trans (hx j)
  have hspan := hc.span_eq_top_of_card_eq_finrank' hcard
  by_contra hne
  obtain ⟨v, hv⟩ := Module.Projective.exists_dual_ne_zero ℚ hne
  obtain ⟨y, rfl⟩ := e.surjective v
  have hy : y ∈ Submodule.span ℚ (Set.range c) := hspan ▸ Submodule.mem_top
  apply hv
  change g y = 0
  have hker : Submodule.span ℚ (Set.range c) ≤ LinearMap.ker g := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hzero j
  exact hker hy

section OppositeBorel

variable [IsCommMonObj T.group.X] {D : Datum T} {b : D.rootDatum.Base}

private theorem rational_coroots_separate (hG : IsReductive G) (hss : IsSemisimple G)
    (hT : IsSplitTorus T.group) (x : RationalCharacters T)
    (hx : ∀ j : b.support, rationalCorootPairing D j.val x = 0) : x = 0 := by
  letI := D.freeCharacters
  letI := D.finiteCharacters
  letI := D.freeCocharacters
  letI := D.finiteCocharacters
  exact coroots_separate D.rootDatum b
    (fun y hy ↦ cocharacter_eq_zero_of_simple_roots (b := b) hG hss hT y hy) x hx

private theorem datum_pairing_eq (E D : Datum T) :
    E.rootDatum.toLinearMap = D.rootDatum.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact (E.pairing_eq (Additive.toMul x) (Additive.toMul y)).trans
    (D.pairing_eq (Additive.toMul x) (Additive.toMul y)).symm

private theorem datum_coroot_eq (E : Datum T)
    (hfaith : ∀ y : Additive (Cocharacter T.group),
      (∀ j : b.support, D.rootDatum.toLinearMap (D.rootDatum.root j.val) y = 0) → y = 0)
    (a : Root T) : E.rootDatum.coroot a = D.rootDatum.coroot a := by
  letI := D.freeCharacters
  letI := D.finiteRoots
  have hpair := datum_pairing_eq E D
  have hroot : E.rootDatum.root = D.rootDatum.root := by
    ext x
    rw [E.root_eq, D.root_eq]
  have heval := Module.Dual.eq_of_preReflection_mapsTo'
    (Set.finite_range D.rootDatum.root) (Submodule.subset_span (Set.mem_range_self a))
    (f := E.rootDatum.toLinearMap.flip (E.rootDatum.coroot a))
    (g := D.rootDatum.toLinearMap.flip (D.rootDatum.coroot a))
    (by rw [← hroot]; exact E.rootDatum.coroot_root_two a)
    (by rw [← hroot]; exact E.rootDatum.mapsTo_reflection_root a)
    (D.rootDatum.coroot_root_two a) (D.rootDatum.mapsTo_reflection_root a)
  apply sub_eq_zero.mp
  apply hfaith
  intro j
  rw [map_sub, sub_eq_zero]
  have he := LinearMap.congr_fun heval
    ⟨D.rootDatum.root j.val, Submodule.subset_span (Set.mem_range_self j.val)⟩
  change E.rootDatum.toLinearMap (D.rootDatum.root j.val) (E.rootDatum.coroot a) = _ at he
  rwa [hpair] at he

open scoped Classical in
/-- Fundamental weights for the opposite Borel are the negatives of the
original fundamental weights, matched by negation of simple roots. -/
private theorem oppositeFundamentalWeights (hG : IsReductive G) (hss : IsSemisimple G)
    (hT : IsSplitTorus T.group) {Bneg : ClosedSubgroup G.val}
    {E : Datum T} {bneg : E.rootDatum.Base} {c cneg : Cocharacter T.group}
    (hpos : positiveRoots T c = subgroupRoots T B)
    (hneg : positiveRoots T cneg = subgroupRoots T Bneg)
    (hb : IsBaseFor D.rootDatum (evaluate D c) b)
    (hbneg : IsBaseFor E.rootDatum (evaluate E cneg) bneg)
    (hc : IsRegular T c) (hop : Specs.OpenCell.AreOpposite T B Bneg)
    (ω : b.support → RationalCharacters T) (ωneg : bneg.support → RationalCharacters T)
    (hω : ∀ i j, rationalCorootPairing D j.val (ω i) = if i = j then 1 else 0)
    (hωneg : ∀ i j, rationalCorootPairing E j.val (ωneg i) = if i = j then 1 else 0) :
    ∃ e : b.support ≃ bneg.support,
      ∀ i, (e i).val.val = i.val.val⁻¹ ∧ ωneg (e i) = -ω i := by
  classical
  let neg (a : Root T) := D.rootDatum.reflectionPerm a a
  have negVal (a : Root T) : (neg a).val = a.val⁻¹ := by
    apply Additive.ofMul.injective
    rw [← D.root_eq, show neg a = D.rootDatum.reflectionPerm a a from rfl,
      D.rootDatum.root_reflectionPerm, D.rootDatum.reflection_apply_self, D.root_eq]
    rfl
  have invol (a : Root T) : neg (neg a) = a := Subtype.ext (by rw [negVal, negVal, inv_inv])
  have pos (a : Root T) : neg a ∈ subgroupRoots T Bneg ↔ a ∈ subgroupRoots T B := by
    rw [hop, ← hpos, Set.mem_compl_iff]
    change (¬ 0 < pairing T.group (neg a).val c) ↔ 0 < pairing T.group a.val c
    rw [negVal, pairing_inv T.group hT]
    have hne := hc a
    omega
  let simple {B₁ B₂ : ClosedSubgroup G.val}
      (h : ∀ a : Root T, neg a ∈ subgroupRoots T B₂ ↔ a ∈ subgroupRoots T B₁)
      (a : SimpleRoot T B₁) : SimpleRoot T B₂ := ⟨neg a.val, (h _).mpr a.property.1, by
    intro x hx y hy he
    have hx' := (h (neg x)).mp (by rwa [invol])
    have hy' := (h (neg y)).mp (by rwa [invol])
    apply a.property.2 (neg x) hx' (neg y) hy'
    simpa only [negVal, inv_inv, mul_inv_rev, mul_comm y.val⁻¹ x.val⁻¹] using
      congrArg (Inv.inv : Character T.group → Character T.group) he⟩
  have hsupp (a : Root T) : a ∈ b.support ↔ neg a ∈ bneg.support := by
    rw [baseSimpleRoot hpos hb, baseSimpleRoot hneg hbneg]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨simple pos x, rfl⟩
    · rintro ⟨x, hx⟩
      have rev (z : Root T) : neg z ∈ subgroupRoots T B ↔ z ∈ subgroupRoots T Bneg := by
        simpa only [invol] using (pos (neg z)).symm
      exact ⟨simple rev x, by change neg x.val = a; rw [hx, invol]⟩
  let e : b.support ≃ bneg.support :=
    { toFun i := ⟨neg i.val, (hsupp i.val).mp i.property⟩
      invFun j := ⟨neg j.val, (hsupp (neg j.val)).mpr (by rw [invol]; exact j.property)⟩
      left_inv i := Subtype.ext (invol i.val)
      right_inv j := Subtype.ext (invol j.val) }
  have hpair := datum_pairing_eq E D
  have hcor (j : b.support) : rationalCorootPairing E (e j).val = - rationalCorootPairing D j.val := by
    have hcj : E.rootDatum.coroot (e j).val = -D.rootDatum.coroot j.val := by
      rw [datum_coroot_eq E (fun y hy ↦
        cocharacter_eq_zero_of_simple_roots (b := b) hG hss hT y hy)]
      change D.rootDatum.coroot (neg j.val) = -D.rootDatum.coroot j.val
      apply (D.opposite _ _).mp
      rw [D.root_eq, D.root_eq, negVal]
      rfl
    unfold rationalCorootPairing
    rw [hpair, hcj, map_neg, LinearMap.baseChange_neg, LinearMap.comp_neg]
  refine ⟨e, ?_⟩
  intro i
  refine ⟨negVal i.val, ?_⟩
  apply sub_eq_zero.mp
  rw [sub_neg_eq_add]
  apply rational_coroots_separate (b := b) hG hss hT
  intro j
  have h := LinearMap.congr_fun (hcor j) (ωneg (e i))
  rw [hωneg, LinearMap.neg_apply] at h
  have he := congrArg Neg.neg h.symm
  simp only [neg_neg, e.injective.eq_iff] at he
  rw [map_add, he, hω, neg_add_cancel]

end OppositeBorel

open Specs.BorelProper (IsParabolic)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.StandardParabolics (SimpleSubset)
open private factor_trans subgroup_trans from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private subgroupOf_mutual_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

/-- The cyclic Chevalley lines for the omitted-root parabolics and the primitive
vectors obtained by taking their tensor powers. -/
private theorem lineWeightData (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (hss : IsSemisimple G) (T B : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hTmax : IsGeometricallyMaximal T) (hB : IsKBorel B) (hTB : IsSubgroupOf T B) :
    ∃ comm : IsCommMonObj T.group.X, letI := comm
      Nonempty (LineWeightData T B) := by
  classical
  obtain ⟨comm, D, W, F, c, b, hreg, hpos, hb, hrep, Q, hQ, hclass⟩ :=
    LinearAlgebraicGroups.Flag.StandardParabolics.standardParabolicClassification
      G hG T B hT hTmax hB hTB
  letI := comm
  obtain ⟨_, _, U, hU, hhigh, _, _⟩ :=
    LinearAlgebraicGroups.Representation.PrimitiveLine.primitiveLine G hG T B hT hTmax hB hTB
  let omitted (i : b.support) : SimpleSubset b := ⟨omittedSimpleRoot b i, Set.sdiff_subset⟩
  let P (i : b.support) := Q (omitted i)
  have hPW (i : b.support) : HasWeylIndices W (P i).limitGroups.parabolic
      (parabolicWeylGroup D (omittedSimpleRoot b i)) := hQ _
  let whole : ClosedSubgroup G.val := ⟨G.val, 𝟙 _, by
    change IsClosedImmersion (𝟙 G.val.X.left)
    infer_instance⟩
  have hwhole : IsParabolic G whole := by
    let F := groupBaseChange k (AlgebraicClosure k)
    have he : F.map whole.inclusion = 𝟙 _ := F.map_id _
    have hclosed : IsClosedImmersion (F.map whole.inclusion).hom.hom.left := by
      rw [he]
      change IsClosedImmersion (𝟙 _)
      infer_instance
    obtain ⟨hclosedB, hborel⟩ := hB
    refine ⟨hG, hG.1, hclosed, baseChangedSubgroup _ B hclosedB, hborel, F.map B.inclusion, ?_⟩
    change F.map B.inclusion ≫ F.map whole.inclusion = F.map B.inclusion
    rw [he, Category.comp_id]
  have hBwhole : IsSubgroupOf B whole := ⟨B.inclusion, Category.comp_id _⟩
  have hmaximal (i : b.support) : IsMaximalProperParabolic (P i).limitGroups.parabolic := by
    refine ⟨(P i).parabolic, ?_, ?_⟩
    · intro hiso
      obtain ⟨n, hn⟩ := hrep (RootPairing.weylGroup.ofIdx D.rootDatum i.val)
      apply omitted_reflection_not_mem i (P i).face
      apply (hPW i _ n hn).mp
      let j := (P i).limitGroups.parabolic.inclusion
      haveI : IsIso j := hiso
      refine ⟨(n ≫ W.normalizer.inclusion.hom.hom) ≫ (inv j).hom.hom, ?_⟩
      change (n ≫ W.normalizer.inclusion.hom.hom) ≫ (inv j ≫ j).hom.hom = _
      rw [IsIso.inv_hom_id j]
      exact Category.comp_id _
    · intro H hH hPH
      obtain ⟨⟨J, hJ, -⟩, hmatch⟩ := hclass H hH (subgroup_trans (P i).containsBorel hPH)
      have hincl : (omitted i).val ⊆ J.val := by
        intro a ha
        let s := RootPairing.weylGroup.ofIdx D.rootDatum a
        obtain ⟨n, hn⟩ := hrep s
        apply (simple_in_parabolicWeylGroup (Q J).face ha.1).mp
        apply (hJ s n hn).mp
        exact factor_trans ((hPW i s n hn).mpr (Subgroup.subset_closure ⟨a, ha, rfl⟩)) hPH
      by_cases hi : i.val ∈ J.val
      · left
        have hfull : J.val = (b.support : Set (Root T)) := by
          apply Set.Subset.antisymm J.property
          intro a ha
          by_cases he : a = i.val
          · exact he ▸ hi
          · exact hincl ⟨ha, he⟩
        have htop : parabolicWeylGroup D J.val = ⊤ := by
          unfold parabolicWeylGroup
          rw [hfull, ← hb.generates]
          congr 1
          ext w
          exact ⟨fun ⟨a, ha, hw⟩ ↦ ⟨⟨a, ha⟩, hw⟩, fun ⟨a, hw⟩ ↦ ⟨a.val, a.property, hw⟩⟩
        have hwholeIndices : HasWeylIndices W whole (parabolicWeylGroup D J.val) := by
          intro w n hn
          rw [htop]
          refine ⟨fun _ ↦ Subgroup.mem_top w,
            fun _ ↦ ⟨n ≫ W.normalizer.inclusion.hom.hom, ?_⟩⟩
          change (n ≫ W.normalizer.inclusion.hom.hom) ≫ 𝟙 _ = _
          exact Category.comp_id _
        have hwholeJ := ((hclass whole hwhole hBwhole).2 J).mp hwholeIndices
        have hwholeH : IsSubgroupOf whole H := subgroup_trans hwholeJ.1 ((hmatch J).mp hJ).2
        obtain ⟨e, he⟩ := subgroupOf_mutual_iso ⟨H.inclusion, Category.comp_id _⟩ hwholeH
        have he' : e.hom = H.inclusion := (Category.comp_id _).symm.trans he
        exact he' ▸ inferInstanceAs (IsIso e.hom)
      · right
        have hJomitted : J = omitted i := by
          apply Subtype.ext
          exact Set.Subset.antisymm (fun a ha ↦
            ⟨J.property ha, fun he ↦ hi ((Set.mem_singleton_iff.mp he) ▸ ha)⟩) hincl
        exact ((hmatch (omitted i)).mp (hJomitted ▸ hJ)).1
  have hex (i : b.support) : Nonempty (ParabolicLine (T := T) U (P i).limitGroups.parabolic) :=
    exists_cyclic_parabolic_line (P i).limitGroups.parabolic hU hTB (P i).containsBorel
      (fun ρ χ v hv hgen ↦ (hhigh ρ χ v hv hgen).1)
  let L (i : b.support) := (hex i).some
  have hpositive (a : SimpleRoot T B) : 0 < evaluate D c (Additive.ofMul a.val.val) := by
    change 0 < D.rootDatum.toLinearMap (Additive.ofMul a.val.val) (Additive.ofMul c)
    rw [D.pairing_eq]
    exact (show a.val ∈ positiveRoots T c by rw [hpos]; exact a.property.1)
  have hsimple (j : b.support) : ∃ a : SimpleRoot T B, a.val = j.val :=
    (baseSimpleRoot hpos hb j.val).mp j.property
  have hroot (j : b.support) : 0 < evaluate D c (D.rootDatum.root j.val) := by
    obtain ⟨a, ha⟩ := hsimple j
    rw [← ha, D.root_eq]
    exact hpositive a
  let degree (i j : b.support) := D.rootDatum.coroot' j.val (Additive.ofMul (L i).weight)
  have hdegree (i j : b.support) : 0 ≤ degree i j ∧ (degree i j = 0 ↔ i ≠ j) := by
    letI := (L i).finite
    letI := (L i).decidable
    let s := RootPairing.weylGroup.ofIdx D.rootDatum j.val
    obtain ⟨n, hn⟩ := hrep s
    have hmax nu hne hnonzero := ((hhigh (L i).representation (L i).weight (L i).vector
      (L i).primitive (L i).cyclic).2.1 nu hnonzero hne).1
    obtain ⟨hle, hzero⟩ := simple_coroot_of_line W hT hpositive (P i).limitGroups.parabolic
      (L i).representation (L i).weight (L i).vector (L i).primitive (L i).highestLine hmax
      j (hroot j) n hn (L i).stabilizer
    refine ⟨hle, hzero.trans ((hPW i s n hn).trans ?_)⟩
    constructor
    · rintro hs rfl
      exact omitted_reflection_not_mem i (P i).face hs
    · intro hne
      apply Subgroup.subset_closure
      refine ⟨j.val, ⟨j.property, ?_⟩, rfl⟩
      exact fun h ↦ hne (Subtype.ext (Set.mem_singleton_iff.mp h).symm)
  have hdiag (i : b.support) : 0 < degree i i :=
    lt_of_le_of_ne (hdegree i i).1 fun h ↦ (hdegree i i).2.mp h.symm rfl
  let d (i : b.support) := (degree i i).toNat
  have hd (i : b.support) : 0 < d i := by
    have h := hdiag i
    dsimp only [d]
    omega
  have hpair (i j : b.support) : degree i j = if i = j then (d i : ℤ) else 0 := by
    by_cases h : i = j
    · subst j
      rw [ite_eq_left rfl]
      exact (Int.toNat_of_nonneg (hdiag i).le).symm
    · rw [ite_eq_right h]
      exact (hdegree i j).2.mpr h
  obtain ⟨ω, hω, hωweight⟩ := normalized_weights
    (fun i ↦ (P i).limitGroups.parabolic) L d hd hpair
  have hsep := rational_coroots_separate (b := b) hG hss hT
  refine ⟨comm, ⟨⟨D, W, F, c, b, U, hreg, hpos, hb, hU, P, L, d, ω, hmaximal, hPW, hsep, hω,
    fun i ↦ ⟨hd i, hωweight i⟩, ?_⟩⟩⟩
  intro lam hlam m hm
  have hdominant (j : b.support) : 0 ≤ D.rootDatum.coroot' j.val (Additive.ofMul lam) := by
    obtain ⟨a, ha⟩ := hsimple j
    rw [← ha]
    exact hlam a
  exact weights_and_tensor_powers (fun i ↦ (P i).limitGroups.parabolic) L hsep d hpair lam hdominant m hm

/-- The maximal-parabolic line weights for a split semisimple group and its
opposite Borel, together with primitive vectors of the dominant multiples. -/
theorem lineWeights : LineWeights.{u} := by
  intro k _ G hG hss T B hT hTmax hB hTB
  obtain ⟨comm, ⟨positive⟩⟩ := lineWeightData G hG hss T B hT hTmax hB hTB
  letI := comm
  refine ⟨comm, positive, ?_⟩
  intro Bneg hBneg hTneg hop
  obtain ⟨comm', ⟨negative⟩⟩ := lineWeightData G hG hss T Bneg hT hTmax hBneg hTneg
  have heq : comm' = comm := Subsingleton.elim _ _
  subst comm'
  obtain ⟨e, he⟩ := oppositeFundamentalWeights hG hss hT positive.positive negative.positive
    positive.isBase negative.isBase positive.regular hop positive.fundamentalWeight
    negative.fundamentalWeight positive.fundamentalPairing negative.fundamentalPairing
  refine ⟨negative, e, fun i ↦ ⟨(he i).1, (he i).2, ?_⟩⟩
  rw [(negative.lineWeight (e i)).2, (he i).2, smul_neg]

end

end LinearAlgebraicGroups.Representation.ParabolicLineWeights
