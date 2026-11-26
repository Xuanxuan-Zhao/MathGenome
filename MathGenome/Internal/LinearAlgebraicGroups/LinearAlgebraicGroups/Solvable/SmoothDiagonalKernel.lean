import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalJordanFactors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Orthogonality
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Group.UniqueProds.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.SmoothDiagonalKernel

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup IsSchemeKernel)
open Specs.SmoothDiagonalKernel (matrixPoint IsDiagonalMorphism IsTorusGroup)
open Specs.SmoothnessAndIsogenies

noncomputable section

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000
set_option linter.style.haveILetI false

private def diagonalUnit {m R : Type u} [Fintype m] [LinearOrder m] [DecidableEq m] [CommRing R]
    (g : Matrix.GeneralLinearGroup m R) (h : g.val.IsUpperTriangular) (i : m) : Rˣ := by
  classical
  have hi : g⁻¹.val.IsUpperTriangular := by
    let := g.invertible
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular h
  have hm : g.val i i * g⁻¹.val i i = 1 := by
    rw [← Specs.Unipotent.IsUpperUnitriangular.mul_apply_diag h hi i]
    have he : g.val * g⁻¹.val = 1 := g.val_inv
    rw [he, Matrix.one_apply_eq]
  exact ⟨g.val i i, g⁻¹.val i i, hm, by rw [mul_comm, hm]⟩

private theorem diagonalUnit_val {m R : Type u} [Fintype m] [LinearOrder m] [DecidableEq m] [CommRing R]
    (g : Matrix.GeneralLinearGroup m R) (h : g.val.IsUpperTriangular) (i : m) :
    (diagonalUnit g h i : R) = g.val i i := rfl

open Specs.StandardGroups
open Specs.Unipotent (Index)

private def triangularPointsDiagonal {n : ℕ} {G H : GroupScheme k} (j : G ⟶ H)
    (e : (groupPointsFunctor k).obj H ≅ generalLinearPoints k (Index.{u} n))
    (h : Specs.SmoothDiagonalKernel.IsUpperTriangular j e) :
    (groupPointsFunctor k).obj G ⟶ multiplicativePowerPoints k (Index.{u} n) where
  app R := GrpCat.ofHom <| show ((groupPointsFunctor k).obj G).obj R →* (Index n → Rˣ) from
    { toFun := fun x i ↦ diagonalUnit (matrixPoint j e R x) (h R x) i
      map_one' := by
        funext i
        apply Units.ext
        change (matrixPoint j e R 1).val i i = 1
        change ((e.hom.app R) (((groupPointsFunctor k).map j).app R 1) :
          Matrix.GeneralLinearGroup (Index n) R).val i i = 1
        rw [map_one, map_one]
        exact Matrix.one_apply_eq i
      map_mul' x y := by
        funext i
        apply Units.ext
        change (diagonalUnit (matrixPoint j e R (x * y)) (h R (x * y)) i).val =
          (diagonalUnit (matrixPoint j e R x) (h R x) i).val *
          (diagonalUnit (matrixPoint j e R y) (h R y) i).val
        simp only [diagonalUnit_val, matrixPoint, map_mul]
        exact Specs.Unipotent.IsUpperUnitriangular.mul_apply_diag (h R x) (h R y) i }
  naturality R S a := by
    apply GrpCat.ext
    intro x
    change ( _ : Index n → Sˣ) = _
    funext i
    apply Units.ext
    change (matrixPoint j e S (((groupPointsFunctor k).obj G).map a x)).val i i =
      a.hom ((matrixPoint j e R x).val i i)
    have hnat := NatTrans.naturality_apply (((groupPointsFunctor k).map j) ≫ e.hom) a x
    exact congrArg (fun g : Matrix.GeneralLinearGroup (Index n) S ↦ g.val i i) hnat

private theorem existsDiagonalMorphism {n : ℕ} (G H T : AffineAlgebraicGroup k)
    (j : G.val ⟶ H.val)
    (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Index.{u} n))
    (t : (groupPointsFunctor k).obj T.val ≅ multiplicativePowerPoints k (Index.{u} n))
    (h : Specs.SmoothDiagonalKernel.IsUpperTriangular j e) :
    ∃ d : G.val ⟶ T.val, IsDiagonalMorphism j e t d := by
  let dPoints := triangularPointsDiagonal j e h
  let equiv := groupHomEquiv G.val T.val G.property.1
  let d := equiv.symm (dPoints ≫ t.inv)
  have hd : (groupPointsFunctor k).map d = dPoints ≫ t.inv := equiv.apply_symm_apply _
  refine ⟨d, fun R x i ↦ ?_⟩
  have he : (groupPointsFunctor k).map d ≫ t.hom = dPoints := by rw [hd]; simp
  have hp := congrArg (fun f : (groupPointsFunctor k).obj G.val ⟶
      multiplicativePowerPoints k (Index n) ↦ (f.app R x i : R)) he
  exact hp

private abbrev underlyingFunctor (k : Type u) [Field k] :=
  Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))

/-- A scheme kernel is normal, by applying the kernel pullback to conjugation. -/
private theorem normalOfSchemeKernel {G T : GroupScheme k} {d : G ⟶ T} {U : ClosedSubgroup G}
    (hU : IsSchemeKernel d U) : Specs.IsNormalSubgroup U.inclusion := by
  have hd : U.inclusion.hom.hom ≫ d.hom.hom = 1 := hU.w
  have hmul : Specs.subgroupConjugation U.inclusion ≫ d.hom.hom = 1 := by
    simp only [Specs.subgroupConjugation, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hd,
      MonObj.comp_one, mul_one, mul_inv_cancel]
  exact ⟨hU.lift _ (toUnit _) hmul, hU.lift_fst _ _ _⟩

open private isMonHom_of_comp_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

/-- A group morphism killed by the diagonal factors through the kernel as a group morphism. -/
private theorem liftToSchemeKernel {G T V : GroupScheme k} {d : G ⟶ T} {U : ClosedSubgroup G}
    (hU : IsSchemeKernel d U) (j : V ⟶ G) (hj : j ≫ d = 0) :
    ∃ v : V ⟶ U.group, v ≫ U.inclusion = j := by
  have hc : j.hom.hom ≫ d.hom.hom = 1 :=
    congrArg (fun f : V ⟶ T ↦ f.hom.hom) hj
  let v := hU.lift j.hom.hom (toUnit _) hc
  have hv : v ≫ U.inclusion.hom.hom = j.hom.hom := hU.lift_fst _ _ _
  letI := U.isClosedImmersion
  letI : IsMonHom v := isMonHom_of_comp_closed v j U.inclusion hv
  exact ⟨Grp.homMk v, Grp.hom_ext _ _ hv⟩

private def isoOfPointIso (G H : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj G.val ≅ (groupPointsFunctor k).obj H.val) : G.val ≅ H.val where
  hom := (groupHomEquiv G.val H.val G.property.1).symm e.hom
  inv := (groupHomEquiv H.val G.val H.property.1).symm e.inv
  hom_inv_id := by
    apply (groupHomEquiv G.val G.val G.property.1).injective
    change (groupPointsFunctor k).map (_ ≫ _) = (groupPointsFunctor k).map (𝟙 _)
    rw [Functor.map_comp (groupPointsFunctor k), (groupPointsFunctor k).map_id]
    rw [show (groupPointsFunctor k).map ((groupHomEquiv G.val H.val G.property.1).symm e.hom) =
        e.hom from (groupHomEquiv G.val H.val G.property.1).apply_symm_apply e.hom,
      show (groupPointsFunctor k).map ((groupHomEquiv H.val G.val H.property.1).symm e.inv) =
        e.inv from (groupHomEquiv H.val G.val H.property.1).apply_symm_apply e.inv,
      Iso.hom_inv_id]
  inv_hom_id := by
    apply (groupHomEquiv H.val H.val H.property.1).injective
    change (groupPointsFunctor k).map (_ ≫ _) = (groupPointsFunctor k).map (𝟙 _)
    rw [Functor.map_comp (groupPointsFunctor k), (groupPointsFunctor k).map_id]
    rw [show (groupPointsFunctor k).map ((groupHomEquiv H.val G.val H.property.1).symm e.inv) =
        e.inv from (groupHomEquiv H.val G.val H.property.1).apply_symm_apply e.inv,
      show (groupPointsFunctor k).map ((groupHomEquiv G.val H.val G.property.1).symm e.hom) =
        e.hom from (groupHomEquiv G.val H.val G.property.1).apply_symm_apply e.hom,
      Iso.inv_hom_id]

open Specs.DiagonalizableGroups (groupAlgebra diagonalGroup FGAbelianGroup)
open Specs.CharacterDescent (StandardLattice multiplicativeTypeSpecFunctor)

private theorem diagonalImageIsSplit {n : ℕ} (D T : AffineAlgebraicGroup k)
    (i : D.val ⟶ T.val) (hi : IsClosedImmersion i.hom.hom.left)
    (t : (groupPointsFunctor k).obj T.val ≅ multiplicativePowerPoints k (Index.{u} n)) :
    ∃ M : FGAbelianGroup.{u}, Nonempty (specGroup (groupAlgebra k M.obj) ≅ D.val) := by
  let P := multiplicativePowerGroup k (Index n)
  let e : T.val ≅ P.val :=
    isoOfPointIso T P (t ≪≫ (LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroupPointsIso
       k (Index n)).symm)
  obtain ⟨l⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) n
  let j : D.val ⟶ (diagonalGroup k (StandardLattice.{u} n)).val := i ≫ e.hom ≫ l.inv
  letI : IsClosedImmersion i.hom.hom.left := hi
  haveI : IsIso (e.hom ≫ l.inv).hom.hom.left :=
    (underlyingFunctor k).map_isIso (e.hom ≫ l.inv)
  have hj : IsClosedImmersion j.hom.hom.left :=
    IsClosedImmersion.comp i.hom.hom.left (e.hom ≫ l.inv).hom.hom.left
  obtain ⟨N, ⟨lD, _⟩, _⟩ :=
    (LinearAlgebraicGroups.DiagonalizableGroups.diagonalClosedSubgroups k (StandardLattice.{u} n)
      D.val j).mp hj
  exact ⟨⟨CommGrpCat.of (StandardLattice.{u} n ⧸ N), inferInstance⟩, ⟨lD.symm⟩⟩

open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private splitBaseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

private theorem reducedImage {G D : AffineAlgebraicGroup k} (p : G.val ⟶ D.val)
    (hG : AlgebraicGeometry.IsReduced G.val.X.left)
    (hp : Flat p.hom.hom.left) (hs : Surjective p.hom.hom.left) :
    AlgebraicGeometry.IsReduced D.val.X.left := by
  letI := G.property.1
  letI := D.property.1
  letI := hG
  have hinj : Function.Injective p.hom.hom.left.appTop :=
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine _).mp ⟨hp, hs⟩).injective
  letI : _root_.IsReduced Γ(D.val.X.left, ⊤) := isReduced_of_injective _ hinj
  exact isReduced_of_isAffine_isReduced _

private theorem imageTorus [IsAlgClosed k] {G D : AffineAlgebraicGroup k}
    (p : G.val ⟶ D.val) (hp : Flat p.hom.hom.left) (hs : Surjective p.hom.hom.left)
    (hGs : Smooth G.val.X.hom) (hGc : ConnectedSpace G.val.X.left)
    (hD : ∃ M : FGAbelianGroup.{u}, Nonempty (specGroup (groupAlgebra k M.obj) ≅ D.val))
    (smoothConnected : SmoothConnectedMultiplicativeType.{u}) :
    IsTorusGroup D ∧ (multiplicativeTypeSpecFunctor k).essImage D := by
  obtain ⟨M, ⟨e⟩⟩ := hD
  let A := groupAlgebra k M.obj
  letI : Group.FG M.obj := M.property
  have hmt : Specs.CharacterDescent.IsMultiplicativeType A :=
    ⟨k, inferInstance, inferInstance, inferInstance,
      splitBaseChange (K := k) A ⟨M, ⟨Iso.refl _⟩⟩⟩
  have hM : (multiplicativeTypeSpecFunctor k).essImage D :=
    ⟨op ⟨⟨A, inferInstance⟩, hmt⟩,
      ⟨(fullyFaithfulInducedFunctor Subtype.val).preimageIso e⟩⟩
  letI := hGs
  have hDred := reducedImage p (isReduced_of_smooth_over_field G.val.X.hom) hp hs
  letI := D.property.2.1
  have hDs := smoothOfReducedOverPerfectField k D.val hDred
  letI := hGc
  have hDc : ConnectedSpace D.val.X.left := hs.1.connectedSpace p.hom.hom.left.continuous
  letI : IsIso e.hom.hom.hom.left := (underlyingFunctor k).map_isIso e.hom
  have hsA : Smooth (specGroup A).X.hom := by
    rw [← e.hom.hom.hom.w]
    letI := hDs
    exact smooth_comp _ _
  have hcA : ConnectedSpace (specGroup A).X.left :=
    ((underlyingFunctor k).mapIso e).hom.homeomorph.connectedSpace_iff.mpr hDc
  exact ⟨⟨A, ⟨e⟩, (smoothConnected A).mpr ⟨hmt, hsA, hcA⟩⟩, hM⟩

open Specs.Unipotent (unitriangularPoints closedSubgroupAlgebraicGroup IsUnipotent)
open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

private def unitriangularPointInclusion (n : ℕ) :
    unitriangularPoints k n ⟶ generalLinearPoints k (Index.{u} n) where
  app R := GrpCat.ofHom (Specs.Unipotent.upperUnitriangular (Index n) R).subtype
  naturality _ _ _ := by
    apply GrpCat.ext
    intro x
    rfl

private def kernelUnitriangularPoints {n : ℕ} {G H T : GroupScheme k}
    (j : G ⟶ H) {d : G ⟶ T} {U : ClosedSubgroup G}
    (e : (groupPointsFunctor k).obj H ≅ generalLinearPoints k (Index.{u} n))
    (t : (groupPointsFunctor k).obj T ≅ multiplicativePowerPoints k (Index.{u} n))
    (htri : Specs.SmoothDiagonalKernel.IsUpperTriangular j e)
    (hd : IsDiagonalMorphism j e t d) (hU : IsSchemeKernel d U) :
    (groupPointsFunctor k).obj U.group ⟶ unitriangularPoints k n where
  app R := GrpCat.ofHom <|
    ((((groupPointsFunctor k).map (U.inclusion ≫ j)) ≫ e.hom).app R).hom.codRestrict _
      (fun x ↦ by
        let y := ((groupPointsFunctor k).map U.inclusion).app R x
        change Specs.Unipotent.IsUpperUnitriangular (matrixPoint j e R y).val
        refine ⟨htri R y, fun i ↦ ?_⟩
        have hy : ((groupPointsFunctor k).map d).app R y = 1 := by
          change (x ≫ U.inclusion.hom.hom) ≫ d.hom.hom = 1
          rw [Category.assoc, hU.w, ← Category.assoc, comp_toUnit]
          rfl
        rw [← hd R y i, hy, map_one]
        rfl)
  naturality R S a := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    exact NatTrans.naturality_apply (((groupPointsFunctor k).map (U.inclusion ≫ j)) ≫ e.hom) a x

private theorem unipotentKernel {n : ℕ} {G H T : AffineAlgebraicGroup k}
    (j : G.val ⟶ H.val) {d : G.val ⟶ T.val} {U : ClosedSubgroup G.val}
    (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Index.{u} n))
    (t : (groupPointsFunctor k).obj T.val ≅ multiplicativePowerPoints k (Index.{u} n))
    (hj : IsClosedImmersion j.hom.hom.left)
    (htri : Specs.SmoothDiagonalKernel.IsUpperTriangular j e)
    (hd : IsDiagonalMorphism j e t d) (hU : IsSchemeKernel d U) :
    IsUnipotent (closedSubgroupAlgebraicGroup U) := by
  let K := closedSubgroupAlgebraicGroup U
  let N := LinearAlgebraicGroups.Unipotent.unitriangularGroup k n
  let ν := LinearAlgebraicGroups.Unipotent.unitriangularGroupPointsIso k n
  let a := kernelUnitriangularPoints j e t htri hd hU
  let b := unitriangularPointInclusion (k := k) n
  let v := (groupHomEquiv K.val N.val K.property.1).symm (a ≫ ν.inv)
  let w := (groupHomEquiv N.val H.val N.property.1).symm (ν.hom ≫ b ≫ e.inv)
  have hv : (groupPointsFunctor k).map v = a ≫ ν.inv :=
    (groupHomEquiv K.val N.val K.property.1).apply_symm_apply _
  have hw : (groupPointsFunctor k).map w = ν.hom ≫ b ≫ e.inv :=
    (groupHomEquiv N.val H.val N.property.1).apply_symm_apply _
  have hab : a ≫ b = (groupPointsFunctor k).map (U.inclusion ≫ j) ≫ e.hom := by
    ext R x
    rfl
  have hvw : v ≫ w = U.inclusion ≫ j := by
    apply (groupHomEquiv K.val H.val K.property.1).injective
    change (groupPointsFunctor k).map (v ≫ w) = _
    rw [Functor.map_comp (groupPointsFunctor k), hv, hw]
    calc
      (a ≫ ν.inv) ≫ ν.hom ≫ b ≫ e.inv = (a ≫ b) ≫ e.inv := by simp
      _ = (groupPointsFunctor k).map (U.inclusion ≫ j) := by rw [hab]; simp
  letI := N.property.1
  letI := H.property.1
  letI : IsAffineHom w.hom.hom.left := isAffineHom_of_isAffine _
  letI : IsClosedImmersion (v.hom.hom.left ≫ w.hom.hom.left) := by
    change IsClosedImmersion (v ≫ w).hom.hom.left
    rw [hvw]
    letI := U.isClosedImmersion
    letI := hj
    exact IsClosedImmersion.comp U.inclusion.hom.hom.left j.hom.hom.left
  have hvc : IsClosedImmersion v.hom.hom.left := IsClosedImmersion.of_comp _ w.hom.hom.left
  obtain ⟨A, _, ⟨eA⟩⟩ := groupPresentation K
  have hc := LinearAlgebraicGroups.Unipotent.unipotenceCriteria K A eA
  exact hc.1.mpr (hc.2.1.mpr (hc.2.2.1.mpr ⟨n, N, ⟨ν⟩, v, hvc⟩))

/-- A section of the quotient makes its scheme kernel a retract of the source scheme. -/
private theorem kernelRetract {G D W : GroupScheme k} (p : G ⟶ D) (j : W ⟶ G)
    (h : IsPullback j.hom.hom (toUnit _) p.hom.hom η[D.X])
    (s : D ⟶ G) (hs : s ≫ p = 𝟙 D) :
    ∃ r : G.X ⟶ W.X, j.hom.hom ≫ r = 𝟙 W.X := by
  have hs' : s.hom.hom ≫ p.hom.hom = 𝟙 D.X :=
    congrArg (fun f : D ⟶ D ↦ f.hom.hom) hs
  let a : G.X ⟶ G.X := 𝟙 G.X * (p.hom.hom ≫ s.hom.hom)⁻¹
  have ha : a ≫ p.hom.hom = 1 := by
    simp only [a, MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp, Category.assoc,
      hs', Category.comp_id, mul_inv_cancel]
  let r := h.lift a (toUnit _) ha
  have hr : r ≫ j.hom.hom = a := h.lift_fst _ _ _
  refine ⟨r, ?_⟩
  apply h.hom_ext
  · rw [Category.assoc, hr]
    have hj : j.hom.hom ≫ p.hom.hom = 1 := h.w
    change j.hom.hom ≫ a = (𝟙 W.X) ≫ j.hom.hom
    simp only [a, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ← Category.assoc,
      hj, MonObj.one_comp, inv_one, mul_one, Category.id_comp]
  · exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _

section GenericPoint

variable {L : Type u} [Field L]
variable {M : Type u} [CommGroup M]

open scoped MonoidAlgebra

private def characterPowers (χ : M →* L) :
    MonoidAlgebra L M →ₗ[L] (Multiplicative ℕ → L) :=
  (MonoidAlgebra.basis M L).constr L (fun m ↦ powersHom L (χ m))

/-- Distinct character values at a point imply schematic density of its nonnegative powers.
Dedekind independence applied to the exponential sequences replaces the Vandermonde matrix. -/
private theorem characterPowers_injective (χ : M →* L) (hχ : Function.Injective χ) :
    Function.Injective (characterPowers χ) := by
  apply (MonoidAlgebra.basis M L).injective_constr_of_linearIndependent
  exact (linearIndependent_monoidHom (Multiplicative ℕ) L).comp _ ((powersHom L).injective.comp hχ)

private theorem characterPowers_apply (χ : M →* L) (x : MonoidAlgebra L M)
    (j : Multiplicative ℕ) :
    characterPowers χ x j = MonoidAlgebra.lift L L M (χ ^ j.toAdd) x := by
  let e : (Multiplicative ℕ → L) →ₗ[L] L := LinearMap.proj j
  have h : e.comp (characterPowers χ) =
      (MonoidAlgebra.lift L L M (χ ^ j.toAdd)).toLinearMap := by
    apply (MonoidAlgebra.basis M L).ext
    intro m
    rw [LinearMap.comp_apply, characterPowers, Module.Basis.constr_basis]
    simp [e, MonoidAlgebra.basis_apply, MonoidAlgebra.lift_single, powersHom_apply]
  exact LinearMap.congr_fun h x

private theorem vanishesAtCharacterPowers (χ : M →* L) (hχ : Function.Injective χ)
    (f : MonoidAlgebra L M)
    (hf : ∀ j : ℕ, MonoidAlgebra.lift L L M (χ ^ j) f = 0) : f = 0 := by
  apply characterPowers_injective χ hχ
  ext j
  simpa [characterPowers_apply] using hf j.toAdd

end GenericPoint

open private baseChangeKernelSquare baseChangeMapPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private extendedSpecIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private smooth_of_smooth_after_fieldExtension from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem connectedBaseChange [IsAlgClosed k] (L : Type u) [Field L] [Algebra k L]
    (G : AffineAlgebraicGroup k) (hc : ConnectedSpace G.val.X.left) :
    ConnectedSpace ((groupBaseChange k L).obj G.val).X.left := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  letI : ConnectedSpace (PrimeSpectrum A) :=
    ((underlyingFunctor k).mapIso e).hom.homeomorph.connectedSpace_iff.mpr hc
  let eL := extendedSpecIso L A ≪≫ (baseChange k L).mapIso ((Grp.forget (SchemeOver k)).mapIso e)
  exact eL.hom.left.homeomorph.connectedSpace_iff.mp
    (connectedPrimeSpectrumBaseChangeOfAlgClosed (k := k) (K := L) (A := A))

/-- A quotient section after field extension gives smoothness and connectedness
of the original kernel. -/
private theorem smoothConnectedKernelOfSection [IsAlgClosed k]
    (L : Type u) [Field L] [IsAlgClosed L] [Algebra k L]
    {G D : AffineAlgebraicGroup k} {U : ClosedSubgroup G.val} (p : G.val ⟶ D.val)
    (hU : IsSchemeKernel p U) (hg : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (s : (groupBaseChange k L).obj D.val ⟶ (groupBaseChange k L).obj G.val)
    (hs : s ≫ (groupBaseChange k L).map p = 𝟙 _) :
    Smooth U.group.X.hom ∧ ConnectedSpace U.group.X.left := by
  let F := groupBaseChange k L
  let j := F.map U.inclusion
  let W := F.obj U.group
  let X := F.obj G.val
  obtain ⟨r, hr⟩ := kernelRetract (F.map p) j (baseChangeKernelSquare p U.inclusion hU) s hs
  have hr' : j.hom.hom.left ≫ r.left = 𝟙 W.X.left :=
    congrArg (fun f : W.X ⟶ W.X ↦ f.left) hr
  letI := hg
  letI : Smooth X.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.val.X.hom (fieldSpecMap k L)))
  letI : AlgebraicGeometry.IsReduced X.X.left := isReduced_of_smooth_over_field X.X.hom
  have happ := congrArg Scheme.Hom.appTop hr'
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at happ
  have hinj : Function.Injective r.left.appTop :=
    (show Function.LeftInverse j.hom.hom.left.appTop r.left.appTop from
      fun x ↦ ConcreteCategory.congr_hom happ x).injective
  let U' := closedSubgroupAlgebraicGroup U
  let W' := Specs.Unipotent.baseChangedAlgebraicGroup L U'
  letI : _root_.IsReduced Γ(W.X.left, ⊤) := isReduced_of_injective _ hinj
  letI : IsAffine W.X.left := W'.property.1
  letI : LocallyOfFiniteType W.X.hom := W'.property.2.1
  have hW : Smooth W.X.hom :=
    smoothOfReducedOverPerfectField L W (isReduced_of_isAffine_isReduced _)
  letI : ConnectedSpace X.X.left := connectedBaseChange L G hc
  have hrs : Function.Surjective r.left := by
    intro w
    exact ⟨j.hom.hom.left w, by
      rw [← Scheme.Hom.comp_apply, hr']
      rfl⟩
  letI : ConnectedSpace W.X.left := hrs.connectedSpace r.left.continuous
  let q : W.X.left ⟶ U.group.X.left := pullback.fst U.group.X.hom (fieldSpecMap k L)
  have hq : Surjective q :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback U.group.X.hom (fieldSpecMap k L)).flip
      (inferInstance : Surjective (fieldSpecMap k L))
  exact ⟨smooth_of_smooth_after_fieldExtension U.group.X.hom hW,
    hq.1.connectedSpace q.continuous⟩

private theorem torusCoordinatesDomain (A : HopfAlgebraCategory k)
    (h : Specs.CharacterDescent.IsTorus A) : IsDomain A := by
  obtain ⟨E, _, _, _, r, ⟨e⟩⟩ := h
  letI : UniqueProds Specs.DiagonalizableGroups.IntegerCharacters.{u} :=
    MulEquiv.ulift.uniqueProds_iff.mpr (inferInstance : UniqueProds (Multiplicative ℤ))
  letI : IsDomain (groupAlgebra E (StandardLattice.{u} r)) :=
    inferInstanceAs (IsDomain (MonoidAlgebra E (StandardLattice.{u} r)))
  letI : IsDomain (extendedHopf E A) :=
    Function.Injective.isDomain e.inv.hom.toAlgHom
      (ConcreteCategory.bijective_of_isIso e.inv).injective
  let f : A →ₐ[k] E ⊗[k] A := Algebra.TensorProduct.includeRight
  exact Function.Injective.isDomain f (Algebra.TensorProduct.includeRight_injective (A := E) (B := A)
    (algebraMap k E).injective)

section ExtensionPoints

variable (L : Type u) [Field L] [Algebra k L]

private def extendedPointsIso (G : GroupScheme k) :
    (groupPointsFunctor L).obj ((groupBaseChange k L).obj G) ≅
      restrictTestAlgebra k L ⋙ (groupPointsFunctor k).obj G :=
  NatIso.ofComponents
    (fun R ↦ (baseChangePointGroupEquiv L G R).toGrpIso) (by
      intro R S a
      apply GrpCat.ext
      intro x
      exact (baseChangePointsNaturality k L G.X a x).symm)

private theorem extendedPointsMap {G H : GroupScheme k} (f : G ⟶ H) :
    (groupPointsFunctor L).map ((groupBaseChange k L).map f) ≫ (extendedPointsIso L H).hom =
      (extendedPointsIso L G).hom ≫ Functor.whiskerLeft (restrictTestAlgebra k L)
        ((groupPointsFunctor k).map f) := by
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro x
  exact baseChangePointsSchemeNaturality k L f.hom.hom R x

private def extendedMatrixPointsIso {n : ℕ} (H : GroupScheme k)
    (e : (groupPointsFunctor k).obj H ≅ generalLinearPoints k (Index.{u} n)) :
    (groupPointsFunctor L).obj ((groupBaseChange k L).obj H) ≅
      generalLinearPoints L (Index.{u} n) :=
  extendedPointsIso L H ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra k L) e

private def extendedDiagonalPointsIso {n : ℕ} (T : GroupScheme k)
    (t : (groupPointsFunctor k).obj T ≅ multiplicativePowerPoints k (Index.{u} n)) :
    (groupPointsFunctor L).obj ((groupBaseChange k L).obj T) ≅
      multiplicativePowerPoints L (Index.{u} n) :=
  extendedPointsIso L T ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra k L) t

end ExtensionPoints

open Affine (RationalPoints)
open WithConv

private def HasSchematicallyDensePowers {D : GroupScheme k} (d : RationalPoints D) : Prop :=
  ∀ a : Γ(D.X.left, ⊤),
    (∀ n : ℕ, ((d ^ n : RationalPoints D) : Points D.X (.of k k)).left.appTop a = 0) →
      a = 0

private theorem hasDensePowers_of_characterValues {M : Type u} [CommGroup M]
    (χ : M →* k) (hχ : Function.Injective χ) :
    HasSchematicallyDensePowers ((hopfSpecPointIso (groupAlgebra k M)).hom.app (.of k k)
      (toConv (MonoidAlgebra.lift k k M χ))) := by
  let A := groupAlgebra k M
  let φ := MonoidAlgebra.lift k k M
  let R := CommAlgCat.of k k
  let e := (hopfSpecPointIso A).hom.app R
  have hφ (n : ℕ) : (toConv (φ χ) : WithConv (A →ₐ[k] k)) ^ n =
      toConv (φ (χ ^ n)) := (map_pow (MonoidAlgebra.liftMulEquiv k k M) χ n).symm
  intro a ha
  have hz : ∀ n : ℕ, φ (χ ^ n) ((Scheme.ΓSpecIso (.of A)).hom a) = 0 := by
    intro n
    have hn := ha n
    change ((e (toConv (φ χ)) ^ n : RationalPoints (specGroup A)) :
      Points (specGroup A).X R).left.appTop a = 0 at hn
    let x : (convolutionPoints A).obj R := toConv (φ χ)
    let y : (convolutionPoints A).obj R := toConv (φ (χ ^ n))
    have hxy : x ^ n = y := hφ n
    have hpow : e x ^ n = e y :=
      (map_pow e.hom x n).symm.trans (congrArg (fun z ↦ e.hom z) hxy)
    change ((e x ^ n : RationalPoints (specGroup A)) :
      Points (specGroup A).X R).left.appTop a = 0 at hn
    rw [hpow] at hn
    let f := CommRingCat.ofHom (φ (χ ^ n)).toRingHom
    change (Spec.map f).appTop a = 0 at hn
    have hnat := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality f) a
    change (Scheme.ΓSpecIso (.of k)).hom ((Spec.map f).appTop a) =
      f ((Scheme.ΓSpecIso (.of A)).hom a) at hnat
    change f ((Scheme.ΓSpecIso (.of A)).hom a) = 0
    exact hnat.symm.trans (by rw [hn, map_zero])
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).hom).injective
    ((vanishesAtCharacterPowers χ hχ _ hz).trans (map_zero _).symm)

/-- Schematic density of powers is invariant under isomorphisms of group schemes. -/
private theorem densePowers_mapIso {D E : GroupScheme k} (e : D ≅ E)
    (d : RationalPoints D) (hd : HasSchematicallyDensePowers d) :
    HasSchematicallyDensePowers (((groupPointsFunctor k).map e.hom).app (.of k k) d) := by
  intro a ha
  have hz : e.hom.hom.hom.left.appTop a = 0 := by
    apply hd
    intro n
    have hn := ha n
    rw [← map_pow] at hn
    change (((d ^ n : RationalPoints D) : Points D.X (.of k k)).left ≫
      e.hom.hom.hom.left).appTop a = 0 at hn
    rwa [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hn
  letI : IsIso e.hom.hom.hom.left := (underlyingFunctor k).map_isIso e.hom
  letI : IsIso e.hom.hom.hom.left.appTop := Scheme.Γ.map_isIso e.hom.hom.hom.left.op
  exact (ConcreteCategory.bijective_of_isIso e.hom.hom.hom.left.appTop).injective
    (hz.trans (map_zero _).symm)

/-- For maps out of an affine group with schematically dense powers, equality on the
powers is enough to identify the morphisms. -/
private theorem hom_ext_of_densePowers {D E : GroupScheme k} [IsAffine E.X.left]
    (d : RationalPoints D) (hd : HasSchematicallyDensePowers d) {f g : D ⟶ E}
    (h : ((groupPointsFunctor k).map f).app (.of k k) d =
      ((groupPointsFunctor k).map g).app (.of k k) d) : f = g := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.ext_of_isAffine
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply sub_eq_zero.mp
  apply hd
  intro n
  have hn := congrArg (· ^ n) h
  rw [← map_pow, ← map_pow] at hn
  have hh : ((d ^ n : RationalPoints D) : Points D.X (.of k k)).left ≫ f.hom.hom.left =
      ((d ^ n : RationalPoints D) : Points D.X (.of k k)).left ≫ g.hom.hom.left :=
    congrArg (fun x : RationalPoints E ↦ (x : Points E.X (.of k k)).left) hn
  have he := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hh) a
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply] at he
  exact (map_sub _ _ _).trans (sub_eq_zero.mpr he)

/-- A morphism whose value on the dense generator comes from a closed subgroup
factors through that closed subgroup. -/
private theorem liftOfDensePowers {D G H : GroupScheme k} [IsAffine H.X.left]
    (d : RationalPoints D) (hd : HasSchematicallyDensePowers d)
    (j : G ⟶ H) [IsClosedImmersion j.hom.hom.left] (s₀ : D ⟶ H) (x : RationalPoints G)
    (hx : ((groupPointsFunctor k).map s₀).app (.of k k) d =
      ((groupPointsFunctor k).map j).app (.of k k) x) :
    ∃ s : D ⟶ G, s ≫ j = s₀ := by
  have hk : j.hom.hom.left.ker ≤ s₀.hom.hom.left.ker := by
    have hkle : RingHom.ker j.hom.hom.left.appTop.hom ≤
        RingHom.ker s₀.hom.hom.left.appTop.hom := by
      intro a ha
      apply hd
      intro n
      have hn := congrArg (· ^ n) hx
      rw [← map_pow, ← map_pow] at hn
      have hh : ((d ^ n : RationalPoints D) : Points D.X (.of k k)).left ≫ s₀.hom.hom.left =
          ((x ^ n : RationalPoints G) : Points G.X (.of k k)).left ≫ j.hom.hom.left :=
        congrArg (fun y : RationalPoints H ↦ (y : Points H.X (.of k k)).left) hn
      have he := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hh) a
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        CommRingCat.comp_apply] at he
      rw [he, show j.hom.hom.left.appTop a = 0 from ha, map_zero]
    rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
    exact Scheme.IdealSheafData.le_of_isAffine (by simpa using hkle)
  let l := IsClosedImmersion.lift j.hom.hom.left s₀.hom.hom.left hk
  have hl := IsClosedImmersion.lift_fac j.hom.hom.left s₀.hom.hom.left hk
  let v : D.X ⟶ G.X := Over.homMk l (by rw [← j.hom.hom.w, ← Category.assoc, hl, s₀.hom.hom.w])
  have hv : v ≫ j.hom.hom = s₀.hom.hom := Over.OverMorphism.ext hl
  letI : IsMonHom v := isMonHom_of_comp_closed v s₀ j hv
  exact ⟨Grp.homMk v, Grp.hom_ext _ _ hv⟩

open private extendedGroupIso extendedSpecIso_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem extendedGroupIso_naturality (L : Type u) [Field L] [Algebra k L]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    specGroupMap (extendedHopfMap L f) ≫ (extendedGroupIso L A).hom =
      (extendedGroupIso L B).hom ≫ (groupBaseChange k L).map (specGroupMap f) := by
  apply Grp.hom_ext
  exact extendedSpecIso_natural L f

private theorem groupPoint_mapAlg {A B : HopfAlgebraCategory k}
    (f : A ⟶ B) (x : B →ₐ[k] k) :
    ((groupPointsFunctor k).map (specGroupMap f)).app (.of k k)
      ((hopfSpecPointIso B).hom.app (.of k k) (toConv x)) =
    (hopfSpecPointIso A).hom.app (.of k k) (toConv (x.comp f.hom.toAlgHom)) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)
    (CommRingCat.ofHom x.toRingHom)).symm

private theorem genericLift {G D : AffineAlgebraicGroup k} (p : G.val ⟶ D.val)
    (hp : Surjective p.hom.hom.left) (hD : IsTorusGroup D)
    (hsplit : ∃ M : FGAbelianGroup.{u}, Nonempty (specGroup (groupAlgebra k M.obj) ≅ D.val)) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : Algebra k L)
      (g : RationalPoints ((groupBaseChange k L).obj G.val)),
      HasSchematicallyDensePowers (((groupPointsFunctor L).map
        ((groupBaseChange k L).map p)).app (.of L L) g) := by
  obtain ⟨M, ⟨eD⟩⟩ := hsplit
  obtain ⟨B, _, ⟨eG⟩⟩ := groupPresentation G
  let A := groupAlgebra k M.obj
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  have hA : IsDomain A := by
    obtain ⟨C, ⟨eC⟩, hC⟩ := hD
    let e := ff.preimageIso (eD ≪≫ eC.symm)
    letI := torusCoordinatesDomain C hC
    exact Function.Injective.isDomain e.unop.inv.hom.toAlgHom
      (ConcreteCategory.bijective_of_isIso e.unop.inv).injective
  letI := hA
  let a : A ⟶ B := (ff.preimage (eG.hom ≫ p ≫ eD.inv)).unop
  have ha : specGroupMap a = eG.hom ≫ p ≫ eD.inv := ff.map_preimage _
  have ha' : specGroupMap a ≫ eD.hom = eG.hom ≫ p := by
    rw [ha, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom a.hom.toAlgHom.toRingHom)) := by
    change Surjective (specGroupMap a).hom.hom.left
    rw [ha]
    have := hp
    have : IsIso eG.hom.hom.hom.left := (underlyingFunctor k).map_isIso eG.hom
    have : IsIso eD.inv.hom.hom.left := (underlyingFunctor k).map_isIso eD.inv
    exact inferInstanceAs (Surjective (eG.hom.hom.hom.left ≫ p.hom.hom.left ≫ eD.inv.hom.hom.left))
  obtain ⟨q, hq⟩ := hsurj.1 (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A)
  have hq' : q.asIdeal.comap a.hom.toAlgHom.toRingHom = ⊥ := congrArg PrimeSpectrum.asIdeal hq
  letI : q.asIdeal.IsPrime := q.isPrime
  let E := q.asIdeal.ResidueField
  let L := AlgebraicClosure E
  let f₀ : B →ₐ[k] E := IsScalarTower.toAlgHom k B E
  let f : B →ₐ[k] L := (IsScalarTower.toAlgHom k E L).comp f₀
  have hi : Function.Injective (f.comp a.hom.toAlgHom) := by
    apply (algebraMap E L).injective.comp
    apply (RingHom.injective_iff_ker_eq_bot ((algebraMap B E).comp a.hom.toAlgHom.toRingHom)).mpr
    change RingHom.ker ((algebraMap B E).comp a.hom.toAlgHom.toRingHom) = ⊥
    rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField, hq']
  let χ : M.obj →* L := (f.comp a.hom.toAlgHom).toMonoidHom.comp (MonoidAlgebra.of k M.obj)
  have hχ : Function.Injective χ := hi.comp MonoidAlgebra.of_injective
  let fL := AlgHom.liftEquiv k L B L f
  let τ := LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange k L M.obj
  let γ : groupAlgebra L M.obj ⟶ extendedHopf L A := CommHopfAlgCat.ofHom τ.symm.toBialgHom
  have hev : (fL.comp (extendedHopfMap L a).hom.toAlgHom).comp γ.hom.toAlgHom =
      MonoidAlgebra.lift L L M.obj χ := by
    apply MonoidAlgebra.algHom_ext
    intro m
    have hτ : τ.symm (MonoidAlgebra.single m (1 : L)) =
        (1 : L) ⊗ₜ[k] MonoidAlgebra.single m (1 : k) :=
      MonoidAlgebra.scalarTensorEquiv_symm_single m 1
    change fL ((extendedHopfMap L a).hom (τ.symm (MonoidAlgebra.single m (1 : L)))) = _
    rw [hτ]
    change fL ((1 : L) ⊗ₜ[k] a.hom (MonoidAlgebra.single m (1 : k))) = _
    rw [AlgHom.liftEquiv_tmul, one_smul, MonoidAlgebra.lift_single, one_smul]
    rfl
    · ext
  let δ : extendedHopf L A ⟶ groupAlgebra L M.obj := CommHopfAlgCat.ofHom τ.toBialgHom
  have hev' : (MonoidAlgebra.lift L L M.obj χ).comp δ.hom.toAlgHom =
      fL.comp (extendedHopfMap L a).hom.toAlgHom := by
    apply AlgHom.ext
    intro x
    have h := DFunLike.congr_fun hev (τ x)
    change (fL.comp (extendedHopfMap L a).hom.toAlgHom) (τ.symm (τ x)) =
      MonoidAlgebra.lift L L M.obj χ (τ x) at h
    rw [BialgEquiv.symm_apply_apply] at h
    exact h.symm
  let F := groupBaseChange k L
  let eGL := extendedGroupIso L B ≪≫ F.mapIso eG
  let eDL := extendedGroupIso L A ≪≫ F.mapIso eD
  let eDL' := (hopfSpec (CommRingCat.of L)).mapIso
    (CommHopfAlgCat.isoMk τ).op ≪≫ eDL
  let g₀ := (hopfSpecPointIso (extendedHopf L B)).hom.app (.of L L) (toConv fL)
  let d₀ := (hopfSpecPointIso (groupAlgebra L M.obj)).hom.app (.of L L)
    (toConv (MonoidAlgebra.lift L L M.obj χ))
  let g := ((groupPointsFunctor L).map eGL.hom).app (.of L L) g₀
  have hcomm : eGL.hom ≫ F.map p =
      specGroupMap (extendedHopfMap L a) ≫ eDL.hom := by
    change ((extendedGroupIso L B).hom ≫ F.map eG.hom) ≫ F.map p =
      specGroupMap (extendedHopfMap L a) ≫ (extendedGroupIso L A).hom ≫ F.map eD.hom
    rw [Category.assoc, ← F.map_comp, ← ha', F.map_comp, ← Category.assoc,
      ← extendedGroupIso_naturality, Category.assoc]
  have h := congrArg (fun b : specGroup (extendedHopf L B) ⟶ F.obj D.val ↦
    ((groupPointsFunctor L).map b).app (.of L L) g₀) hcomm
  simp only [(groupPointsFunctor L).map_comp, NatTrans.comp_app, GrpCat.comp_apply] at h
  refine ⟨L, inferInstance, inferInstance, inferInstance, g, ?_⟩
  change HasSchematicallyDensePowers (((groupPointsFunctor L).map (F.map p)).app (.of L L)
    (((groupPointsFunctor L).map eGL.hom).app (.of L L) g₀))
  rw [h]
  have hd' := densePowers_mapIso eDL' d₀ (hasDensePowers_of_characterValues χ hχ)
  change HasSchematicallyDensePowers (((groupPointsFunctor L).map
    (specGroupMap δ ≫ eDL.hom)).app (.of L L) d₀) at hd'
  rw [(groupPointsFunctor L).map_comp, NatTrans.comp_app, GrpCat.comp_apply] at hd'
  change HasSchematicallyDensePowers (((groupPointsFunctor L).map eDL.hom).app (.of L L)
    (((groupPointsFunctor L).map (specGroupMap δ)).app (.of L L)
      ((hopfSpecPointIso (groupAlgebra L M.obj)).hom.app (.of L L)
        (toConv (MonoidAlgebra.lift L L M.obj χ))))) at hd'
  rw [groupPoint_mapAlg] at hd'
  have hg0 := groupPoint_mapAlg (extendedHopfMap L a) fL
  change HasSchematicallyDensePowers (((groupPointsFunctor L).map eDL.hom).app (.of L L)
    (((groupPointsFunctor L).map (specGroupMap (extendedHopfMap L a))).app (.of L L)
      ((hopfSpecPointIso (extendedHopf L B)).hom.app (.of L L) (toConv fL))))
  rw [hg0]
  rw [hev'] at hd'
  exact hd'

open Module
open private eigenbasis_of_isSemisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LinearJordanFactors

private theorem unipotentUpperTriangular_diagonal {m : Type u} [LinearOrder m] [Fintype m]
    [DecidableEq m] {A : Matrix m m k} (hA : A.IsUpperTriangular)
    (h : IsNilpotent (A - 1)) (i : m) : A i i = 1 := by
  have ht : (A - 1).IsUpperTriangular := hA.sub Matrix.blockTriangular_one
  have hpow (n : ℕ) : ((A - 1) ^ n) i i = ((A - 1) i i) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, Specs.Unipotent.IsUpperUnitriangular.mul_apply_diag (ht.pow n) ht, ih]
  obtain ⟨n, hn⟩ := h
  have hnil : IsNilpotent ((A - 1) i i) := ⟨n, by rw [← hpow, hn]; rfl⟩
  have hz := hnil.eq_zero
  simpa using sub_eq_zero.mp (show A i i - 1 = 0 from by simpa using hz)

private def unitDiagonal {m R : Type u} [Fintype m] [DecidableEq m] [CommRing R] :
    (m → Rˣ) →* Matrix.GeneralLinearGroup m R :=
  (Units.map (Matrix.diagonalRingHom m R).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : m ↦ R)).symm.toMonoidHom

private theorem unitDiagonal_natural {m R S : Type u} [Fintype m] [DecidableEq m]
    [CommRing R] [CommRing S] (a : R →+* S) (v : m → Rˣ) :
    Matrix.GeneralLinearGroup.map a (unitDiagonal v) =
      unitDiagonal (fun i ↦ Units.map a.toMonoidHom (v i)) := by
  apply Units.ext
  change (Matrix.diagonal (fun i ↦ (v i : R))).map a =
    Matrix.diagonal (fun i ↦ a (v i))
  exact Matrix.diagonal_map (map_zero a)

private theorem semisimpleUpperTriangular_conjugate [IsAlgClosed k] {m : Type u}
    [LinearOrder m] [Fintype m] [DecidableEq m] (S : Matrix.GeneralLinearGroup m k)
    (hS : S.val.IsUpperTriangular)
    (hs : Module.End.IsSemisimple (Matrix.toLin (Pi.basisFun k m) (Pi.basisFun k m) S.val)) :
    ∃ (P : Matrix.GeneralLinearGroup m k) (a : m → m),
      S = MulAut.conj P (unitDiagonal (fun i ↦ diagonalUnit S hS (a i))) := by
  classical
  let b := Pi.basisFun k m
  let f : Module.End k (m → k) := Matrix.toLin b b S.val
  obtain ⟨c, ev, he⟩ := eigenbasis_of_isSemisimple hs
  have hfin : finrank k (m → k) = Fintype.card m := Module.finrank_pi k
  let e : Fin (finrank k (m → k)) ≃ m := (Fintype.equivFinOfCardEq hfin.symm).symm
  let c' := c.reindex e
  let v := ev ∘ e.symm
  have hv (i : m) : f (c' i) = v i • c' i := by simpa [c', v] using he (e.symm i)
  have heigenvalue (i : m) : ∃ j : m, S.val j j = v i := by
    have hm : f.HasEigenvalue (v i) := by
      intro h
      have hmem : c' i ∈ f.eigenspace (v i) := Module.End.mem_eigenspace_iff.mpr (hv i)
      change f.eigenspace (v i) = ⊥ at h
      rw [h] at hmem
      exact c'.ne_zero i (by simpa using hmem)
    have hr := (Module.End.hasEigenvalue_iff_isRoot_charpoly f (v i)).mp hm
    rw [show f.charpoly = S.val.charpoly from Matrix.charpoly_toLin _ _,
      Matrix.charpoly_of_isUpperTriangular _ hS] at hr
    change Polynomial.eval (v i) (∏ j, (Polynomial.X - Polynomial.C (S.val j j))) = 0 at hr
    rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨j, _, hj⟩ := hr
    exact ⟨j, (sub_eq_zero.mp (by simpa using hj : v i - S.val j j = 0)).symm⟩
  choose a ha using heigenvalue
  let T := b.equiv c' (Equiv.refl m)
  let F := LinearMap.toMatrixAlgEquiv b
  let t : (Module.End k (m → k))ˣ :=
    ⟨T, T.symm, LinearMap.ext T.apply_symm_apply, LinearMap.ext T.symm_apply_apply⟩
  let P := Units.map F.toMonoidHom t
  refine ⟨P, a, ?_⟩
  have hd : F (T.symm.toLinearMap * f * T.toLinearMap) =
      Matrix.diagonal (fun i ↦ S.val (a i) (a i)) := by
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    by_cases hij : i = j
    · subst j
      simp [Module.End.mul_apply, T, hv, ha]
    · simp [Module.End.mul_apply, T, hv, ha, hij]
  apply Units.ext
  change S.val = P.val * Matrix.diagonal (fun i ↦ S.val (a i) (a i)) * P⁻¹.val
  rw [← hd, map_mul, map_mul]
  have hP : P.val = F T.toLinearMap := rfl
  have hPi : P⁻¹.val = F T.symm.toLinearMap := rfl
  rw [← hP, ← hPi]
  change S.val = P.val * (P⁻¹.val * F f * P.val) * P⁻¹.val
  have hp : P.val * P⁻¹.val = 1 := P.val_inv
  simp only [← Matrix.mul_assoc, hp, one_mul]
  rw [Matrix.mul_assoc, hp, mul_one]
  exact (LinearMap.toMatrix_toLin b b S.val).symm

private def conjugatedDiagonalPoints {m : Type u} [Fintype m] [DecidableEq m]
    (P : Matrix.GeneralLinearGroup m k) (a : m → m) :
    multiplicativePowerPoints k m ⟶ generalLinearPoints k m where
  app R := GrpCat.ofHom <|
    (MulAut.conj (Matrix.GeneralLinearGroup.map (algebraMap k R) P)).toMonoidHom.comp
      (unitDiagonal.comp (MonoidHom.pi (fun i ↦ Pi.evalMonoidHom _ (a i))))
  naturality R S φ := by
    apply GrpCat.ext
    intro v
    change (MulAut.conj (Matrix.GeneralLinearGroup.map (algebraMap k S) P))
        (unitDiagonal (fun i ↦ Units.map φ.hom.toRingHom.toMonoidHom (v (a i)))) =
      Matrix.GeneralLinearGroup.map φ.hom.toRingHom
        ((MulAut.conj (Matrix.GeneralLinearGroup.map (algebraMap k R) P))
          (unitDiagonal (fun i ↦ v (a i))))
    rw [← unitDiagonal_natural]
    have h : Matrix.GeneralLinearGroup.map φ.hom.toRingHom
        (Matrix.GeneralLinearGroup.map (algebraMap k R) P) =
        Matrix.GeneralLinearGroup.map (algebraMap k S) P := by
      rw [← MonoidHom.comp_apply, ← Matrix.GeneralLinearGroup.map_comp]
      congr
      ext x
      exact φ.hom.commutes x
    simp only [MulAut.conj_apply, map_mul, map_inv, h]

/-- A semisimple factor of a lift of the generic diagonal point produces a section.
The conjugated diagonal formula agrees on all powers of the generic point, hence
factors through the closed matrix subgroup. -/
private theorem sectionOfDenseLift {n : ℕ} {G H T D : AffineAlgebraicGroup k}
    (j : G.val ⟶ H.val) (d : G.val ⟶ T.val) (p : G.val ⟶ D.val) (i : D.val ⟶ T.val)
    (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Index.{u} n))
    (t : (groupPointsFunctor k).obj T.val ≅ multiplicativePowerPoints k (Index.{u} n))
    (hj : IsClosedImmersion j.hom.hom.left) (hi : IsClosedImmersion i.hom.hom.left)
    (hpi : p ≫ i = d) (htri : Specs.SmoothDiagonalKernel.IsUpperTriangular j e)
    (hd : IsDiagonalMorphism j e t d)
    (L : Type u) [Field L] [IsAlgClosed L] [Algebra k L]
    (g : RationalPoints ((groupBaseChange k L).obj G.val))
    (hg : HasSchematicallyDensePowers
      (((groupPointsFunctor L).map ((groupBaseChange k L).map p)).app (.of L L) g)) :
    ∃ s : (groupBaseChange k L).obj D.val ⟶ (groupBaseChange k L).obj G.val,
      s ≫ (groupBaseChange k L).map p = 𝟙 _ := by
  let F := groupBaseChange k L
  let G' := Specs.Unipotent.baseChangedAlgebraicGroup L G
  let H' := Specs.Unipotent.baseChangedAlgebraicGroup L H
  let D' := Specs.Unipotent.baseChangedAlgebraicGroup L D
  let j' := F.map j
  let d' := F.map d
  let p' := F.map p
  let i' := F.map i
  let e' := extendedMatrixPointsIso L H.val e
  let t' := extendedDiagonalPointsIso L T.val t
  have hj' : IsClosedImmersion j'.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := L) j.hom.hom).flip hj
  have hi' : IsClosedImmersion i'.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := L) i.hom.hom).flip hi
  have hpi' : p' ≫ i' = d' := (F.map_comp p i).symm.trans (congrArg F.map hpi)
  let R := CommAlgCat.of L L
  let oldPoint := (extendedPointsIso L G.val).hom.app R
  let mat := (((groupPointsFunctor L).map j') ≫ e'.hom).app R
  let diag := (((groupPointsFunctor L).map d') ≫ t'.hom).app R
  have hmat (x : RationalPoints G'.val) :
      mat x = matrixPoint j e ((restrictTestAlgebra k L).obj R) (oldPoint x) := by
    have h := congrArg (fun v ↦ v.app R x) (extendedPointsMap L j)
    exact congrArg (fun y ↦ e.hom.app ((restrictTestAlgebra k L).obj R) y) h
  have hval (x : RationalPoints G'.val) (a : Index n) :
      (diag x a : L) = (mat x).val a a := by
    have h := congrArg (fun v ↦ v.app R x) (extendedPointsMap L d)
    rw [hmat]
    exact (congrArg (fun y ↦ (t.hom.app ((restrictTestAlgebra k L).obj R) y a : Lˣ).val) h).trans
      (hd _ (oldPoint x) a)
  have hu (x : RationalPoints G'.val) : (mat x).val.IsUpperTriangular := by
    rw [hmat]
    exact htri _ _
  obtain ⟨⟨s, u'⟩, hs, _⟩ := Affine.rationalJordanDecomposition G' g
  let b := Pi.basisFun L (Index n)
  have hJs := hs.2.2 b H'.val e' j'
  have hsemi : Module.End.IsSemisimple (Matrix.toLin b b (mat s).val) := hJs.semisimple
  have hnil : IsNilpotent ((mat u').val - 1) := by
    have h := hJs.unipotent.map (LinearMap.toMatrixAlgEquiv b)
    change IsNilpotent (LinearMap.toMatrixAlgEquiv b (Matrix.toLin b b (mat u').val - 1)) at h
    rw [map_sub, map_one] at h
    simpa only [LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply,
      LinearMap.toMatrix_toLin] using h
  have hdiag_s : diag g = diag s := by
    funext a
    apply Units.ext
    let diagMap : RationalPoints (F.obj G.val) →* (Index n → Lˣ) := diag.hom
    have hsplit : (g : RationalPoints (F.obj G.val)) = s * u' := hs.1
    have hmul := (congrArg (fun x ↦ diagMap x) hsplit).trans (diagMap.map_mul s u')
    change (diag g : Index n → Lˣ) = (diag s : Index n → Lˣ) * diag u' at hmul
    rw [hmul]
    change (diag s a).val * (diag u' a).val = (diag s a).val
    rw [hval u' a, unipotentUpperTriangular_diagonal (hu u') hnil, mul_one]
  obtain ⟨P, a, hP⟩ := semisimpleUpperTriangular_conjugate (mat s) (hu s) hsemi
  let d₀ := ((groupPointsFunctor L).map p').app R g
  let S₀ := (groupPointsFunctor L).map i' ≫ t'.hom ≫ conjugatedDiagonalPoints P a ≫ e'.inv
  let s₀ := (groupHomEquiv D'.val H'.val D'.property.1).symm S₀
  have hs₀ : (groupPointsFunctor L).map s₀ = S₀ :=
    (groupHomEquiv D'.val H'.val D'.property.1).apply_symm_apply _
  have hPa : (fun x ↦ diagonalUnit (mat s) (hu s) (a x)) = (fun x ↦ diag g (a x)) := by
    funext x
    apply Units.ext
    change (mat s).val (a x) (a x) = (diag g (a x)).val
    rw [hdiag_s, hval]
  have hP' : mat s = MulAut.conj P (unitDiagonal (fun i ↦ diag g (a i))) := hPa ▸ hP
  have hs₀g : ((groupPointsFunctor L).map s₀).app R d₀ =
      ((groupPointsFunctor L).map j').app R s := by
    rw [hs₀]
    apply (ConcreteCategory.bijective_of_isIso (e'.hom.app R)).injective
    have heq : ((groupPointsFunctor L).map i').app R d₀ =
        ((groupPointsFunctor L).map d').app R g := by
      change (((groupPointsFunctor L).map p' ≫ (groupPointsFunctor L).map i').app R) g = _
      rw [← (groupPointsFunctor L).map_comp, hpi']
    change e'.hom.app R (e'.inv.app R
      ((conjugatedDiagonalPoints P a).app R (t'.hom.app R
        (((groupPointsFunctor L).map i').app R d₀)))) = mat s
    rw [heq, ← GrpCat.comp_apply, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app]
    change MulAut.conj (Matrix.GeneralLinearGroup.map (algebraMap L L) P)
      (unitDiagonal (fun i ↦ diag g (a i))) = mat s
    have hPmap : Matrix.GeneralLinearGroup.map (algebraMap L L)
        (P : Matrix.GeneralLinearGroup (Index n) L) = P := by
      simp [Algebra.algebraMap_self]
    rw [hPmap]
    exact hP'.symm
  letI : IsAffine (F.obj H.val).X.left := H'.property.1
  letI := hj'
  obtain ⟨s', hs'⟩ := liftOfDensePowers d₀ hg j' s₀ s hs₀g
  have hsd : ((groupPointsFunctor L).map s').app R d₀ = s := by
    have h := congrArg (fun f : D'.val ⟶ H'.val ↦ ((groupPointsFunctor L).map f).app R d₀) hs'
    have h' := h.trans hs₀g
    change (((groupPointsFunctor L).map s').app R d₀ : Points (F.obj G.val).X R) ≫ j'.hom.hom =
      (s : Points (F.obj G.val).X R) ≫ j'.hom.hom at h'
    have : Mono j'.hom.hom := Over.mono_of_mono_left _
    exact (cancel_mono j'.hom.hom).mp h'
  have hd₀ : ((groupPointsFunctor L).map p').app R s = d₀ := by
    have h := (ConcreteCategory.bijective_of_isIso (t'.hom.app R)).injective (hdiag_s.symm)
    change ((groupPointsFunctor L).map d').app R s = ((groupPointsFunctor L).map d').app R g at h
    rw [← hpi', (groupPointsFunctor L).map_comp, NatTrans.comp_app, GrpCat.comp_apply,
      GrpCat.comp_apply] at h
    letI := hi'
    have : Mono i'.hom.hom := Over.mono_of_mono_left _
    exact (cancel_mono i'.hom.hom).mp h
  refine ⟨s', ?_⟩
  letI : IsAffine (F.obj D.val).X.left := D'.property.1
  apply hom_ext_of_densePowers d₀ hg
  rw [(groupPointsFunctor L).map_comp, NatTrans.comp_app, GrpCat.comp_apply, hsd, hd₀,
    (groupPointsFunctor L).map_id, NatTrans.id_app]
  rfl

/-- Conditional derivation of the geometric diagonal-kernel assertion. -/
theorem smoothDiagonalKernel_conditional
    (_ : CharacterPullbackEquivariant.{u})
    (_ : MultiplicativeTypeSmoothness.{u})
    (_ : MultiplicativeTypeSmoothnessCharZero.{u})
    (_ : RootsOfUnityNonreduced.{u})
    (_ : RootsOfUnityPowerSequence.{u})
    (smoothConnected : SmoothConnectedMultiplicativeType.{u})
    (_ : TorusIsogenyCorrespondence.{u})
    (_ : TorusIsogenyCriterion.{u})
    (_ : TorusIsogenyKernel.{u}) :
    Specs.SmoothDiagonalKernel.SmoothDiagonalKernel.{u} := by
  intro k _ _ n G H T j e t hj htri hGs hGc
  obtain ⟨d, hd⟩ := existsDiagonalMorphism G H T j e t htri
  obtain ⟨D, p, i, U, hpi, hi, hU, _⟩ := schemeImageQuotient G T d
  have ⟨hc, hpf, hps, _, _, hic⟩ := hpi
  have hsplit := diagonalImageIsSplit D T i hic t
  obtain ⟨htor, hmt⟩ := imageTorus p hpf hps hGs hGc hsplit smoothConnected
  have hUn := unipotentKernel j e t hj htri hd hU
  obtain ⟨L, _, _, _, g, hg⟩ := genericLift p hps htor hsplit
  obtain ⟨s, hs⟩ := sectionOfDenseLift j d p i e t hj hic hc htri hd L g hg
  have hpU : IsSchemeKernel p U := by
    letI := hic
    letI : Mono i.hom.hom := Over.mono_of_mono_left _
    have hcomp : p.hom.hom ≫ i.hom.hom = d.hom.hom :=
      congrArg (fun h : G.val ⟶ T.val ↦ h.hom.hom) hc
    have hunit : η[D.val.X] ≫ i.hom.hom = η[T.val.X] := IsMonHom.one_hom _
    have ht : IsPullback (𝟙 (𝟙_ (SchemeOver k))) η[D.val.X] η[T.val.X] i.hom.hom :=
      IsPullback.of_horiz_isIso_mono ⟨(Category.id_comp _).trans hunit.symm⟩
    have hfull : IsPullback U.inclusion.hom.hom (toUnit U.group.X ≫ 𝟙 _)
        (p.hom.hom ≫ i.hom.hom) η[T.val.X] := by
      rw [Category.comp_id, hcomp]
      exact hU
    have hsq : U.inclusion.hom.hom ≫ p.hom.hom = toUnit U.group.X ≫ η[D.val.X] := by
      apply (cancel_mono i.hom.hom).mp
      simpa only [Category.assoc, hcomp, hunit] using hU.w
    exact hfull.of_bot hsq ht.flip
  obtain ⟨hUs, hUc⟩ := smoothConnectedKernelOfSection L p hpU hGs hGc s hs
  refine ⟨d, hd, D, p, i, U, hpi, hi, hU, htor, hUs, hUc, normalOfSchemeKernel hU, hUn, ?_⟩
  intro V hV
  have hkill : V.inclusion ≫ p = 0 :=
    LinearAlgebraicGroups.Unipotent.homFromUnipotentToMultiplicativeType
      (closedSubgroupAlgebraicGroup V) D (V.inclusion ≫ p) hV hmt
  exact liftToSchemeKernel hpU V.inclusion hkill

end
end LinearAlgebraicGroups.SmoothDiagonalKernel

universe v8_closure_79c8202701012f3d_u0
theorem _root_.«LinearAlgebraicGroups».«SmoothDiagonalKernel».«smoothDiagonalKernel» : _root_.«LinearAlgebraicGroups».«Specs».«SmoothDiagonalKernel».«SmoothDiagonalKernel».{v8_closure_79c8202701012f3d_u0} :=
  @_root_.«LinearAlgebraicGroups».«SmoothDiagonalKernel».«smoothDiagonalKernel_conditional».{v8_closure_79c8202701012f3d_u0} (@_root_.«LinearAlgebraicGroups».«SmoothnessAndIsogenies».«characterPullbackEquivariant».{v8_closure_79c8202701012f3d_u0}) (@_root_.«LinearAlgebraicGroups».«SmoothnessAndIsogenies».«multiplicativeTypeSmoothness».{v8_closure_79c8202701012f3d_u0}) (@_root_.«LinearAlgebraicGroups».«SmoothnessAndIsogenies».«multiplicativeTypeSmoothnessCharZero».{v8_closure_79c8202701012f3d_u0}) (@_root_.«LinearAlgebraicGroups».«SmoothnessAndIsogenies».«rootsOfUnityNonreduced».{v8_closure_79c8202701012f3d_u0}) (@_root_.«LinearAlgebraicGroups».«SmoothnessAndIsogenies».«rootsOfUnityPowerSequence».{v8_closure_79c8202701012f3d_u0}) (@_root_.«LinearAlgebraicGroups».«SmoothnessAndIsogenies».«smoothConnectedMultiplicativeType».{v8_closure_79c8202701012f3d_u0}) (@_root_.«LinearAlgebraicGroups».«SmoothnessAndIsogenies».«torusIsogenyCorrespondence».{v8_closure_79c8202701012f3d_u0}) (@_root_.«LinearAlgebraicGroups».«SmoothnessAndIsogenies».«torusIsogenyCriterion».{v8_closure_79c8202701012f3d_u0}) (@_root_.«LinearAlgebraicGroups».«SmoothnessAndIsogenies».«torusIsogenyKernel».{v8_closure_79c8202701012f3d_u0})
