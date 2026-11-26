import Specs.LinearAlgebraicGroups.Reductive.GeneralLinearCentralIsogeny
import LinearAlgebraicGroups.Reductive.CentralDerived
import LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Polynomial
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Reductive.GeneralLinearCentralIsogeny

open _root_.LinearAlgebraicGroups.Specs
open Specs.CentralDerived Specs.CentralTorus Specs.GeneralLinearCentralIsogeny
open Specs.GeneralLinearStructure (MatrixPoints SpecialMatrixPoints)
open Specs.GeometricRadicals (IsSplitReductive IsTorus)
open Specs.SmoothnessAndIsogenies (rootsOfUnityCoordinates)
open Specs.DiagonalizableGroups (diagonalGroup rootsOfUnityPoints)
open Specs.Unipotent (Index)
open Matrix

open private Unipotent.groupIsoOfPoints from LinearAlgebraicGroups.Unipotent.Criteria
open private Unipotent.onPoints_injective from LinearAlgebraicGroups.Unipotent.CentralSeries
open private GeneralLinearStructure.baseChangePowerTorusIso
  from LinearAlgebraicGroups.Reductive.GeneralLinearStructure
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private SmoothnessAndIsogenies.reducedOfSmoothHopf
  from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]


private theorem scalarCentreIsTorus {M : AffineAlgebraicGroup k} {Z : GroupScheme k}
    (i : M.val ≅ Z) (a : (groupPointsFunctor k).obj M.val ≅ Specs.StandardGroups.multiplicativePoints k) :
    IsTorus Z := by
  let P := StandardGroups.multiplicativePowerGroup k (Index.{u} 1)
  let c := StandardGroups.multiplicativePowerGroupPointsIso k (Index.{u} 1)
  let b : Specs.StandardGroups.multiplicativePoints k ≅
      Specs.StandardGroups.multiplicativePowerPoints k (Index.{u} 1) :=
    NatIso.ofComponents (fun R =>
      ({ toFun := fun z _ => z
         invFun := fun f => f ⟨0⟩
         left_inv := fun _ => rfl
         right_inv := fun f => funext fun j => congrArg f (Subsingleton.elim _ _)
         map_mul' := fun _ _ => rfl } : Rˣ ≃* (Index.{u} 1 → Rˣ)).toGrpIso)
      (by intro R A f; apply GrpCat.ext; intro z; rfl)
  let e : M.val ≅ P.val := Unipotent.groupIsoOfPoints (G := M) (H := P) (a ≪≫ b ≪≫ c.symm)
  exact ⟨k, inferInstance, inferInstance, inferInstance,
    1, ⟨(groupBaseChange k k).mapIso (i.symm ≪≫ e) ≪≫
      GeneralLinearStructure.baseChangePowerTorusIso k 1⟩⟩

private theorem determinantRootLift {n : ℕ} (hn : 0 < n) (R : TestAlgebra k) (d : Rˣ) :
    let A := determinantRootTestAlgebra R n d
    let b := determinantRootMap R n d
    Module.Finite R (determinantRootAlgebra R n d) ∧
    Module.FaithfullyFlat R (determinantRootAlgebra R n d) ∧
    ∃ z : Aˣ, (z : A) = AdjoinRoot.root (X ^ n - C (d : R)) ∧
      z ^ n = Units.map b.hom.toMonoidHom d := by
  let p := X ^ n - C (d : R)
  have hp : p.Monic := Polynomial.monic_X_pow_sub_C _ hn.ne'
  refine ⟨hp.finite_adjoinRoot, ?_, ?_⟩
  · rcases subsingleton_or_nontrivial R with hR | hR
    · letI := hp.free_adjoinRoot
      refine ⟨fun m hm => (hm.ne_top (Subsingleton.elim m ⊤)).elim⟩
    · let b := AdjoinRoot.powerBasisAux' hp
      haveI : Nonempty (Fin p.natDegree) := by
        rw [show p.natDegree = n from Polynomial.natDegree_X_pow_sub_C]
        exact ⟨⟨0, hn⟩⟩
      exact Module.FaithfullyFlat.of_linearEquiv _ _ b.repr
  · let A := determinantRootTestAlgebra R n d
    let b := determinantRootMap R n d
    let z := AdjoinRoot.root p
    let d' : Aˣ := Units.map b.hom.toMonoidHom d
    have hz : z ^ n = (d' : A) := by
      change z ^ n = AdjoinRoot.of p (d : R)
      exact sub_eq_zero.mp (by simpa [p, z] using AdjoinRoot.eval₂_root p)
    have hu : IsUnit z := (isUnit_pow_iff hn.ne').mp (hz.symm ▸ d'.isUnit)
    refine ⟨hu.unit, hu.unit_spec, Units.ext ?_⟩
    change (hu.unit.val : A) ^ n = (d' : A)
    rw [hu.unit_spec, hz]

private theorem detScalar {R : TestAlgebra k} (n : ℕ) (z : Rˣ) :
    (GeneralLinearGroup.scalar (Index.{u} n) z).det = z ^ n := by
  rw [GeneralLinearGroup.det_scalar]
  simp [Index]

private def productPoint {A B : GroupScheme k} {R : TestAlgebra k}
    (x : Points A.X R) (y : Points B.X R) : Points (A ⊗ B).X R :=
  lift x y

private theorem productPoint_first {A B : GroupScheme k} {R : TestAlgebra k}
    (x : Points A.X R) (y : Points B.X R) :
    pointMap (firstProjection A B) R (productPoint x y) = x := lift_fst x y

private theorem productPoint_second {A B : GroupScheme k} {R : TestAlgebra k}
    (x : Points A.X R) (y : Points B.X R) :
    pointMap (secondProjection A B) R (productPoint x y) = y := lift_snd x y

private theorem pointMap_comp {A B C : GroupScheme k} (f : A ⟶ B) (g : B ⟶ C)
    {R : TestAlgebra k} (x : Points A.X R) :
    pointMap (f ≫ g) R x = pointMap g R (pointMap f R x) :=
  (Category.assoc x f.hom.hom g.hom.hom).symm

/-- Specialization of the central product theorem to the standard matrix groups. -/
theorem generalLinearCentralIsogeny : GeneralLinearCentralIsogeny.{u} := by
  intro k _ n hn G S M g s a
  have hred := GeneralLinearStructure.generalLinearReductive k n hn G g
  have hsplit : IsSplitReductive G := by
    obtain ⟨Tdiag, _, _, _, hsplit, _, _, _, _, _, hbase, _, hmax, _⟩ :=
      GeneralLinearStructure.generalLinearBorelPair k n hn G g
    exact ⟨hred, Tdiag, hsplit, hbase, hmax⟩
  refine ⟨hsplit, ?_⟩
  obtain ⟨Z, hZ, i, hi⟩ := GeneralLinearStructure.generalLinearCenter k n hn G g M a
  obtain ⟨f, hf, hfpoints, _, hD⟩ := GeneralLinearStructure.generalLinearDerived k n hn G S g s
  let T : ClosedSubgroup Z.group := ⟨Z.group, 𝟙 _, by
    change IsClosedImmersion (𝟙 Z.group.X.left)
    infer_instance⟩
  let D : ClosedSubgroup G.val := ⟨S.val, f, hf⟩
  let t : T.group ⟶ M.val := T.inclusion ≫ i.inv
  have hT : IsLargestTorus T :=
    ⟨scalarCentreIsTorus i a, fun U _ => ⟨U.inclusion, Category.comp_id _⟩⟩
  have ht : IsIso t := by
    change IsIso (𝟙 Z.group ≫ i.inv)
    infer_instance
  have hscalar (R : TestAlgebra k) (x : Points M.val.X R) :
      g.hom.app R (pointMap (i.hom ≫ Z.inclusion) R x) =
        GeneralLinearGroup.scalar (Index.{u} n) (a.hom.app R x) :=
    Units.ext ((hi R x).trans (GeneralLinearGroup.coe_scalar _).symm)
  obtain ⟨m, hm, I, _, _, J, _, hI, eIJ, _, _, hJ, hcentral⟩ :=
    CentralDerived.centralProductKernel G hred Z hZ T hT D hD
  obtain ⟨hflat, hsurj⟩ :=
    CentralDerived.centralProductFaithfullyFlat G hred Z hZ T hT D hD m hm
  have hmul (R : TestAlgebra k) (x : Points (T.group ⊗ S.val).X R) :
      g.hom.app R (pointMap m R x) =
        GeneralLinearGroup.scalar (Index.{u} n)
          (a.hom.app R (pointMap (firstProjection T.group S.val ≫ t) R x)) *
          SpecialLinearGroup.toGL (s.hom.app R (pointMap (secondProjection T.group S.val) R x)) := by
    have hfirst : firstProjection T.group S.val ≫ T.inclusion ≫ Z.inclusion =
        (firstProjection T.group S.val ≫ t) ≫ (i.hom ≫ Z.inclusion) := by
      simp [t]
    have hprod : pointMap m R x =
        pointMap ((firstProjection T.group S.val ≫ t) ≫ (i.hom ≫ Z.inclusion)) R x *
          pointMap (secondProjection T.group S.val ≫ f) R x := by
      rw [← hfirst]
      exact (congrArg (fun h => x ≫ h) hm).trans (MonObj.comp_mul _ _ _)
    rw [hprod, map_mul,
      pointMap_comp (firstProjection T.group S.val ≫ t) (i.hom ≫ Z.inclusion),
      pointMap_comp (secondProjection T.group S.val) f, hscalar, hfpoints]
  refine ⟨Z, i, T, f, hf, hZ, hT, ?_, hD, hscalar, hfpoints, m, hm, hflat, hsurj, hmul, ?_, ?_⟩
  · change IsIso (𝟙 Z.group)
    infer_instance
  · intro R x
    let d := GeneralLinearGroup.det (g.hom.app R x)
    let A := determinantRootTestAlgebra R n d
    let b := determinantRootMap R n d
    obtain ⟨hfin, hfaith, z, hzval, hz⟩ := determinantRootLift hn R d
    let X := GeneralLinearGroup.map b.hom.toRingHom (g.hom.app R x)
    let U := GeneralLinearGroup.scalar (Index.{u} n) z⁻¹ * X
    have hX : X.det = Units.map b.hom.toMonoidHom d :=
      GeneralLinearGroup.map_det b.hom.toRingHom _
    have hU : U.det = 1 := by
      change (GeneralLinearGroup.scalar (Index.{u} n) z⁻¹ * X).det = 1
      rw [map_mul, detScalar, inv_pow, hz]
      change (Units.map b.hom.toMonoidHom d)⁻¹ * X.det = 1
      rw [hX]
      exact inv_mul_cancel _
    let v := SpecialLinearGroup.toGLKerEquiv.symm ⟨U, hU⟩
    let l := (a.app A).groupIsoToMulEquiv.symm z
    let y₁ := (((groupPointsFunctor k).mapIso (asIso t)).app A).groupIsoToMulEquiv.symm l
    let y₂ := (s.app A).groupIsoToMulEquiv.symm v
    let y := productPoint y₁ y₂
    have h₁ : a.hom.app A (pointMap (firstProjection T.group S.val ≫ t) A y) = z := by
      change a.hom.app A (pointMap t A (pointMap (firstProjection T.group S.val) A y)) = z
      rw [productPoint_first]
      change (a.app A).groupIsoToMulEquiv
        ((((groupPointsFunctor k).mapIso (asIso t)).app A).groupIsoToMulEquiv y₁) = _
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have h₂ : SpecialLinearGroup.toGL (s.hom.app A (pointMap (secondProjection T.group S.val) A y)) =
        U := by
      rw [productPoint_second]
      change SpecialLinearGroup.toGL ((s.app A).groupIsoToMulEquiv y₂) = U
      rw [MulEquiv.apply_symm_apply]
      exact congrArg Subtype.val (SpecialLinearGroup.toGLKerEquiv.apply_symm_apply ⟨U, hU⟩)
    refine ⟨hfin, hfaith, z, y, hzval, hz, h₁, h₂, ?_⟩
    apply (g.app A).groupIsoToMulEquiv.injective
    change g.hom.app A (pointMap m A y) = g.hom.app A (mapPoints b x)
    have hnat : g.hom.app A (mapPoints b x) = X :=
      congrArg (fun a => a x) (g.hom.naturality b)
    rw [hmul A y, h₁, h₂, hnat]
    change GeneralLinearGroup.scalar (Index.{u} n) z *
      (GeneralLinearGroup.scalar (Index.{u} n) z⁻¹ * X) = X
    rw [map_inv]
    exact mul_inv_cancel_left _ _
  · have hfin : IsFinite J.group.X.hom := by
      haveI : IsIso eIJ.inv.hom.hom.left :=
        Functor.map_isIso ((Grp.forget (SchemeOver k)) ⋙ Over.forget _) eIJ.inv
      haveI := hI
      rw [← Over.w eIJ.inv.hom.hom]
      infer_instance
    letI : IsFinite J.group.X.hom := hfin
    have hA : IsAffine J.group.X.left := isAffine_of_isAffineHom J.group.X.hom
    let Jalg : AffineAlgebraicGroup k := ⟨J.group, hA, inferInstance, inferInstance⟩
    let l := J.inclusion ≫ firstProjection T.group S.val ≫ t
    let r := J.inclusion ≫ secondProjection T.group S.val
    have hker (R : TestAlgebra k) (x : Points (T.group ⊗ S.val).X R) :
        x ∈ SubgroupSections J ((testSpec k).obj (op R)) ↔
          GeneralLinearGroup.scalar (Index.{u} n)
            (a.hom.app R (pointMap (firstProjection T.group S.val ≫ t) R x)) *
            SpecialLinearGroup.toGL (s.hom.app R (pointMap (secondProjection T.group S.val) R x)) =
          1 := by
      rw [schemeKernel_sections hJ, ← hmul R x, ← map_one (g.app R).groupIsoToMulEquiv]
      exact (g.app R).groupIsoToMulEquiv.injective.eq_iff.symm
    have hxy (R : TestAlgebra k) (x : Points J.group.X R) :
        GeneralLinearGroup.scalar (Index.{u} n) (a.hom.app R (pointMap l R x)) *
          SpecialLinearGroup.toGL (s.hom.app R (pointMap r R x)) = 1 :=
      (hker R (pointMap J.inclusion R x)).mp ⟨x, rfl⟩
    have hr (R : TestAlgebra k) (x : Points J.group.X R) :
        SpecialLinearGroup.toGL (s.hom.app R (pointMap r R x)) =
          GeneralLinearGroup.scalar (Index.{u} n) (a.hom.app R (pointMap l R x))⁻¹ := by
      simpa only [map_inv] using (eq_inv_of_mul_eq_one_right (hxy R x))
    let α := (groupPointsFunctor k).map l ≫ a.hom
    let β (R : TestAlgebra k) : ((groupPointsFunctor k).obj J.group).obj R →* rootsOfUnity n R :=
      (α.app R).hom.codRestrict (rootsOfUnity n R) (fun x => by
        have h := congrArg (GeneralLinearGroup.det : GeneralLinearGroup (Index.{u} n) R →* Rˣ)
          (hxy R x)
        apply (mem_rootsOfUnity n _).mpr
        change a.hom.app R (pointMap l R x) ^ n = 1
        simpa only [map_mul, SpecialLinearGroup.coeToGL_det, mul_one, detScalar, map_one] using h)
    have hβ (R : TestAlgebra k) : Function.Bijective (β R) := by
      constructor
      · intro x y h
        have hl : a.hom.app R (pointMap l R x) = a.hom.app R (pointMap l R y) :=
          congrArg Subtype.val h
        let p := J.inclusion ≫ firstProjection T.group S.val
        have hl' : pointMap l R x = pointMap l R y :=
          (a.app R).groupIsoToMulEquiv.injective hl
        have h₁ : pointMap p R x = pointMap p R y := by
          apply (((groupPointsFunctor k).mapIso (asIso t)).app R).groupIsoToMulEquiv.injective
          change pointMap t R (pointMap p R x) = pointMap t R (pointMap p R y)
          rw [← pointMap_comp, ← pointMap_comp]
          simpa only [p, l, Category.assoc] using hl'
        have h₂ : pointMap r R x = pointMap r R y := by
          apply (s.app R).groupIsoToMulEquiv.injective
          apply SpecialLinearGroup.toGL_injective
          change SpecialLinearGroup.toGL (s.hom.app R (pointMap r R x)) =
            SpecialLinearGroup.toGL (s.hom.app R (pointMap r R y))
          rw [hr R x, hr R y, hl]
        apply Unipotent.onPoints_injective J.inclusion J.isClosedImmersion R
        apply CartesianMonoidalCategory.hom_ext
        · exact (pointMap_comp _ _ x).symm.trans (h₁.trans (pointMap_comp _ _ y))
        · exact (pointMap_comp _ _ x).symm.trans (h₂.trans (pointMap_comp _ _ y))
      · intro z
        let V := GeneralLinearGroup.scalar (Index.{u} n) z.val⁻¹
        have hV : V.det = 1 := by
          change (GeneralLinearGroup.scalar (Index.{u} n) z.val⁻¹).det = 1
          rw [detScalar, inv_pow, (mem_rootsOfUnity n _).mp z.property, inv_one]
        let v := SpecialLinearGroup.toGLKerEquiv.symm ⟨V, hV⟩
        let a₁ := (a.app R).groupIsoToMulEquiv.symm z.val
        let x₁ := (((groupPointsFunctor k).mapIso (asIso t)).app R).groupIsoToMulEquiv.symm a₁
        let x₂ := (s.app R).groupIsoToMulEquiv.symm v
        let w := productPoint x₁ x₂
        have hw₁ : a.hom.app R (pointMap (firstProjection T.group S.val ≫ t) R w) = z.val := by
          change a.hom.app R (pointMap t R (pointMap (firstProjection T.group S.val) R w)) = _
          rw [productPoint_first]
          change (a.app R).groupIsoToMulEquiv
            ((((groupPointsFunctor k).mapIso (asIso t)).app R).groupIsoToMulEquiv x₁) = _
          rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        have hw₂ : SpecialLinearGroup.toGL (s.hom.app R (pointMap (secondProjection T.group S.val) R w)) =
            V := by
          rw [productPoint_second]
          change SpecialLinearGroup.toGL ((s.app R).groupIsoToMulEquiv x₂) = V
          rw [MulEquiv.apply_symm_apply]
          exact congrArg Subtype.val (SpecialLinearGroup.toGLKerEquiv.apply_symm_apply ⟨V, hV⟩)
        have hw := (hker R w).mpr (by
          rw [hw₁, hw₂]
          change GeneralLinearGroup.scalar (Index.{u} n) z.val *
            GeneralLinearGroup.scalar (Index.{u} n) z.val⁻¹ = 1
          rw [map_inv]
          exact mul_inv_cancel _)
        obtain ⟨x, hx⟩ := hw
        refine ⟨x, Subtype.ext ?_⟩
        change a.hom.app R (pointMap (firstProjection T.group S.val ≫ t) R
          (pointMap J.inclusion R x)) = z.val
        rw [show pointMap J.inclusion R x = w from hx, hw₁]
    let c : (groupPointsFunctor k).obj J.group ≅ rootsOfUnityPoints k n :=
      NatIso.ofComponents (fun R => (MulEquiv.ofBijective (β R) (hβ R)).toGrpIso) (by
        intro R A b
        apply GrpCat.ext
        intro x
        apply Subtype.ext
        exact congrArg (fun f => f x) (α.naturality b))
    letI : NeZero n := ⟨hn.ne'⟩
    obtain ⟨cyclic, hμ⟩ := DiagonalizableGroups.diagonalCyclic k n
    let e : J.group ≅ specGroup (rootsOfUnityCoordinates k n) :=
      Unipotent.groupIsoOfPoints (G := Jalg) (H := diagonalGroup k _) (c ≪≫ cyclic.symm)
    have he : (groupPointsFunctor k).mapIso e ≪≫ cyclic = c := by
      apply Iso.ext
      change (groupPointsFunctor k).map e.hom ≫ cyclic.hom = c.hom
      have h := Classical.choose_spec
        ((groupHomComparison k J.group (specGroup (rootsOfUnityCoordinates k n)) hA).2 (c ≪≫ cyclic.symm).hom)
      rw [show (groupPointsFunctor k).map e.hom = (c ≪≫ cyclic.symm).hom from h]
      simp
    refine ⟨J, e, cyclic, hJ, hfin, hcentral, hμ, ?_, ?_⟩
    · rw [he]
      exact fun R x => ⟨rfl, hr R x⟩
    · intro p _ hp hpn het
      letI : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero k hp.ne'⟩
      haveI := het
      haveI : IsIso e.inv.hom.hom.left :=
        Functor.map_isIso ((Grp.forget (SchemeOver k)) ⋙ Over.forget _) e.inv
      have hsm : Smooth (specGroup (rootsOfUnityCoordinates k n)).X.hom := by
        rw [← Over.w e.inv.hom.hom]
        infer_instance
      exact SmoothnessAndIsogenies.rootsOfUnityNonreduced k p n hn hpn
        ((affine_isReduced_iff _).mpr (SmoothnessAndIsogenies.reducedOfSmoothHopf _ hsm))

end

end LinearAlgebraicGroups.Reductive.GeneralLinearCentralIsogeny
