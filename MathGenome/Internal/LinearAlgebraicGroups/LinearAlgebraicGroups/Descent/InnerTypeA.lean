import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.InnerTypeA
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.MatrixAlgebraForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup
import Mathlib.Algebra.Ring.Action.End
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.RatFunc.Degree
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory WithConv
open scoped MatrixGroups TensorProduct

universe u w

namespace LinearAlgebraicGroups.Descent.InnerTypeA

noncomputable section

open Specification
open _root_.RM03.CSA _root_.RM03.CSA.NormOneGroup
open LinearAlgebraicGroups.Specs.StandardGroups
open Algebra.TensorProduct
open Matrix

set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

theorem reducedNormComparison : ReducedNormComparison.{u} := by
  intro k K _ _ _ A _ _ ι _ hA b s
  refine ⟨fun hK => reducedNorm_basis_baseChange hA b hK, genericReducedNorm_map hA b s,
    reducedNorm_mul hA, ?_, ?_, ?_⟩
  · intro a
    change MvPolynomial.eval (fun i => (b.baseChange k).repr (1 ⊗ₜ[k] a) i)
      (genericReducedNorm hA b) = reducedNorm hA a
    simp only [Module.Basis.baseChange_repr_tmul, smul_eq_mul, mul_one]
    exact reducedNorm_basis_eval hA b a
  · intro R x y
    exact ⟨(normHom hA b).map_one, (normHom hA b).map_mul x y⟩
  · intro R S f x
    exact normAt_natural hA b f.hom x

theorem cocycleOnTestAlgebras : CocycleOnTestAlgebras.{u} := by
  intro k K _ _ _ n A _ _ s d hd _ _ ρ c hρ hc R S σ G hG f hf x
  let j : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) S :=
    (algebraMap K S).mapMatrix
  have hcoeff (m : Matrix (Fin n) (Fin n) K) :
      f.hom.toRingHom.mapMatrix ((algebraMap K R).mapMatrix m) = j (m.map σ) := by
    ext p q
    exact hf (m p q)
  have hsmul (r : R) (m : Matrix (Fin n) (Fin n) R) :
      f.hom.toRingHom.mapMatrix (r • m) = f.hom r • f.hom.toRingHom.mapMatrix m := by
    ext p q
    simp [RingHom.mapMatrix_apply, smul_eq_mul]
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    let m := s (1 ⊗ₜ[k] a)
    have hm : ρ.act σ m = m := by simpa only [m, map_one] using hρ σ 1 a
    have h := congrArg j ((hc σ G hG m).symm.trans hm)
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [hd, hd]
    change f.hom r • j m = j (G : Matrix (Fin n) (Fin n) K) *
      f.hom.toRingHom.mapMatrix (r • ((algebraMap K R).mapMatrix m)) *
      j (↑G⁻¹ : Matrix (Fin n) (Fin n) K)
    rw [hsmul, hcoeff, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simpa only [map_mul] using h.symm
  | add x y hx hy =>
    change d S (Algebra.TensorProduct.map f.hom (.id k A) (x + y)) =
      j (G : Matrix (Fin n) (Fin n) K) * f.hom.toRingHom.mapMatrix (d R (x + y)) *
        j (↑G⁻¹ : Matrix (Fin n) (Fin n) K)
    simp only [map_add, Matrix.add_mul, Matrix.mul_add]
    exact congrArg₂ (· + ·) hx hy

open private Representation Representation.mk Representation.equiv Representation.naturality Representation.operations Representation.represents
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

open private coord_change isUnit_of_includeRight
  from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup

section NormOne

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]
variable {ι : Type u} [Fintype ι]
variable (hA : IsCentralSimple k A) (b : Module.Basis ι k A)

local notation "I" => normOneIdeal hA b
local notation "Q" => NormOneCoordinates hA b
local notation "q" => Ideal.Quotient.mkₐ k I

private def normOneEvaluate (R : TestAlgebra k) (f : Q →ₐ[k] R) :
    (normOneFunctor hA b).obj R := by
  classical
  let c : ι → R := fun i => f (q (MvPolynomial.X i))
  let x := ((b.baseChange R).equivFun).symm c
  have hx (i : ι) : (b.baseChange R).repr x i = c i :=
    congrFun ((b.baseChange R).equivFun.apply_symm_apply c) i
  have hf : MvPolynomial.aeval c = f.comp q := by
    ext i
    simp [c]
  refine ⟨x, ?_⟩
  change MvPolynomial.eval₂ (algebraMap k R) (fun i => (b.baseChange R).repr x i)
    (genericReducedNorm hA b) = 1
  rw [show (fun i => (b.baseChange R).repr x i) = c from funext hx]
  change MvPolynomial.aeval c (genericReducedNorm hA b) = 1
  rw [hf]
  have hq : q (genericReducedNorm hA b) = 1 := by
    have h : q (genericReducedNorm hA b - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simpa only [map_sub, map_one, sub_eq_zero] using h
  change f (q (genericReducedNorm hA b)) = 1
  rw [hq, map_one]

private theorem normOneEvaluate_coord (R : TestAlgebra k) (f : Q →ₐ[k] R) (i : ι) :
    (b.baseChange R).repr (normOneEvaluate hA b R f).1 i = f (q (MvPolynomial.X i)) :=
  congrFun ((b.baseChange R).equivFun.apply_symm_apply _) i

private def normOneEvaluationHom (R : TestAlgebra k) (x : (normOneFunctor hA b).obj R) :
    Q →ₐ[k] R :=
  let f := MvPolynomial.aeval (fun i => (b.baseChange R).repr x.1 i)
  Ideal.Quotient.liftₐ I f (by
    intro p hp
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hp
    have h : f (_root_.Specs.RM03.CSA.genericReducedNorm (show _root_.Specs.RM03.CSA.isCentralSimple k A from hA) b) = 1 := x.2
    rw [map_mul, map_sub, h, map_one, sub_self, zero_mul])

private theorem normOneEvaluationHom_coord (R : TestAlgebra k)
    (x : (normOneFunctor hA b).obj R) (i : ι) :
    normOneEvaluationHom hA b R x (q (MvPolynomial.X i)) = (b.baseChange R).repr x.1 i :=
  MvPolynomial.aeval_X _ _

private def normOneRepresentation : Representation Q (normOneFunctor hA b) :=
  Representation.mk (fun R =>
    { toFun := normOneEvaluate hA b R
      invFun := normOneEvaluationHom hA b R
      left_inv f := by
        apply Ideal.Quotient.algHom_ext k
        ext i
        exact (normOneEvaluationHom_coord hA b R _ i).trans (normOneEvaluate_coord hA b R f i)
      right_inv x := by
        apply Subtype.ext
        apply (b.baseChange R).equivFun.injective
        funext i
        exact (normOneEvaluate_coord hA b R _ i).trans (normOneEvaluationHom_coord hA b R x i) }) (by
    intro _ _ a f
    apply Subtype.ext
    apply (b.baseChange _).equivFun.injective
    funext i
    change (b.baseChange _).repr (normOneEvaluate hA b _ (a.hom.comp f)).1 i =
      (b.baseChange _).repr (changeCoefficients a.hom (normOneEvaluate hA b _ f).1) i
    rw [coord_change, normOneEvaluate_coord, normOneEvaluate_coord, AlgHom.comp_apply])

theorem normOneRepresentability : NormOneRepresentability.{u} := by
  intro k _ A _ _ ι _ hA b
  let P := normOneRepresentation hA b
  refine ⟨(Representation.operations P), normOneFunctor hA b, fun _ => Equiv.refl _, ?_, ?_, ?_, ?_⟩
  · intro R
    rfl
  · intro R a b
    rfl
  · intro R S f x
    rfl
  · exact Representation.represents P _ (fun R f i => normOneEvaluate_coord hA b R f i)

end NormOne

section Units

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]
variable {ι : Type u} [Fintype ι]
variable (hA : IsCentralSimple k A) (b : Module.Basis ι k A)

private theorem isUnit_normAt_iff (R : TestAlgebra k) (x : R ⊗[k] A) :
    IsUnit (normAt hA b x) ↔ IsUnit x := by
  refine ⟨fun hx => ?_, fun hx => hx.map (normHom hA b)⟩
  obtain ⟨s⟩ := algEquiv_matrix_algebraicClosure hA
  let L := AlgebraicClosure k
  let T := L ⊗[k] R
  let f : R →ₐ[k] T := includeRight
  have hd : IsUnit (extendSplitting s (changeCoefficients f x)).det := by
    rw [← normAt_eq_det hA b s, normAt_natural]
    exact hx.map f
  have hm := (Matrix.isUnit_iff_isUnit_det _).2 hd
  have ht : IsUnit (changeCoefficients f x) := by
    simpa only [AlgEquiv.symm_apply_apply] using hm.map (extendSplitting s).symm
  let a := Algebra.TensorProduct.assoc k k L L R A
  have he (y : R ⊗[k] A) : a (changeCoefficients f y) = 1 ⊗ₜ[k] y := by
    induction y using TensorProduct.inductionOn with
    | tmul r v => rfl
    | add y z hy hz => simp [hy, hz, TensorProduct.tmul_add]
  exact isUnit_of_includeRight x (he x ▸ ht.map a)

private def unitFunctor (k : Type u) [Field k] (A : Type u) [Ring A] [Algebra k A] :
    TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (R ⊗[k] A)ˣ
  map f := GrpCat.ofHom (Units.map (changeCoefficients (A := A) f.hom).toMonoidHom)
  map_id R := by
    apply GrpCat.ext
    intro x
    apply Units.ext
    simp [changeCoefficients, Algebra.TensorProduct.map_id]
  map_comp f g := by
    apply GrpCat.ext
    intro x
    apply Units.ext
    have h := Algebra.TensorProduct.map_comp g.hom f.hom (AlgHom.id k A) (AlgHom.id k A)
    exact DFunLike.congr_fun (by simpa only [AlgHom.id_comp] using h) x.val

local notation "P" => MvPolynomial ι k
local notation "N" => _root_.Specs.RM03.CSA.genericReducedNorm
  (hA : _root_.Specs.RM03.CSA.isCentralSimple k A) b
local notation "U" => UnitCoordinates hA b
local notation "j" => algebraMap P U

private def unitEvaluate (R : TestAlgebra k) (f : U →ₐ[k] R) :
    (unitFunctor k A).obj R := by
  let c : ι → R := fun i => f (j (MvPolynomial.X i))
  let x := ((b.baseChange R).equivFun).symm c
  have hx (i : ι) : (b.baseChange R).repr x i = c i :=
    congrFun ((b.baseChange R).equivFun.apply_symm_apply c) i
  have hf : MvPolynomial.aeval c = f.comp (IsScalarTower.toAlgHom k P U) := by
    ext i
    simp [c]
  have hn : IsUnit (normAt hA b x) := by
    change IsUnit (MvPolynomial.aeval (fun i => (b.baseChange R).repr x i) N)
    rw [show (fun i => (b.baseChange R).repr x i) = c from funext hx, hf]
    exact (IsLocalization.Away.algebraMap_isUnit N).map f
  exact ((isUnit_normAt_iff hA b R x).1 hn).unit

private theorem unitEvaluate_coord (R : TestAlgebra k) (f : U →ₐ[k] R) (i : ι) :
    (b.baseChange R).repr (unitEvaluate hA b R f).val i = f (j (MvPolynomial.X i)) := by
  unfold unitEvaluate
  rw [IsUnit.unit_spec]
  exact congrFun ((b.baseChange R).equivFun.apply_symm_apply _) i

private def unitEvaluationHom (R : TestAlgebra k) (x : (unitFunctor k A).obj R) :
    U →ₐ[k] R :=
  IsLocalization.Away.liftAlgHom N
    (f := MvPolynomial.aeval (fun i => (b.baseChange R).repr x.val i))
    ((isUnit_normAt_iff hA b R x.val).2 x.isUnit)

private theorem unitEvaluationHom_coord (R : TestAlgebra k)
    (x : (unitFunctor k A).obj R) (i : ι) :
    unitEvaluationHom hA b R x (j (MvPolynomial.X i)) = (b.baseChange R).repr x.val i := by
  rw [unitEvaluationHom, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact MvPolynomial.aeval_X _ _

private def unitRepresentation : Representation U (unitFunctor k A) :=
  Representation.mk (fun R =>
    { toFun := unitEvaluate hA b R
      invFun := unitEvaluationHom hA b R
      left_inv f := by
        apply AlgHom.toRingHom_injective
        apply IsLocalization.ringHom_ext (Submonoid.powers N)
        have he : (unitEvaluationHom hA b R (unitEvaluate hA b R f)).comp
            (IsScalarTower.toAlgHom k P U) = f.comp (IsScalarTower.toAlgHom k P U) := by
          ext i
          exact (unitEvaluationHom_coord hA b R _ i).trans (unitEvaluate_coord hA b R f i)
        exact congrArg AlgHom.toRingHom he
      right_inv x := by
        apply Units.ext
        apply (b.baseChange R).equivFun.injective
        funext i
        exact (unitEvaluate_coord hA b R _ i).trans (unitEvaluationHom_coord hA b R x i) }) (by
    intro _ _ f h
    apply Units.ext
    apply (b.baseChange _).equivFun.injective
    funext i
    change (b.baseChange _).repr (unitEvaluate hA b _ (f.hom.comp h)).val i =
      (b.baseChange _).repr (changeCoefficients f.hom (unitEvaluate hA b _ h).val) i
    rw [coord_change, unitEvaluate_coord, unitEvaluate_coord, AlgHom.comp_apply])

theorem unitGroupRepresentability : UnitGroupRepresentability.{u} := by
  intro k _ A _ _ ι _ hA b
  let M := unitRepresentation hA b
  exact ⟨(Representation.operations M), unitFunctor k A, fun _ => MulEquiv.refl _, fun _ _ => rfl,
    Representation.represents M _ (fun R f i => unitEvaluate_coord hA b R f i)⟩

end Units

open private Representation.hopf Representation.convolutionIso spectrumPointsIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

private theorem representedEvaluation {k C : Type u} [Field k] [CommRing C] [Algebra k C]
    [Algebra.FiniteType k C] {F : TestAlgebra k ⥤ GrpCat.{u}} (P : Representation C F)
    (R : TestAlgebra k) (f : C →ₐ[k] R) :
    letI := Representation.hopf P
    (spectrumPointsIso (Representation.convolutionIso P)).hom.app R
      ((hopfSpecPointIso (CommHopfAlgCat.of k C)).hom.app R (toConv f)) =
        Representation.equiv P R f := by
  letI := Representation.hopf P
  let e := hopfSpecPointIso (CommHopfAlgCat.of k C)
  have h : e ≪≫ spectrumPointsIso (Representation.convolutionIso P) =
      Representation.convolutionIso P := by simp [e, spectrumPointsIso]
  exact congrArg (fun j => j.hom.app R (toConv f)) h

private def affineGroupIso {k : Type u} [Field k] {G H : Specs.GroupScheme k}
    (hG : IsAffine G.X.left) (hH : IsAffine H.X.left)
    (e : (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj H) : G ≅ H := by
  let f := (groupHomEquiv G H hG).symm e.hom
  let g := (groupHomEquiv H G hH).symm e.inv
  have hf : (groupPointsFunctor k).map f = e.hom :=
    (groupHomEquiv G H hG).apply_symm_apply _
  have hg : (groupPointsFunctor k).map g = e.inv :=
    (groupHomEquiv H G hH).apply_symm_apply _
  refine ⟨f, g, ?_, ?_⟩
  · apply (groupHomEquiv G G hG).injective
    change (groupPointsFunctor k).map (f ≫ g) = (groupPointsFunctor k).map (𝟙 G)
    rw [Functor.map_comp, hf, hg, Iso.hom_inv_id]
    exact ((groupPointsFunctor k).map_id G).symm
  · apply (groupHomEquiv H H hH).injective
    change (groupPointsFunctor k).map (g ≫ f) = (groupPointsFunctor k).map (𝟙 H)
    rw [Functor.map_comp, hg, hf, Iso.inv_hom_id]
    exact ((groupPointsFunctor k).map_id H).symm

private theorem affineGroupIso_hom {k : Type u} [Field k] {G H : Specs.GroupScheme k}
    (hG : IsAffine G.X.left) (hH : IsAffine H.X.left)
    (e : (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj H) :
    (groupPointsFunctor k).map (affineGroupIso hG hH e).hom = e.hom :=
  (groupHomEquiv G H hG).apply_symm_apply _

private def baseChangePointIso {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : Specs.GroupScheme k) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj G) ≅
      restrictTestAlgebra k K ⋙ (groupPointsFunctor k).obj G :=
  NatIso.ofComponents (fun R => (baseChangePointGroupEquiv K G R).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro x
    exact baseChangePointsNaturality k K G.X f x)

private theorem baseChangeGroupPointNaturality {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H : Specs.GroupScheme k} (f : G ⟶ H) (R : TestAlgebra K)
    (p : Points ((groupBaseChange k K).obj G).X R) :
    baseChangePoint k K H.X R (p ≫ ((groupBaseChange k K).map f).hom.hom) =
      baseChangePoint k K G.X R p ≫ f.hom.hom :=
  baseChangePointsSchemeNaturality k K f.hom.hom R p

private def liftSpecialLinear {R : Type u} [CommRing R] (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) R ≃*
      Matrix.SpecialLinearGroup (ULift.{u} (Fin n)) R where
  toFun x := ⟨Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm x.val,
    (Matrix.det_reindex_self _ _).trans x.prop⟩
  invFun x := ⟨Matrix.reindex Equiv.ulift Equiv.ulift x.val,
    (Matrix.det_reindex_self _ _).trans x.prop⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' x y := Subtype.ext ((Matrix.reindexRingEquiv R Equiv.ulift.symm).map_mul x.val y.val)

private def splitNormOnePoints {k K : Type u} [Field k] [Field K] [Algebra k K]
    {A : Type u} [Ring A] [Algebra k A] {ι : Type u} [Fintype ι]
    (hA : IsCentralSimple k A) (b : Module.Basis ι k A)
    (s : (K ⊗[k] A) ≃ₐ[K] Matrix (Fin (degree k A)) (Fin (degree k A)) K) :
    restrictTestAlgebra k K ⋙ normOneFunctor hA b ≅
      specialLinearPoints K (ULift.{u} (Fin (degree k A))) :=
  NatIso.ofComponents (fun R =>
    ((normOneSplit (R := restrictTestAlgebraObj k K R) hA b s).trans
      (liftSpecialLinear _)).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    let T := restrictTestAlgebraObj k K R
    let U := restrictTestAlgebraObj k K S
    let l := liftSpecialLinear (R := U) (degree k A)
    have h := normOneSplit_natural (R := T) (S := U) hA b s f.hom x
    exact congrArg (fun y => (l y).val) h)

private theorem affine_baseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOver k) (hX : IsAffine X.left) : IsAffine ((baseChange k K).obj X).left := by
  let : IsAffine X.left := hX
  change IsAffine (Limits.pullback X.hom (fieldSpecMap k K))
  infer_instance

theorem specialLinearSplitting : SpecialLinearSplitting.{u} := by
  intro k K _ _ _ A _ _ ι _ hA b s
  let I := ULift.{u} (Fin (degree k A))
  let P := normOneRepresentation hA b
  letI := Representation.hopf P
  let G := Specs.StandardGroups.spectrum k (NormOneCoordinates hA b)
  obtain ⟨_, J, _, _, _, _, _, _, _, hJ⟩ :=
    LinearAlgebraicGroups.StandardGroups.specialLinearGroupSpecification K I
  letI := J.hopf
  let L := Specs.StandardGroups.spectrum K (SLCoordinates K I)
  obtain ⟨_, _, z, _⟩ := hJ
  let e := spectrumPointsIso (Representation.convolutionIso P)
  let d (R : TestAlgebra K) := extendSplitting (R := restrictTestAlgebraObj k K R) s
  let t := baseChangePointIso (K := K) G.val ≪≫ ((Functor.whiskeringLeft _ _ _).obj (restrictTestAlgebra k K)).mapIso e ≪≫
    splitNormOnePoints hA b s ≪≫ z.symm
  let j := affineGroupIso (affine_baseChange G.val.X G.property.1) L.property.1 t
  refine ⟨(Representation.operations P), J, normOneFunctor hA b, fun _ => Equiv.refl _, e, z, j, d,
    fun R r a => extendSplitting_tmul (R := restrictTestAlgebraObj k K R) s r a,
    cocycleOnTestAlgebras s d (fun R r a =>
      extendSplitting_tmul (R := restrictTestAlgebraObj k K R) s r a), (fun _ _ => rfl), ?_, ?_⟩
  · intro R f p hp i
    let f' := (hopfSpecPointIso (CommHopfAlgCat.of k (NormOneCoordinates hA b))).hom.app R (toConv f)
    have he : p = f' := by
      apply Over.OverMorphism.ext
      exact hp
    subst p
    have h := representedEvaluation P R f
    change e.hom.app R f' = normOneEvaluate hA b R f at h
    rw [h]
    exact normOneEvaluate_coord hA b R f i
  · intro R p i j₀
    have hj : (groupPointsFunctor K).map j.hom = t.hom := affineGroupIso_hom _ _ _
    change (show Matrix.SpecialLinearGroup I R from
        z.hom.app R (((groupPointsFunctor K).map j.hom).app R p)).val i j₀ = _
    rw [hj]
    change (show Matrix.SpecialLinearGroup I R from z.hom.app R
      (z.inv.app R ((splitNormOnePoints hA b s).hom.app R
        (e.hom.app _ (baseChangePoint k K G.val.X R p))))).val i j₀ = _
    have hz := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (z.inv_hom_id_app R))
      ((splitNormOnePoints hA b s).hom.app R (e.hom.app _ (baseChangePoint k K G.val.X R p)))
    change z.hom.app R (z.inv.app R _) = _ at hz
    rw [hz]
    rfl

section Projective

open LinearAlgebraicGroups.Specs
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open LaurentPolynomial
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes

private def scalarUnitPoints (k : Type u) [Field k] (A : Type u) [Ring A] [Algebra k A] :
    multiplicativePoints k ⟶ unitFunctor k A where
  app R := GrpCat.ofHom (Units.map (algebraMap R (R ⊗[k] A)).toMonoidHom)
  naturality R S f := by
    apply GrpCat.ext
    intro a
    apply Units.ext
    change changeCoefficients f.hom (a.val ⊗ₜ[k] (1 : A)) = f.hom a.val ⊗ₜ[k] (1 : A)
    simp [changeCoefficients]

open scoped CategoryTheory.MonObj in
private theorem centralScalarSubgroup {k A : Type u} [Field k] [Ring A] [Algebra k A]
    {M U : AffineAlgebraicGroup k}
    (m : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k)
    (e : (groupPointsFunctor k).obj U.val ≅ unitFunctor k A) (i : M.val ⟶ U.val)
    (hi : ∀ (R : TestAlgebra k) (x : Points M.val.X R),
      e.hom.app R (x ≫ i.hom.hom) =
        Units.map (algebraMap R (R ⊗[k] A)).toMonoidHom (m.hom.app R x)) :
    IsNormalSubgroup i := by
  let X := U.val.X
  let Y := M.val.X
  refine ⟨snd X Y, ?_⟩
  apply hom_ext_of_points (X := X ⊗ Y)
  · haveI : IsAffine X.left := U.property.1
    haveI : IsAffine Y.left := M.property.1
    change IsAffine (Limits.pullback X.hom Y.hom)
    infer_instance
  · intro R p
    let x : Points X R := p ≫ fst X Y
    let y : Points Y R := p ≫ snd X Y
    let z : Points X R := y ≫ i.hom.hom
    have hz : p ≫ (snd X Y ≫ i.hom.hom) = z := (Category.assoc _ _ _).symm
    rw [hz, subgroupConjugation, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hz]
    change z = x * z * x⁻¹
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app R)).1
    change (e.hom.app R).hom z = (e.hom.app R).hom (x * z * x⁻¹)
    rw [map_mul, map_mul, map_inv]
    have hs : (e.hom.app R).hom z =
      Units.map (algebraMap R (R ⊗[k] A)).toMonoidHom (m.hom.app R y) := hi R y
    rw [hs]
    set a := (e.hom.app R).hom x
    set b := m.hom.app R y
    have h : Commute a (Units.map (algebraMap R (R ⊗[k] A)).toMonoidHom b) := by
      apply Units.ext
      exact (Algebra.commutes b.val (show (R ⊗[k] A)ˣ from a).val).symm
    rw [h.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem laurent_surjective_of_generator_inverse {k C : Type u} [Field k]
    [CommRing C] [Algebra k C] (c : C →ₐ[k] LaurentPolynomial k)
    (hp : T 1 ∈ c.range) (hn : T (-1) ∈ c.range) : Function.Surjective c := by
  intro p
  change p ∈ c.range
  induction p using LaurentPolynomial.induction_on with
  | h_C a => rw [C_eq_algebraMap]; exact c.range.algebraMap_mem a
  | h_add hp hq => exact c.range.add_mem hp hq
  | h_C_mul_T n a hh => rw [T_add, ← mul_assoc]; exact c.range.mul_mem hh hp
  | h_C_mul_T_Z n a hh =>
    rw [sub_eq_add_neg, T_add, ← mul_assoc]
    exact c.range.mul_mem hh hn

private theorem scalarCoordinatesSurjective {k A ι : Type u} [Field k]
    [Ring A] [Algebra k A] [Fintype ι] (hA : IsCentralSimple k A) (b : Module.Basis ι k A)
    (c : UnitCoordinates hA b →ₐ[k] LaurentPolynomial k)
    (t : (LaurentPolynomial k)ˣ) (ht : t.val = T 1)
    (hc : unitEvaluate hA b (CommAlgCat.of k (LaurentPolynomial k)) c =
      Units.map (algebraMap (LaurentPolynomial k) (LaurentPolynomial k ⊗[k] A)).toMonoidHom t) :
    Function.Surjective c := by
  letI : IsSimpleRing A := hA.1
  obtain ⟨i, hi⟩ : ∃ i, b.repr (1 : A) i ≠ 0 := by
    by_contra! h
    have hh : b.repr (1 : A) = b.repr 0 := by
      ext j
      simpa only [map_zero, Finsupp.zero_apply] using h j
    exact one_ne_zero (b.repr.injective hh)
  let d := b.repr (1 : A) i
  let R := CommAlgCat.of k (LaurentPolynomial k)
  let U := UnitCoordinates hA b
  let v := unitEvaluate hA b (CommAlgCat.of k U) (.id k U)
  let j := algebraMap (MvPolynomial ι k) U
  have hv : Units.map (changeCoefficients c).toMonoidHom v = unitEvaluate hA b R c := by
    have h := (Representation.naturality (unitRepresentation hA b) (CommAlgCat.ofHom c)
      (AlgHom.id k U)).symm
    change Units.map (changeCoefficients c).toMonoidHom v =
      unitEvaluate hA b R (c.comp (AlgHom.id k U)) at h
    have hh : c.comp (AlgHom.id k U) = c := AlgHom.comp_id c
    rw [hh] at h
    exact h
  have hcoeff (w : (U ⊗[k] A)ˣ) (z : Rˣ)
      (hw : Units.map (changeCoefficients c).toMonoidHom w =
        Units.map (algebraMap R (R ⊗[k] A)).toMonoidHom z) :
      z.val ∈ c.range := by
    refine ⟨algebraMap k U d⁻¹ * (b.baseChange U).repr w.val i, ?_⟩
    change c (algebraMap k U d⁻¹ * (b.baseChange U).repr w.val i) = z.val
    rw [map_mul, AlgHom.commutes, ← coord_change b c]
    have he := congrArg Units.val hw
    change changeCoefficients c w.val = (z.val ⊗ₜ[k] (1 : A)) at he
    rw [he, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, ← mul_assoc]
    change (algebraMap k (LaurentPolynomial k)) d⁻¹ *
      (algebraMap k (LaurentPolynomial k)) d * z.val = z.val
    rw [← map_mul, inv_mul_cancel₀ hi, map_one, one_mul]
  have hp := hcoeff v t (hv.trans hc)
  have hn := hcoeff v⁻¹ t⁻¹ (by rw [map_inv, map_inv, hv, hc])
  rw [ht] at hp
  have ht' : (t⁻¹).val = (T (-1) : LaurentPolynomial k) := by
    apply (Units.mul_right_inj t).mp
    rw [Units.mul_inv, ht, ← T_add, add_neg_cancel, T_zero]
  rw [ht'] at hn
  exact laurent_surjective_of_generator_inverse c hp hn

theorem projectiveModel : ProjectiveModel.{u} := by
  intro k _ A _ _ ι _ hA b
  let P := unitRepresentation hA b
  letI := Representation.hopf P
  let U := Specs.StandardGroups.spectrum k (UnitCoordinates hA b)
  let e := spectrumPointsIso (Representation.convolutionIso P)
  obtain ⟨H, _, _, _, hM⟩ :=
    LinearAlgebraicGroups.StandardGroups.multiplicativeGroupSpecification k
  letI := H.hopf
  let M := Specs.StandardGroups.spectrum k (LaurentPolynomial k)
  obtain ⟨eM, hEM, m, hmEval⟩ := hM
  let τ := m.hom ≫ scalarUnitPoints k A ≫ e.inv
  obtain ⟨i, hi⟩ := (groupHomComparison k M.val U.val M.property.1).2 τ
  have hp (R : TestAlgebra k) (a : Points M.val.X R) :
      e.hom.app R (a ≫ i.hom.hom) =
        Units.map (algebraMap R (R ⊗[k] A)).toMonoidHom (m.hom.app R a) := by
    have h := congrArg (fun f ↦ (f.app R) a) hi
    change a ≫ i.hom.hom = e.inv.app R
      (Units.map (algebraMap R (R ⊗[k] A)).toMonoidHom (m.hom.app R a)) at h
    rw [h, ← GrpCat.comp_apply, e.inv_hom_id_app]
    rfl
  let R := CommAlgCat.of k (LaurentPolynomial k)
  let a : Points M.val.X R := eM.hom.app R (toConv (AlgHom.id k R))
  let t : Rˣ := m.hom.app R a
  have ht : t.val = T 1 := hmEval R (AlgHom.id k R)
  let eU := hopfSpecPointIso (CommHopfAlgCat.of k (UnitCoordinates hA b))
  let c : UnitCoordinates hA b →ₐ[k] R := (eU.inv.app R (a ≫ i.hom.hom)).ofConv
  have hc : eU.hom.app R (toConv c) = a ≫ i.hom.hom := by
    change eU.hom.app R (eU.inv.app R (a ≫ i.hom.hom)) = _
    rw [← GrpCat.comp_apply, eU.inv_hom_id_app]
    rfl
  have hcs : i.hom.hom.left = Spec.map (CommRingCat.ofHom c.toRingHom) := by
    have ha : a.left = 𝟙 (Spec (CommRingCat.of R)) :=
      (hEM R (AlgHom.id k R)).trans (Spec.map_id _)
    have h := congrArg Over.Hom.left hc
    let g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (UnitCoordinates hA b)) :=
      i.hom.hom.left
    change Spec.map (CommRingCat.ofHom c.toRingHom) = a.left ≫ g at h
    change g = _
    rw [ha] at h
    exact (Category.id_comp g).symm.trans h.symm
  have hclosed : IsClosedImmersion i.hom.hom.left := by
    rw [hcs]
    apply IsClosedImmersion.spec_of_surjective
    apply scalarCoordinatesSurjective hA b c t ht
    have h := hp R a
    rw [← hc] at h
    have he := representedEvaluation P R c
    change e.hom.app R (eU.hom.app R (toConv c)) = unitEvaluate hA b R c at he
    rw [he] at h
    exact h
  have hn := centralScalarSubgroup m e i hp
  refine ⟨Representation.operations P, H, unitFunctor k A, fun _ => MulEquiv.refl _, e, m,
    i, hclosed, (fun _ _ => rfl), ?_, hp, hn, ?_⟩
  · intro S f p hs j
    let g := (eU.hom.app S (toConv f) : Points U.val.X S)
    have hg : p = g := Over.OverMorphism.ext hs
    subst p
    have he := representedEvaluation P S f
    change e.hom.app S g = unitEvaluate hA b S f at he
    rw [he]
    exact unitEvaluate_coord hA b S f j
  · let B : ClosedSubgroup U.val := ⟨M.val, i, hclosed⟩
    obtain ⟨_, _, Q, q, _, _, hq, _, _, eq, heq⟩ := normalAffineQuotient U B hn
    exact ⟨Q, q, hq, eq, heq⟩

open CategoryTheory.Limits
open LinearAlgebraicGroups.HomogeneousQuotient
open private compareRepresentatives compareRepresentatives_projection baseChangeMapIsPullback
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient

private def unitPointIso {k A : Type u} [Field k] [Ring A] [Algebra k A]
    (F : TestAlgebra k ⥤ GrpCat.{u}) (p : ∀ R : TestAlgebra k, F.obj R ≃* (R ⊗[k] A)ˣ)
    (h : ∀ {R S : TestAlgebra k} (a : R ⟶ S) (x : F.obj R),
      p S (F.map a x) = Units.map (changeCoefficients a.hom).toMonoidHom (p R x)) :
    F ≅ unitFunctor k A :=
  NatIso.ofComponents (fun R => (p R).toGrpIso) (by
    intro R S a
    apply GrpCat.ext
    intro x
    exact h a x)

private def splitUnitPoints {k K A : Type u} [Field k] [Field K] [Algebra k K]
    [Ring A] [Algebra k A] {n : ℕ}
    (s : (K ⊗[k] A) ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    restrictTestAlgebra k K ⋙ unitFunctor k A ≅
      generalLinearPoints K (ULift.{u} (Fin n)) :=
  NatIso.ofComponents (fun R =>
    ((Units.mapEquiv (extendSplitting (R := restrictTestAlgebraObj k K R) s).toMulEquiv).trans
      MatrixAlgebraForms.liftMatrix).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro x
    apply Units.ext
    have h := extendSplitting_natural (R := restrictTestAlgebraObj k K R)
      (S := restrictTestAlgebraObj k K S) s f.hom x.val
    exact congrArg (Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm) h)

private def restrictScalarPoints {k K : Type u} [Field k] [Field K] [Algebra k K] :
    restrictTestAlgebra k K ⋙ multiplicativePoints k ≅ multiplicativePoints K :=
  NatIso.ofComponents (fun _ => (MulEquiv.refl _).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro x
    rfl)

private def restrictLinearPoints {k K : Type u} [Field k] [Field K] [Algebra k K]
    (I : Type u) [Fintype I] [DecidableEq I] :
    restrictTestAlgebra k K ⋙ generalLinearPoints k I ≅ generalLinearPoints K I :=
  NatIso.ofComponents (fun _ => (MulEquiv.refl _).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro x
    rfl)

open scoped CategoryTheory.MonObj in
private def projectiveMatrixHom {k : Type u} [Field k] {n : ℕ}
    (P : MatrixAlgebraForms.ProjectivePresentation k n) (R : TestAlgebra k) :
    GL (Fin n) R →* Points P.projectiveGroup.val.X R :=
  (((groupPointsFunctor k).map P.projection).app R).hom.comp
    ((P.linearPoints.inv.app R).hom.comp MatrixAlgebraForms.liftMatrix.toMonoidHom)

private theorem projectiveMatrixPoint_natural {k : Type u} [Field k] {n : ℕ}
    (P : MatrixAlgebraForms.ProjectivePresentation k n) {R S : TestAlgebra k}
    (f : R ⟶ S) (g : GL (Fin n) R) :
    mapPoints f (projectiveMatrixPoint P R g) =
      projectiveMatrixPoint P S (GeneralLinearGroup.map f.hom.toRingHom g) := by
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (P.linearPoints.inv.naturality f))
    (MatrixAlgebraForms.liftMatrix g)
  change P.linearPoints.inv.app S
        (GeneralLinearGroup.map f.hom.toRingHom (MatrixAlgebraForms.liftMatrix g)) =
      mapPoints f (P.linearPoints.inv.app R (MatrixAlgebraForms.liftMatrix g)) at h
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ P.projection.hom.hom) h.symm)

/-- Changing only the (K)-algebra structure makes the identity on the
underlying ring `σ`-semilinear from the original test algebra. -/
private abbrev twistTestAlgebra {k K : Type u} [Field k] [Field K] [Algebra k K]
    (σ : Gal(K/k)) (R : TestAlgebra K) : TestAlgebra K :=
  letI : Algebra K R := ((algebraMap K R).comp σ.symm.toRingHom).toAlgebra
  CommAlgCat.of K R

private def testAlgebraHom {k : Type u} [Field k] {R S : TestAlgebra k}
    (f : R →+* S) (h : ∀ a : k, f (algebraMap k R a) = algebraMap k S a) : R ⟶ S :=
  CommAlgCat.ofHom ⟨f, h⟩

private def twistIdentity {k K : Type u} [Field k] [Field K] [Algebra k K]
    (σ : Gal(K/k)) (R : TestAlgebra K) :
    restrictTestAlgebraObj k K R ⟶ restrictTestAlgebraObj k K (twistTestAlgebra σ R) :=
  ConcreteCategory.ofHom (C := CommAlgCat k)
    ({ toRingHom := RingHom.id R
       commutes' := fun a => congrArg (algebraMap K R) (σ.symm.commutes a).symm } :
      restrictTestAlgebraObj k K R →ₐ[k] restrictTestAlgebraObj k K (twistTestAlgebra σ R))

private def twistMap {k K : Type u} [Field k] [Field K] [Algebra k K]
    (σ : Gal(K/k)) {R S : TestAlgebra K} (f : R ⟶ S) :
    twistTestAlgebra σ R ⟶ twistTestAlgebra σ S :=
  testAlgebraHom (R := twistTestAlgebra σ R) (S := twistTestAlgebra σ S)
    f.hom.toRingHom (fun a => f.hom.commutes (σ.symm a))

private theorem twistIdentity_comm {k K : Type u} [Field k] [Field K] [Algebra k K]
    (σ : Gal(K/k)) {R S : TestAlgebra K} (f : R ⟶ S) :
    (restrictTestAlgebra k K).map f ≫ twistIdentity σ S =
      twistIdentity σ R ≫ (restrictTestAlgebra k K).map (twistMap σ f) := by
  ext r
  rfl

open scoped CategoryTheory.MonObj in
private theorem projectiveCocycleOnLift {k K A : Type u} [Field k] [Field K] [Algebra k K]
    [Ring A] [Algebra k A] {n : ℕ}
    {s : (K ⊗[k] A) ≃ₐ[K] Matrix (Fin n) (Fin n) K}
    {d : ∀ R : TestAlgebra K, (restrictTestAlgebraObj k K R ⊗[k] A) ≃ₐ[R]
      Matrix (Fin n) (Fin n) R}
    (hd : IsCocycleComparison s d)
    [FiniteDimensional k K] [IsGalois k K]
    (ρ : _root_.RM03.Brauer.SemilinearDescent.AlgebraAction k K (Matrix (Fin n) (Fin n) K))
    (c : _root_.RM03.Brauer.ProjectiveClassification.Cocycle k K n)
    (hρ : _root_.RM03.Brauer.ProjectiveClassification.IsTransport ρ s)
    (hc : _root_.RM03.Brauer.ProjectiveClassification.Implements ρ c)
    (P : MatrixAlgebraForms.ProjectivePresentation k n)
    {R S : TestAlgebra K} (σ : Gal(K/k)) (G : GL (Fin n) K)
    (hG : ProjGenLinGroup.mk G = c.val σ)
    (f : restrictTestAlgebraObj k K R ⟶ restrictTestAlgebraObj k K S)
    (hf : ∀ a : K, f.hom (algebraMap K R a) = algebraMap K S (σ a))
    (x : (restrictTestAlgebraObj k K R ⊗[k] A)ˣ) :
    let g := projectiveMatrixPoint P (restrictTestAlgebraObj k K S)
      (Units.map (algebraMap K S).mapMatrix.toMonoidHom G)
    projectiveMatrixPoint P (restrictTestAlgebraObj k K S)
      (Units.map (d S).toMonoidHom (Units.map (changeCoefficients f.hom).toMonoidHom x)) =
      g * mapPoints f (projectiveMatrixPoint P (restrictTestAlgebraObj k K R)
        (Units.map (d R).toMonoidHom x)) * g⁻¹ := by
  dsimp only
  rw [projectiveMatrixPoint_natural]
  let g := Units.map (algebraMap K S).mapMatrix.toMonoidHom G
  let y := GeneralLinearGroup.map f.hom.toRingHom (Units.map (d R).toMonoidHom x)
  let m := projectiveMatrixHom P (restrictTestAlgebraObj k K S)
  have he : Units.map (d S).toMonoidHom (Units.map (changeCoefficients f.hom).toMonoidHom x) =
      g * y * g⁻¹ := by
    apply Units.ext
    have hg : g⁻¹ = Units.map (algebraMap K S).mapMatrix.toMonoidHom G⁻¹ :=
      (map_inv _ _).symm
    rw [hg]
    exact hd ρ c hρ hc σ G hG f hf x.val
  change m _ = m g * m y * (m g)⁻¹
  rw [he, map_mul, map_mul, map_inv]

private theorem rightQuotientMap_projection {k : Type u} [Field k] {G G' : GroupScheme k}
    {B : ClosedSubgroup G} {B' : ClosedSubgroup G'}
    (f : G ⟶ G') (s : B.group ⟶ B'.group) (hs : B.inclusion ≫ f = s ≫ B'.inclusion) :
    rightQuotientProjection B ≫ rightQuotientMap f s hs =
      (fppfOver k).uliftYoneda.map f.hom.hom ≫ rightQuotientProjection B' := by
  apply Sheaf.hom_ext
  ext T a
  exact rightQuotientMapOnLifts f s hs a.down

private def quotientIsoOfGroupIso {k : Type u} [Field k] {G G' : GroupScheme k}
    {B : ClosedSubgroup G} {B' : ClosedSubgroup G'}
    (f : G ≅ G') (s : B.group ≅ B'.group) (hs : B.inclusion ≫ f.hom = s.hom ≫ B'.inclusion) :
    rightQuotientSheaf B ≅ rightQuotientSheaf B' := by
  have hs' : B'.inclusion ≫ f.inv = s.inv ≫ B.inclusion := by
    rw [← cancel_mono f.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, hs]
    simp
  haveI : Sheaf.IsLocallySurjective (rightQuotientProjection B) := rightQuotientLocalLifts B
  haveI : Sheaf.IsLocallySurjective (rightQuotientProjection B') := rightQuotientLocalLifts B'
  let Y := (fppfOver k).uliftYoneda
  refine ⟨rightQuotientMap f.hom s.hom hs, rightQuotientMap f.inv s.inv hs', ?_, ?_⟩
  · apply (cancel_epi (rightQuotientProjection B)).mp
    rw [← Category.assoc, rightQuotientMap_projection, Category.assoc,
      rightQuotientMap_projection, ← Category.assoc, ← Y.map_comp]
    simp [← Grp.comp_hom_hom]
    exact Category.id_comp _
  · apply (cancel_epi (rightQuotientProjection B')).mp
    rw [← Category.assoc, rightQuotientMap_projection, Category.assoc,
      rightQuotientMap_projection, ← Category.assoc, ← Y.map_comp]
    simp [← Grp.comp_hom_hom]
    exact Category.id_comp _

private theorem epi_product_of_flat_surjective {k : Type u} [Field k]
    {X Y : SchemeOver k} (q : X ⟶ Y) [Flat q.left] [Surjective q.left] :
    Epi (prod.map q q) := by
  have e (T : SchemeOver k) : Epi (prod.map q (𝟙 T)) := by
    let F := Over.forget (Spec (CommRingCat.of k))
    have h := F.map_isPullback (IsPullback.of_prod_fst_with_id q T)
    haveI : Flat (prod.map q (𝟙 T)).left :=
      MorphismProperty.of_isPullback (P := @Flat) h (show Flat q.left from inferInstance)
    haveI : Surjective (prod.map q (𝟙 T)).left :=
      MorphismProperty.of_isPullback (P := @Surjective) h (show Surjective q.left from inferInstance)
    haveI := Flat.epi_of_flat_of_surjective (prod.map q (𝟙 T)).left
    exact Over.epi_of_epi_left _
  have he : prod.map (𝟙 Y) q =
      (prod.braiding Y X).hom ≫ prod.map q (𝟙 Y) ≫ (prod.braiding Y Y).hom := by
    ext <;> simp
  haveI : Epi (prod.map q (𝟙 X)) := e X
  haveI : Epi (prod.map q (𝟙 Y)) := e Y
  haveI : Epi (prod.map (𝟙 Y) q) := by rw [he]; infer_instance
  have hh : prod.map q q = prod.map q (𝟙 X) ≫ prod.map (𝟙 Y) q := by
    ext <;> simp
  rw [hh]
  infer_instance

section QuotientGroupIso

open scoped CategoryTheory.MonObj

private def groupIsoOfQuotientProjection {k : Type u} [Field k]
    {G H G' H' : GroupScheme k} (p : G ⟶ H) (q : G' ⟶ H') (f : G ≅ G')
    (e : H.X ≅ H'.X) (he : p.hom.hom ≫ e.hom = f.hom.hom.hom ≫ q.hom.hom)
    [Flat p.hom.hom.left] [Surjective p.hom.hom.left] : H ≅ H' := by
  let g := (f.hom ≫ q).hom.hom
  change p.hom.hom ≫ e.hom = g at he
  refine Grp.mkIso e ?_ ?_
  · calc
      η[H.X] ≫ e.hom = η[G.X] ≫ p.hom.hom ≫ e.hom := by rw [IsMonHom.one_hom_assoc]
      _ = η[H'.X] := by rw [he, IsMonHom.one_hom]
  · let c (X : SchemeOver k) : X ⊗ X ≅ X ⨯ X :=
      (tensorProductIsBinaryProduct X X).conePointUniqueUpToIso (limit.isLimit _)
    have hc₁ (X : SchemeOver k) : (c X).hom ≫ prod.fst = fst X X :=
      IsLimit.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct X X)
        (limit.isLimit (pair X X)) ⟨WalkingPair.left⟩
    have hc₂ (X : SchemeOver k) : (c X).hom ≫ prod.snd = snd X X :=
      IsLimit.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct X X)
        (limit.isLimit (pair X X)) ⟨WalkingPair.right⟩
    have hprod : (p.hom.hom ⊗ₘ p.hom.hom) =
        (c G.X).hom ≫ prod.map p.hom.hom p.hom.hom ≫ (c H.X).inv := by
      apply (cancel_mono (c H.X).hom).mp
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply prod.hom_ext
      · simp only [Category.assoc, hc₁, tensorHom_fst, prod.map_fst]
        rw [← Category.assoc, hc₁]
      · simp only [Category.assoc, hc₂, tensorHom_snd, prod.map_snd]
        rw [← Category.assoc, hc₂]
    haveI := epi_product_of_flat_surjective p.hom.hom
    haveI : Epi (p.hom.hom ⊗ₘ p.hom.hom) := by rw [hprod]; infer_instance
    apply (cancel_epi (p.hom.hom ⊗ₘ p.hom.hom)).mp
    rw [← IsMonHom.mul_hom_assoc, he, IsMonHom.mul_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom, he]

end QuotientGroupIso

private theorem affineLift {k : Type u} [Field k] {X Y : SchemeOver k}
    (hX : IsAffine X.left) (hY : IsAffine Y.left)
    (q : X ⟶ Y) [Flat q.left] [Surjective q.left] {R : TestAlgebra k} (p : Points Y R) :
    ∃ (S : TestAlgebra k) (a : R ⟶ S) (x : Points X S),
      Flat ((testSpec k).map a.op).left ∧ Surjective ((testSpec k).map a.op).left ∧
        x ≫ q = mapPoints a p := by
  let T := (testSpec k).obj (Opposite.op R)
  let W := pullback q p
  let F := Over.forget (Spec (CommRingCat.of k))
  have hp : IsPullback (pullback.fst q p).left (pullback.snd q p).left q.left p.left :=
    F.map_isPullback (IsPullback.of_hasPullback q p)
  letI : IsAffine X.left := hX
  letI : IsAffine Y.left := hY
  haveI : IsAffine T.left := by change IsAffine (Spec (CommRingCat.of R)); infer_instance
  haveI : IsAffine W.left := IsAffine.of_isPullback hp
  obtain ⟨S, ⟨i⟩⟩ := essImage_algSpec.mpr (show IsAffine W.left from inferInstance)
  let v : (testSpec k).obj S ⟶ T := i.hom ≫ pullback.snd q p
  let a := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage v).unop
  have ha : (testSpec k).map a.op = v :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage v
  haveI : Flat (pullback.snd q p).left :=
    MorphismProperty.of_isPullback (P := @Flat) hp inferInstance
  haveI : Surjective (pullback.snd q p).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hp inferInstance
  refine ⟨S.unop, a, i.hom ≫ pullback.fst q p, ?_, ?_, ?_⟩
  · rw [ha]
    change Flat (i.hom.left ≫ (pullback.snd q p).left)
    infer_instance
  · rw [ha]
    change Surjective (i.hom.left ≫ (pullback.snd q p).left)
    infer_instance
  · change (i.hom ≫ pullback.fst q p) ≫ q = (testSpec k).map a.op ≫ p
    rw [ha, Category.assoc, pullback.condition, ← Category.assoc]

private theorem mapPoints_comp {k : Type u} [Field k] {X : SchemeOver k}
    {R S T : TestAlgebra k} (a : R ⟶ S) (b : S ⟶ T) (p : Points X R) :
    mapPoints (a ≫ b) p = mapPoints b (mapPoints a p) := by
  change (testSpec k).map (b.op ≫ a.op) ≫ p = _
  rw [Functor.map_comp, Category.assoc]

open scoped CategoryTheory.MonObj in
private theorem projectiveCocycleOfLifts {k K : Type u} [Field k] [Field K] [Algebra k K]
    {U Q : GroupScheme k} (q : U ⟶ Q)
    (hU : IsAffine U.X.left) (hQ : IsAffine Q.X.left)
    [Flat ((groupBaseChange k K).map q).hom.hom.left]
    [Surjective ((groupBaseChange k K).map q).hom.hom.left]
    {n : ℕ} (P : MatrixAlgebraForms.ProjectivePresentation k n)
    (z : restrictedGroupPoints k K Q ≅ restrictedGroupPoints k K P.projectiveGroup.val)
    (σ : Gal(K/k)) (G : GL (Fin n) K)
    (hl : ∀ {R S : TestAlgebra K}
      (f : restrictTestAlgebraObj k K R ⟶ restrictTestAlgebraObj k K S),
      (∀ a : K, f.hom (algebraMap K R a) = algebraMap K S (σ a)) →
      ∀ p : Points U.X (restrictTestAlgebraObj k K R),
        let g := projectiveMatrixPoint P (restrictTestAlgebraObj k K S)
          (GeneralLinearGroup.map (algebraMap K S) G)
        z.hom.app S (mapPoints f (p ≫ q.hom.hom)) =
          g * mapPoints f (z.hom.app R (p ≫ q.hom.hom)) * g⁻¹)
    {R S : TestAlgebra K} (f : restrictTestAlgebraObj k K R ⟶ restrictTestAlgebraObj k K S)
    (hf : ∀ a : K, f.hom (algebraMap K R a) = algebraMap K S (σ a))
    (p : Points Q.X (restrictTestAlgebraObj k K R)) :
    let g := projectiveMatrixPoint P (restrictTestAlgebraObj k K S)
      (GeneralLinearGroup.map (algebraMap K S) G)
    z.hom.app S (mapPoints f p) = g * mapPoints f (z.hom.app R p) * g⁻¹ := by
  let β := restrictTestAlgebra k K
  let g (T : TestAlgebra K) := projectiveMatrixPoint P (β.obj T)
    (GeneralLinearGroup.map (algebraMap K T) G)
  have hg {T T' : TestAlgebra K} (a : T ⟶ T') : mapPoints (β.map a) (g T) = g T' := by
    dsimp only [g]
    rw [projectiveMatrixPoint_natural]
    have ha : a.hom.toRingHom.comp (algebraMap K T) = algebraMap K T' :=
      RingHom.ext a.hom.commutes
    change projectiveMatrixPoint P (β.obj T') (GeneralLinearGroup.map
      (a.hom.toRingHom.comp (algebraMap K T)) G) = _
    rw [ha]
  have hz {T T' : TestAlgebra K} (a : T ⟶ T') (v : Points Q.X (β.obj T)) :
      z.hom.app T' (mapPoints (β.map a) v) = mapPoints (β.map a) (z.hom.app T v) :=
    DFunLike.congr_fun (congrArg GrpCat.Hom.hom (z.hom.naturality a)) v
  have he {T T' : TestAlgebra K} (a : T ⟶ T') (v : Points P.projectiveGroup.val.X (β.obj T)) :
      mapPoints (β.map a) (g T * v * (g T)⁻¹) =
        g T' * mapPoints (β.map a) v * (g T')⁻¹ := by
    let m := ((groupPointsFunctor k).obj P.projectiveGroup.val).map (β.map a)
    change m.hom (g T * v * (g T)⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    change mapPoints (β.map a) (g T) * mapPoints (β.map a) v *
      (mapPoints (β.map a) (g T))⁻¹ = _
    rw [hg]
  let T := twistTestAlgebra σ R
  let idσ := twistIdentity σ R
  -- Changing the scalar structure preserves the affine covering map.
  have ht : z.hom.app T (mapPoints idσ p) =
      g T * mapPoints idσ (z.hom.app R p) * (g T)⁻¹ := by
    let qK := ((groupBaseChange k K).map q).hom.hom
    let pK := (baseChangePointsEquiv K Q.X R).symm p
    obtain ⟨V, a, x, ha, hsurj, hx⟩ := affineLift
      (affine_baseChange U.X hU) (affine_baseChange Q.X hQ) qK pK
    let x₀ := baseChangePoint k K U.X V x
    have hx₀ : x₀ ≫ q.hom.hom = mapPoints (β.map a) p := by
      have h := congrArg (baseChangePoint k K Q.X V) hx
      change baseChangePoint k K Q.X V
        (x ≫ (baseChange k K).map q.hom.hom) = baseChangePoint k K Q.X V (mapPoints a pK) at h
      rw [baseChangePointsSchemeNaturality k K q.hom.hom,
        baseChangePointsNaturality k K Q.X] at h
      exact h.trans (congrArg (mapPoints (β.map a)) ((baseChangePointsEquiv K Q.X R).apply_symm_apply p))
    let b := twistMap σ a
    let specMap := (testSpec k).map (β.map b).op
    have hspec : specMap.left = ((testSpec K).map a.op).left := rfl
    haveI : Flat specMap.left := hspec ▸ ha
    haveI : Surjective specMap.left := hspec ▸ hsurj
    haveI := Flat.epi_of_flat_of_surjective specMap.left
    haveI : Epi specMap := Over.epi_of_epi_left specMap
    apply (cancel_epi specMap).mp
    change mapPoints (β.map b) (z.hom.app T (mapPoints idσ p)) =
      mapPoints (β.map b) (g T * mapPoints idσ (z.hom.app R p) * (g T)⁻¹)
    rw [← hz, he, ← mapPoints_comp, ← mapPoints_comp, ← twistIdentity_comm σ a,
      mapPoints_comp, mapPoints_comp, ← hz, ← hx₀]
    exact hl (twistIdentity σ V) (fun a => (congrArg (algebraMap K V) (σ.symm_apply_apply a)).symm) x₀
  let a : T ⟶ S := testAlgebraHom (R := T) (S := S) f.hom.toRingHom (fun x =>
    (hf (σ.symm x)).trans (congrArg (algebraMap K S) (σ.apply_symm_apply x)))
  have hf' : f = idσ ≫ β.map a := by ext x; rfl
  change z.hom.app S (mapPoints f p) = g S * mapPoints f (z.hom.app R p) * (g S)⁻¹
  rw [hf', mapPoints_comp, mapPoints_comp, hz, ht, he]

theorem projectiveSplitting : ProjectiveSplitting.{u} := by
  intro k K _ _ _ A _ _ ι _ hA b s
  let n := degree k A
  let I := ULift.{u} (Fin n)
  obtain ⟨J, HM, F, point, e, m, i, hi, hpoint, hcoords, hs, hn, Q, q, hker, eq, heq⟩ :=
    projectiveModel (k := k) hA b
  letI := J.hopf
  letI := HM.hopf
  let U := Specs.StandardGroups.spectrum k (UnitCoordinates hA b)
  let M := Specs.StandardGroups.spectrum k (LaurentPolynomial k)
  let B : ClosedSubgroup U.val := ⟨M.val, i, hi⟩
  letI : Nonempty I := ⟨⟨⟨0, degree_pos hA⟩⟩⟩
  obtain ⟨hm, hl, em, el, sc, hsc, hscalar, _, P₀, PGL, q₀, e₀, _, hker₀, hq₀⟩ :=
    projectiveLinearQuotient k I
  letI := hl.hopf
  letI := hm.hopf
  let linear := Specs.StandardGroups.spectrum k (GLCoordinates k I)
  let GM := Specs.StandardGroups.spectrum k (LaurentPolynomial k)
  let P : MatrixAlgebraForms.ProjectivePresentation k n :=
    ⟨linear.val, ⟨GM.val, sc, hsc⟩, el, em, hscalar, PGL, q₀, hker₀, P₀, e₀, hq₀⟩
  obtain ⟨⟨T⟩, _⟩ := homogeneousQuotient k U B
  let j₁ := compareRepresentatives T eq
  have hj₁ : T.projection ≫ j₁.hom = q.hom.hom :=
    compareRepresentatives_projection T q.hom.hom eq heq
  obtain ⟨hiK, eqK, heqK⟩ := quotientBaseChange k K T
  let C := groupBaseChange k K
  let V := C.obj U.val
  let N := C.obj M.val
  let iK := C.map i
  let B' : ClosedSubgroup V := ⟨N, iK, hiK⟩
  obtain ⟨hiP, eqP₀, heP₀⟩ := quotientBaseChange k K P.presentation
  let S : ClosedSubgroup (C.obj P.linearGroup) :=
    ⟨C.obj P.scalarGroup.group, C.map P.scalarGroup.inclusion, hiP⟩
  let D := baseChange k K
  let Y := (fppfOver K).uliftYoneda
  let eqV : rightQuotientSheaf B' ≅ schemeFppfSheaf (C.obj Q.val).X :=
    eqK ≪≫ Y.mapIso (D.mapIso j₁)
  have heV : rightQuotientProjection B' ≫ eqV.hom = Y.map (C.map q).hom.hom := by
    change rightQuotientProjection B' ≫ (eqK.hom ≫ Y.map (D.map j₁.hom)) = _
    rw [← Category.assoc, heqK, ← Y.map_comp, ← D.map_comp, hj₁]
    rfl
  let eqP : rightQuotientSheaf S ≅ schemeFppfSheaf (C.obj P.projectiveGroup.val).X :=
    eqP₀ ≪≫ Y.mapIso (D.mapIso P.comparison)
  have heP : rightQuotientProjection S ≫ eqP.hom = Y.map (C.map P.projection).hom.hom := by
    change rightQuotientProjection S ≫ (eqP₀.hom ≫ Y.map (D.map P.comparison.hom)) = _
    rw [← Category.assoc, heP₀, ← Y.map_comp, ← D.map_comp, P.projectionFormula]
    rfl
  let W := (Functor.whiskeringLeft (TestAlgebra K) (TestAlgebra k) GrpCat.{u}).obj
    (restrictTestAlgebra k K)
  let t := baseChangePointIso (K := K) U.val ≪≫ W.mapIso (e ≪≫ unitPointIso F point @hpoint) ≪≫
    splitUnitPoints s ≪≫ (restrictLinearPoints I).symm ≪≫ W.mapIso P.linearPoints.symm ≪≫
    (baseChangePointIso (K := K) P.linearGroup).symm
  let a := baseChangePointIso (K := K) M.val ≪≫ W.mapIso m ≪≫
    restrictScalarPoints ≪≫ W.mapIso P.scalarPoints.symm ≪≫
    (baseChangePointIso (K := K) P.scalarGroup.group).symm
  have hL : IsAffine (C.obj P.linearGroup).X.left :=
    affine_baseChange P.linearGroup.X linear.property.1
  have hM : IsAffine S.group.X.left := affine_baseChange P.scalarGroup.group.X GM.property.1
  let l := affineGroupIso (affine_baseChange U.val.X U.property.1) hL t
  let r := affineGroupIso (affine_baseChange M.val.X M.property.1) hM a
  have hlt : (groupPointsFunctor K).map l.hom = t.hom := affineGroupIso_hom _ _ _
  have hra : (groupPointsFunctor K).map r.hom = a.hom := affineGroupIso_hom _ _ _
  have ht (R : TestAlgebra K) (p : Points V.X R) :
      baseChangePoint k K P.linearGroup.X R (p ≫ l.hom.hom.hom) =
        P.linearPoints.inv.app (restrictTestAlgebraObj k K R)
          (MatrixAlgebraForms.liftMatrix (Units.map
            (extendSplitting (R := restrictTestAlgebraObj k K R) s).toMonoidHom
              (point _ (e.hom.app _ (baseChangePoint k K U.val.X R p))))) := by
    have h := DFunLike.congr_fun (congrArg (fun z => (z.app R).hom) hlt) p
    change p ≫ l.hom.hom.hom = (baseChangePointsEquiv K P.linearGroup.X R).symm _ at h
    rw [h]
    exact (baseChangePointsEquiv K P.linearGroup.X R).apply_symm_apply _
  have ha (R : TestAlgebra K) (p : Points N.X R) :
      baseChangePoint k K P.scalarGroup.group.X R (p ≫ r.hom.hom.hom) =
        P.scalarPoints.inv.app (restrictTestAlgebraObj k K R)
          (m.hom.app _ (baseChangePoint k K M.val.X R p)) := by
    have h := DFunLike.congr_fun (congrArg (fun z => (z.app R).hom) hra) p
    change p ≫ r.hom.hom.hom = (baseChangePointsEquiv K P.scalarGroup.group.X R).symm _ at h
    rw [h]
    exact (baseChangePointsEquiv K P.scalarGroup.group.X R).apply_symm_apply _
  have comm : B'.inclusion ≫ l.hom = r.hom ≫ S.inclusion := by
    apply (groupHomComparison K N (C.obj P.linearGroup) (affine_baseChange M.val.X M.property.1)).1
    change (groupPointsFunctor K).map (iK ≫ l.hom) =
      (groupPointsFunctor K).map (r.hom ≫ C.map P.scalarGroup.inclusion)
    ext : 1
    funext R
    apply GrpCat.ext
    intro p
    apply (baseChangePointsEquiv K P.linearGroup.X R).injective
    apply (ConcreteCategory.bijective_of_isIso
      (P.linearPoints.hom.app (restrictTestAlgebraObj k K R))).1
    change P.linearPoints.hom.app _ (baseChangePoint k K P.linearGroup.X R
      (p ≫ (iK ≫ l.hom).hom.hom)) =
      P.linearPoints.hom.app _ (baseChangePoint k K P.linearGroup.X R
        (p ≫ (r.hom ≫ C.map P.scalarGroup.inclusion).hom.hom))
    rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc, ht,
      baseChangeGroupPointNaturality P.scalarGroup.inclusion, ha, P.scalarFormula]
    let v : Points M.val.X (restrictTestAlgebraObj k K R) := baseChangePoint k K M.val.X R p
    let d := extendSplitting (R := restrictTestAlgebraObj k K R) s
    rw [← GrpCat.comp_apply, P.linearPoints.inv_hom_id_app,
      ← GrpCat.comp_apply, P.scalarPoints.inv_hom_id_app]
    change MatrixAlgebraForms.liftMatrix (Units.map d.toMonoidHom
        (point _ (e.hom.app _ (baseChangePoint k K U.val.X R (p ≫ iK.hom.hom))))) =
      Matrix.GeneralLinearGroup.scalar I (m.hom.app _ v)
    rw [baseChangeGroupPointNaturality i, hs]
    apply Units.ext
    ext x y
    let a : (restrictTestAlgebraObj k K R)ˣ := m.hom.app _ v
    have h := d.commutes a.val
    change d (a.val ⊗ₜ[k] (1 : A)) = _ at h
    change d (a.val ⊗ₜ[k] (1 : A)) x.down y.down = (GeneralLinearGroup.scalar I a).val x y
    refine (congrArg (fun X : Matrix (Fin n) (Fin n) R => X x.down y.down) h).trans ?_
    rw [Matrix.algebraMap_matrix_apply]
    change (if x.down = y.down then a.val else 0) = Matrix.diagonal (fun _ : I => a.val) x y
    have hxy : x.down = y.down ↔ x = y := ⟨ULift.ext, congrArg ULift.down⟩
    rw [Matrix.diagonal_apply]
    exact ite_cond_congr (propext hxy)
  let α := quotientIsoOfGroupIso (B := B') (B' := S) l r comm
  let τ := eqV.symm ≪≫ α ≪≫ eqP
  let β := (fppfOver K).fullyFaithfulUliftYoneda.preimageIso τ
  have hβ : (C.map q).hom.hom ≫ β.hom = l.hom.hom.hom ≫ (C.map P.projection).hom.hom := by
    apply Y.map_injective
    have he : Y.map β.hom = τ.hom := by
      change Y.map ((fppfOver K).fullyFaithfulUliftYoneda.preimageIso τ).hom = τ.hom
      rw [Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
    rw [Y.map_comp, Y.map_comp, ← heV, ← heP, he]
    simp only [τ, Iso.trans_hom, Category.assoc, Iso.symm_hom, Iso.hom_inv_id_assoc]
    change rightQuotientProjection B' ≫ rightQuotientMap l.hom r.hom comm ≫ eqP.hom = _
    rw [← Category.assoc, rightQuotientMap_projection, Category.assoc]
  have hp₀ := baseChangeMapIsPullback K T.projection
  haveI : Flat (D.map T.projection).left :=
    MorphismProperty.of_isPullback (P := @Flat) hp₀.flip T.flat
  haveI : Surjective (D.map T.projection).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hp₀.flip T.surjective
  have hp : (C.map q).hom.hom.left = (D.map T.projection).left ≫ (D.map j₁.hom).left := by
    rw [← Over.comp_left, ← D.map_comp, hj₁]
    rfl
  haveI : Flat (C.map q).hom.hom.left := hp ▸ inferInstance
  haveI : Surjective (C.map q).hom.hom.left := hp ▸ inferInstance
  let j := groupIsoOfQuotientProjection (C.map q) (C.map P.projection) l β hβ
  let z := (baseChangePointIso (K := K) Q.val).symm ≪≫ (groupPointsFunctor K).mapIso j ≪≫
    baseChangePointIso (K := K) P.projectiveGroup.val
  let d (R : TestAlgebra K) := extendSplitting (R := restrictTestAlgebraObj k K R) s
  have hd (R : TestAlgebra K) (r : R) (a : A) :=
    extendSplitting_tmul (R := restrictTestAlgebraObj k K R) s r a
  have hz (R : TestAlgebra K) (p : Points (C.obj Q.val).X R) :
      z.hom.app R (baseChangePoint k K Q.val.X R p) =
        baseChangePoint k K P.projectiveGroup.val.X R (p ≫ j.hom.hom.hom) := by
    change baseChangePoint k K P.projectiveGroup.val.X R
      ((baseChangePointsEquiv K Q.val.X R).symm (baseChangePoint k K Q.val.X R p) ≫ j.hom.hom.hom) = _
    exact congrArg (fun x : Points (C.obj Q.val).X R =>
      baseChangePoint k K P.projectiveGroup.val.X R (x ≫ j.hom.hom.hom))
      ((baseChangePointsEquiv K Q.val.X R).symm_apply_apply p)
  have hproj (R : TestAlgebra K) (p : Points U.val.X (restrictTestAlgebraObj k K R)) :
      z.hom.app R (p ≫ q.hom.hom) =
        projectiveMatrixPoint P (restrictTestAlgebraObj k K R)
          (Units.map (d R).toMonoidHom (point _ (e.hom.app _ p))) := by
    let x : Points (C.obj U.val).X R := (baseChangePointsEquiv K U.val.X R).symm p
    have hx : baseChangePoint k K U.val.X R x = p :=
      (baseChangePointsEquiv K U.val.X R).apply_symm_apply p
    rw [← hx, ← baseChangeGroupPointNaturality q, hz]
    change baseChangePoint k K P.projectiveGroup.val.X R
      ((x ≫ (C.map q).hom.hom) ≫ β.hom) = _
    rw [Category.assoc, hβ, ← Category.assoc,
      baseChangeGroupPointNaturality P.projection, ht]
    rfl
  refine ⟨J, M.val, F, point, e, m, i, hi, Q, q, P, j, z, d, @hpoint, hcoords, hs, ⟨hker, eq, heq⟩,
    hd, hz, hproj, (by
      intro _ _
      exact MatrixAlgebraForms.classificationOnPresentation (degree_pos hA) P), ?_⟩
  intro _ _ ρ c hρ hc R S σ G hG f hf p
  apply projectiveCocycleOfLifts q U.property.1 Q.property.1 P z σ G _ f hf p
  intro R' S' a ha x
  have hp : mapPoints a (x ≫ q.hom.hom) = mapPoints a x ≫ q.hom.hom :=
    (Category.assoc _ _ _).symm
  rw [hp, hproj, hproj]
  have he := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.hom.naturality a)) x
  change e.hom.app _ (mapPoints a x) = F.map a (e.hom.app _ x) at he
  rw [he, hpoint]
  exact projectiveCocycleOnLift (cocycleOnTestAlgebras s d hd) ρ c hρ hc P σ G hG a ha
    (point _ (e.hom.app _ x))

end Projective

theorem innerClassification : InnerClassification.{u,w} :=
  MatrixAlgebraForms.classification

section OppositeAlgebra

open MulOpposite

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

private def oppositeTensor (R : Type u) [CommRing R] [Algebra k R] :
    (R ⊗[k] A)ᵐᵒᵖ ≃ₐ[R] R ⊗[k] Aᵐᵒᵖ :=
  (Algebra.TensorProduct.opAlgEquiv k R R A).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.toOpposite R R).symm (AlgEquiv.refl : Aᵐᵒᵖ ≃ₐ[k] Aᵐᵒᵖ))

private theorem oppositeTensor_tmul {R : Type u} [CommRing R] [Algebra k R]
    (r : R) (a : A) : oppositeTensor R (op (r ⊗ₜ[k] a)) = r ⊗ₜ[k] op a := rfl

private theorem oppositeTensor_linear {R : Type u} [CommRing R] [Algebra k R]
    (x : R ⊗[k] A) :
    oppositeTensor R (op x) =
      TensorProduct.map (LinearMap.id : R →ₗ[k] R)
        (opLinearEquiv k : A ≃ₗ[k] Aᵐᵒᵖ).toLinearMap x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy =>
    change oppositeTensor R (op x + op y) = _
    simp only [map_add, hx, hy]

private theorem oppositeTensor_natural {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) (x : R ⊗[k] A) :
    oppositeTensor S (op (changeCoefficients f x)) =
      changeCoefficients f (oppositeTensor R (op x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy =>
    rw [map_add]
    change oppositeTensor S (op (changeCoefficients f x) + op (changeCoefficients f y)) =
      changeCoefficients f (oppositeTensor R (op x + op y))
    simp only [map_add, hx, hy]

private theorem centralSimple_opposite (hA : IsCentralSimple k A) : IsCentralSimple k Aᵐᵒᵖ := by
  let : IsSimpleRing A := hA.1
  let : Algebra.IsCentral k A := hA.2.1
  let : FiniteDimensional k A := hA.2.2
  exact ⟨inferInstance, inferInstance, (opLinearEquiv k (M := A)).finiteDimensional⟩

private theorem opposite_degree : degree k Aᵐᵒᵖ = degree k A := by
  unfold degree
  rw [← (opLinearEquiv k (M := A)).finrank_eq]

private def oppositeSplitting {K : Type u} [Field K] [Algebra k K] {n : ℕ}
    (s : (K ⊗[k] A) ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    (K ⊗[k] Aᵐᵒᵖ) ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
  (oppositeTensor K).symm.trans ((AlgEquiv.op s).trans (Matrix.transposeAlgEquiv _ _ _).symm)

private def inverseTransposeUnit {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (g : GL I R) : GL I R where
  val := (↑g⁻¹ : Matrix I I R).transpose
  inv := g.val.transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

open _root_.RM03.Brauer.ProjectiveClassification in
theorem oppositeTwisting : OppositeTwisting.{u} := by
  intro k K A _ _ _ _ _ _ _ n hA s ρ c hρ hc
  let t := oppositeSplitting s
  have htr (z : K ⊗[k] A) : t (oppositeTensor K (op z)) = (s z).transpose := by
    dsimp only [t, oppositeSplitting, AlgEquiv.trans_apply]
    rw [AlgEquiv.symm_apply_apply]
    rfl
  have ht (r : K) (a : A) : t (r ⊗ₜ[k] op a) = (s (r ⊗ₜ[k] a)).transpose :=
    htr (r ⊗ₜ[k] a)
  have hn : 0 < n := (degree_eq_matrix_size hA s) ▸ degree_pos hA
  obtain ⟨τ, hτ, d, hd⟩ := transported_cocycle hn t
  obtain ⟨e, he, _⟩ := MatrixAlgebraForms.conjugationIdentification (k := k) (K := K) hn
  refine ⟨t, ht, τ, d, hτ, hd, ?_, ?_⟩
  · intro σ G hG
    let H := inverseTransposeUnit G
    refine ⟨H, rfl, ?_⟩
    obtain ⟨D, hD⟩ := ProjGenLinGroup.mk_surjective (d.val σ)
    rw [← hD]
    apply e.injective
    ext m : 1
    let x := m.map σ.symm
    have hx : x.map σ = m := by
      ext i j
      exact σ.apply_symm_apply (m i j)
    obtain ⟨z, hz⟩ := s.surjective x.transpose
    have htz : t (oppositeTensor K (op z)) = x := by rw [htr, hz, Matrix.transpose_transpose]
    have h (z : K ⊗[k] A) :
        τ.act σ (t (oppositeTensor K (op z))) = (ρ.act σ (s z)).transpose := by
      induction z using TensorProduct.inductionOn with
      | tmul r a => rw [oppositeTensor_tmul, hτ, hρ, ht]
      | add x y hx hy =>
        change τ.act σ (t (oppositeTensor K (op x + op y))) = _
        simp only [map_add, Matrix.transpose_add, hx, hy]
    have h' := h z
    rw [htz, hc σ G hG, hz, Matrix.transpose_mul, Matrix.transpose_mul] at h'
    change τ.act σ x = H.val * (x.map σ * (H⁻¹).val) at h'
    rw [hx, ← mul_assoc] at h'
    rw [he, he, ← h', hd σ D hD, hx]
  · let hO := centralSimple_opposite hA
    let X : Form k K n := ⟨toCSA hA, ⟨s⟩⟩
    let Y : Form k K n := ⟨toCSA hO, ⟨t⟩⟩
    obtain ⟨α, hα, _⟩ := _root_.RM03.Brauer.ProjectiveClassification.classification.{u,u,u} hn (k := k) (K := K)
    change (Quot.mk (Cohomologous k K n) c : H1 k K n) = Quot.mk (Cohomologous k K n) d ↔ _
    rw [← hα X s ρ c hρ hc, ← hα Y t τ d hτ hd, α.apply_eq_iff_eq]
    exact splitClasses_eq_iff X Y

private theorem normAt_opposite {ι κ R : Type u} [Fintype ι] [Fintype κ] [CommRing R]
    [Algebra k R] (hA : IsCentralSimple k A) (hO : IsCentralSimple k Aᵐᵒᵖ)
    (b : Module.Basis ι k A) (c : Module.Basis κ k Aᵐᵒᵖ) (x : R ⊗[k] A) :
    normAt hO c (oppositeTensor R (op x)) = normAt hA b x := by
  let K := AlgebraicClosure k
  obtain ⟨s⟩ := algEquiv_matrix_algebraicClosure hA
  let t := oppositeSplitting s
  have hn : degree k Aᵐᵒᵖ = degree k A := opposite_degree
  let e := t.trans (Matrix.reindexAlgEquiv K K (finCongr hn.symm))
  let T := K ⊗[k] R
  let f : R →ₐ[k] T := includeRight
  have hf : Function.Injective f :=
    includeRight_injective (algebraMap k K).injective
  apply hf
  rw [← normAt_natural hO c f, ← normAt_natural hA b f, ← oppositeTensor_natural,
    normAt_eq_det hO c e, normAt_eq_det hA b s]
  generalize changeCoefficients f x = z
  have hm : extendSplitting e (oppositeTensor T (op z)) =
      Matrix.reindex (finCongr hn.symm) (finCongr hn.symm) (extendSplitting s z).transpose := by
    induction z using TensorProduct.inductionOn with
    | tmul r a =>
      rw [oppositeTensor_tmul, extendSplitting_tmul, extendSplitting_tmul]
      rfl
    | add z w hz hw =>
      change extendSplitting e (oppositeTensor T (op z + op w)) = _
      rw [map_add, map_add, hz, hw, map_add, Matrix.transpose_add]
      rfl
  rw [hm, Matrix.det_reindex_self, Matrix.det_transpose]

private def normOneOppositeEquiv {ι κ R : Type u} [Fintype ι] [Fintype κ] [CommRing R]
    [Algebra k R] (hA : IsCentralSimple k A) (hO : IsCentralSimple k Aᵐᵒᵖ)
    (b : Module.Basis ι k A) (c : Module.Basis κ k Aᵐᵒᵖ) :
    (normOne (R := R) hA b)ᵐᵒᵖ ≃* normOne (R := R) hO c where
  toFun x := ⟨oppositeTensor R (op x.unop.val),
    (normAt_opposite hA hO b c _).trans x.unop.prop⟩
  invFun y := op ⟨(oppositeTensor R).symm y.val |>.unop, by
    rw [← normAt_opposite hA hO b c, op_unop, AlgEquiv.apply_symm_apply]
    exact y.prop⟩
  left_inv x := by
    apply unop_injective
    apply Subtype.ext
    change ((oppositeTensor R).symm (oppositeTensor R (op x.unop.val))).unop = x.unop.val
    rw [AlgEquiv.symm_apply_apply, unop_op]
  right_inv x := by
    apply Subtype.ext
    change oppositeTensor R (op ((oppositeTensor R).symm x.val).unop) = x.val
    rw [op_unop, AlgEquiv.apply_symm_apply]
  map_mul' x y := by
    apply Subtype.ext
    exact (oppositeTensor R).map_mul (op x.unop.val) (op y.unop.val)

private def inversionOpposite (M : Type*) [Group M] : M ≃* Mᵐᵒᵖ where
  toFun x := op x⁻¹
  invFun x := x.unop⁻¹
  left_inv x := inv_inv x
  right_inv x := by simp
  map_mul' x y := congrArg op (_root_.mul_inv_rev x y)

private def oppositeNormOnePoints {ι κ : Type u} [Fintype ι] [Fintype κ]
    (hA : IsCentralSimple k A) (hO : IsCentralSimple k Aᵐᵒᵖ)
    (b : Module.Basis ι k A) (c : Module.Basis κ k Aᵐᵒᵖ) :
    normOneFunctor hA b ≅ normOneFunctor hO c :=
  NatIso.ofComponents (fun R =>
    ((inversionOpposite _).trans (normOneOppositeEquiv (R := R) hA hO b c)).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro x
    simp only [GrpCat.comp_apply]
    apply Subtype.ext
    change oppositeTensor S (op (((mapNormOne hA b f.hom) x)⁻¹).val) =
      changeCoefficients f.hom (oppositeTensor R (op (x⁻¹).val))
    rw [← map_inv]
    exact oppositeTensor_natural f.hom (x⁻¹).val)

theorem oppositeNormOne : OppositeNormOne.{u} := by
  intro k A ι κ _ _ _ _ _ hA b c
  let hO := centralSimple_opposite hA
  let P := normOneRepresentation hA b
  let T := normOneRepresentation hO c
  letI := Representation.hopf P
  letI := Representation.hopf T
  let G := Specs.StandardGroups.spectrum k (NormOneCoordinates hA b)
  let L := Specs.StandardGroups.spectrum k (NormOneCoordinates hO c)
  let e := spectrumPointsIso (Representation.convolutionIso P)
  let z := spectrumPointsIso (Representation.convolutionIso T)
  let θ := oppositeNormOnePoints hA hO b c
  let j := affineGroupIso G.property.1 L.property.1 (e ≪≫ θ ≪≫ z.symm)
  refine ⟨hO, Representation.operations P, Representation.operations T, j, ?_⟩
  intro R f g p hp hg
  let eG := hopfSpecPointIso (CommHopfAlgCat.of k (NormOneCoordinates hA b))
  let eL := hopfSpecPointIso (CommHopfAlgCat.of k (NormOneCoordinates hO c))
  have hf' : p = eG.hom.app R (toConv f) := Over.OverMorphism.ext hp
  have hg' : p ≫ j.hom.hom.hom = eL.hom.app R (toConv g) := Over.OverMorphism.ext hg
  have hj := congrArg (fun q => q.app R p) (affineGroupIso_hom G.property.1 L.property.1
    (e ≪≫ θ ≪≫ z.symm))
  change p ≫ j.hom.hom.hom = z.inv.app R (θ.hom.app R (e.hom.app R p)) at hj
  rw [hg', hf', representedEvaluation P R f] at hj
  have hj' := congrArg (fun v => z.hom.app R v) hj
  rw [representedEvaluation T R g, ← GrpCat.comp_apply, z.inv_hom_id_app] at hj'
  let x := normOneEvaluate hA b R f
  let u := (isUnit_of_normAt_eq_one hA b x.val x.prop).unit
  refine ⟨u, IsUnit.unit_spec _, ?_⟩
  change (normOneEvaluate hO c R g).val =
    TensorProduct.map _ _ (↑u⁻¹ : R ⊗[k] A)
  change normOneEvaluate hO c R g = θ.hom.app R x at hj'
  rw [hj']
  exact oppositeTensor_linear _

end OppositeAlgebra

section DistinctInnerClasses

set_option backward.isDefEq.respectTransparency true

private def rationalFunctionAction {F L : Type u} [Field F] [Field L] [Algebra F L] :
    Gal(L/F) →* (RatFunc L ≃+* RatFunc L) :=
  (IsFractionRing.ringEquivOfRingEquivHom (Polynomial L) (RatFunc L)).comp
    { toFun := fun σ => (Polynomial.mapAlgEquiv σ).toRingEquiv
      map_one' := by ext p; simp [Polynomial.mapAlgEquiv]
      map_mul' := fun σ τ => by
        ext p
        simp [Polynomial.mapAlgEquiv] }

private theorem rationalFunctionAction_polynomial {F L : Type u} [Field F] [Field L]
    [Algebra F L] (σ : Gal(L/F)) (p : Polynomial L) :
    rationalFunctionAction σ (algebraMap (Polynomial L) (RatFunc L) p) =
      algebraMap (Polynomial L) (RatFunc L) (p.map σ.toRingHom) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ p

private theorem rationalFunctionAction_X {F L : Type u} [Field F] [Field L] [Algebra F L]
    (σ : Gal(L/F)) : rationalFunctionAction σ (RatFunc.X : RatFunc L) = RatFunc.X := by
  change rationalFunctionAction σ (algebraMap (Polynomial L) (RatFunc L) Polynomial.X) = _
  rw [rationalFunctionAction_polynomial, Polynomial.map_X]
  rfl

private theorem rationalFunctionAction_intDegree {F L : Type u} [Field F] [Field L]
    [Algebra F L] (σ : Gal(L/F)) (x : RatFunc L) :
    (rationalFunctionAction σ x).intDegree = x.intDegree := by
  by_cases hx : x = 0
  · simp [hx]
  let j := algebraMap (Polynomial L) (RatFunc L)
  have hj := IsFractionRing.injective (Polynomial L) (RatFunc L)
  have hd (p q : Polynomial L) (hp : p ≠ 0) (hq : q ≠ 0) :
      (j p / j q).intDegree = (p.natDegree : ℤ) - q.natDegree := by
    have hp' : j p ≠ 0 := (map_ne_zero_iff j hj).2 hp
    have hq' : j q ≠ 0 := (map_ne_zero_iff j hj).2 hq
    rw [RatFunc.intDegree_div hp' hq', RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  have hm (p : Polynomial L) (hp : p ≠ 0) : p.map σ.toRingHom ≠ 0 := by
    simpa only [Polynomial.map_zero] using (Polynomial.map_injective σ.toRingHom σ.injective).ne hp
  calc
    _ = (rationalFunctionAction σ (j x.num / j x.denom)).intDegree :=
      congrArg (fun y => (rationalFunctionAction σ y).intDegree) (RatFunc.num_div_denom x).symm
    _ = ((j (x.num.map σ.toRingHom)) / j (x.denom.map σ.toRingHom)).intDegree := by
      dsimp only [j]
      rw [map_div₀, rationalFunctionAction_polynomial, rationalFunctionAction_polynomial]
    _ = (j x.num / j x.denom).intDegree := by
      rw [hd _ _ (hm _ (x.num_ne_zero hx)) (hm _ x.denom_ne_zero),
        hd _ _ (x.num_ne_zero hx) x.denom_ne_zero,
        Polynomial.natDegree_map_eq_of_injective σ.injective,
        Polynomial.natDegree_map_eq_of_injective σ.injective]
    _ = _ := congrArg RatFunc.intDegree (RatFunc.num_div_denom x)

private theorem rationalFunctionAction_injective {F L : Type u} [Field F] [Field L]
    [Algebra F L] : Function.Injective (rationalFunctionAction (F := F) (L := L)) := by
  intro σ τ h
  ext x
  have he := DFunLike.congr_fun h (algebraMap (Polynomial L) (RatFunc L) (Polynomial.C x))
  rw [rationalFunctionAction_polynomial, rationalFunctionAction_polynomial,
    Polynomial.map_C, Polynomial.map_C] at he
  exact Polynomial.C_injective ((IsFractionRing.injective _ _ ) he)

private def cyclicPowers {G : Type*} [Group G] (g : G) (hg : g ^ 3 = 1) :
    Multiplicative (ZMod 3) →* G where
  toFun i := g ^ i.toAdd.val
  map_one' := by
    change g ^ 0 = 1
    exact pow_zero _
  map_mul' i j := by
    change g ^ (i.toAdd + j.toAdd).val = _
    rw [ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div (i.toAdd.val + j.toAdd.val) 3, pow_add, pow_mul, hg,
      one_pow, mul_one]

private def rotationMatrix {L : Type u} [Field L] : Matrix (Fin 3) (Fin 3) (RatFunc L) :=
  !![0, 0, RatFunc.X; 1, 0, 0; 0, 1, 0]

private theorem rotationMatrix_det {L : Type u} [Field L] :
    (rotationMatrix (L := L)).det = RatFunc.X := by
  simp [rotationMatrix, Matrix.det_fin_three]

private def rotationUnit (L : Type u) [Field L] : GL (Fin 3) (RatFunc L) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero rotationMatrix (by rw [rotationMatrix_det]; exact RatFunc.X_ne_zero)

private theorem rotationUnit_cube (L : Type u) [Field L] :
    rotationUnit L ^ 3 = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 RatFunc.X RatFunc.X_ne_zero) := by
  apply Units.ext
  change rotationMatrix ^ 3 = Matrix.diagonal (fun _ => (RatFunc.X : RatFunc L))
  rw [pow_succ, pow_succ, pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal]

open _root_.RM03.Brauer.ProjectiveClassification

/-- The coefficient action fixes the companion matrix. Its projective
class has cube one and defines a cocycle. -/
private theorem cubicCocycle {F L : Type} [Field F] [Fintype F] [Field L] [Finite L]
    [Algebra F L] [FiniteDimensional F L] (hn : Module.finrank F L = 3) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra k (RatFunc L))
      (_ : FiniteDimensional k (RatFunc L)) (_ : IsGalois k (RatFunc L)),
      ∃ (σ : Gal(RatFunc L/k)) (c : Cocycle k (RatFunc L) 3),
        (∀ x : RatFunc L, (σ x).intDegree = x.intDegree) ∧
        c.val σ = ProjGenLinGroup.mk (rotationUnit L) := by
  let K := RatFunc L
  let G := Gal(L/F)
  letI : MulSemiringAction G K := MulSemiringAction.compHom K rationalFunctionAction
  haveI : FaithfulSMul G K :=
    ⟨fun h => rationalFunctionAction_injective (RingEquiv.ext h)⟩
  let k := FixedPoints.subfield G K
  let e := FixedPoints.toAlgAutMulEquiv G K
  haveI : FiniteDimensional k K := inferInstance
  haveI : IsGalois k K := (inferInstance : IsGaloisGroup G k K).isGalois
  let γ := FiniteField.frobeniusAlgEquivOfAlgebraic F L
  have ho : orderOf γ = 3 :=
    (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F L).trans hn
  have hγ : γ ^ 3 = 1 := by simpa only [ho] using pow_orderOf_eq_one γ
  have hpow : Function.Bijective (cyclicPowers γ hγ) := by
    have h := FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F L
    rw [hn] at h
    exact h
  let w := (MulEquiv.ofBijective (cyclicPowers γ hγ) hpow).trans e
  let p := ProjGenLinGroup.mk (rotationUnit L)
  have hp : p ^ 3 = 1 := by
    rw [← map_pow, rotationUnit_cube, ProjGenLinGroup.mk_scalar]
  let m := (cyclicPowers p hp).comp w.symm.toMonoidHom
  have hX (σ : Gal(K/k)) : σ (RatFunc.X : K) = RatFunc.X := by
    obtain ⟨τ, rfl⟩ := e.surjective σ
    exact rationalFunctionAction_X τ
  have hfixed (σ : Gal(K/k)) : projectiveAction k K 3 σ p = p := by
    change ProjGenLinGroup.map σ.toRingHom (ProjGenLinGroup.mk (rotationUnit L)) = _
    rw [ProjGenLinGroup.map_mk]
    congr 1
    apply Units.ext
    change rotationMatrix.map σ = rotationMatrix
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotationMatrix, hX]
  let c : Cocycle k K 3 :=
    { val := m
      law := fun σ τ => by
        change m (σ * τ) = m σ * projectiveAction k K 3 σ (m τ)
        rw [map_mul]
        congr 1
        change p ^ (w.symm τ).toAdd.val = projectiveAction k K 3 σ (p ^ (w.symm τ).toAdd.val)
        rw [map_pow, hfixed] }
  let i := Multiplicative.ofAdd (1 : ZMod 3)
  let σ := w i
  have hdegree (x : RatFunc L) : (σ x).intDegree = x.intDegree := by
    obtain ⟨τ, hτ⟩ := e.surjective σ
    rw [← hτ]
    exact rationalFunctionAction_intDegree τ x
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, σ, c, hdegree, ?_⟩
  change (cyclicPowers p hp) (w.symm (w i)) = p
  rw [w.symm_apply_apply]
  exact pow_one p

private def unitsDegree {L : Type u} [Field L] : (RatFunc L)ˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd x.val.intDegree
  map_one' := by
    change Multiplicative.ofAdd (1 : RatFunc L).intDegree = _
    rw [RatFunc.intDegree_one]
    rfl
  map_mul' x y := (congrArg Multiplicative.ofAdd (RatFunc.intDegree_mul x.ne_zero y.ne_zero))

/-- The degrees of the two determinants are (1) and (-1). A change of
cocycle representative shifts the degree by a multiple of (3). -/
private theorem oppositeRotation_not_cohomologous {k L : Type} [Field k] [Field L]
    [Algebra k (RatFunc L)] (σ : Gal(RatFunc L/k))
    (hdeg : ∀ x : RatFunc L, (σ x).intDegree = x.intDegree)
    {c d : Cocycle k (RatFunc L) 3} (hc : c.val σ = ProjGenLinGroup.mk (rotationUnit L))
    (H : GL (Fin 3) (RatFunc L)) (hH : H.val = (↑(rotationUnit L)⁻¹ : Matrix (Fin 3) (Fin 3) _).transpose)
    (hd : ProjGenLinGroup.mk H = d.val σ) : ¬ Cohomologous k (RatFunc L) 3 c d := by
  rintro ⟨b, hb⟩
  obtain ⟨B, rfl⟩ := ProjGenLinGroup.mk_surjective b
  let g := rotationUnit L
  let B' := GeneralLinearGroup.map σ.toRingHom B
  have he : ProjGenLinGroup.mk (B⁻¹ * g * B') = ProjGenLinGroup.mk H := by
    have h := hb σ
    rw [hc, ← hd] at h
    change ProjGenLinGroup.mk H = (ProjGenLinGroup.mk B)⁻¹ * ProjGenLinGroup.mk g *
      ProjGenLinGroup.map σ.toRingHom (ProjGenLinGroup.mk B) at h
    simpa only [map_mul, map_inv, ProjGenLinGroup.map_mk, B'] using h.symm
  obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
  let m := (unitsDegree (L := L)).comp (GeneralLinearGroup.det (n := Fin 3))
  have hmG : (m g).toAdd = 1 := by
    change g.val.det.intDegree = 1
    change (rotationMatrix (L := L)).det.intDegree = 1
    rw [rotationMatrix_det, RatFunc.intDegree_X]
  have hmH : (m H).toAdd = -1 := by
    change H.val.det.intDegree = -1
    rw [hH, Matrix.det_transpose, ← GeneralLinearGroup.val_det_apply, map_inv, Units.val_inv_eq_inv_val]
    exact (RatFunc.intDegree_inv _).trans (congrArg Neg.neg hmG)
  have hmB : (m B').toAdd = (m B).toAdd := by
    change ((GeneralLinearGroup.det (GeneralLinearGroup.map σ.toRingHom B)).val).intDegree = _
    rw [GeneralLinearGroup.map_det]
    exact hdeg B.det.val
  have hmA : (m (GeneralLinearGroup.scalar (Fin 3) a)).toAdd = 3 * a.val.intDegree := by
    change (unitsDegree (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) a))).toAdd = _
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow]
    change (3 : ℕ) • a.val.intDegree = _
    simp
  have h := congrArg (fun u => (m u).toAdd) ha
  simp only [map_mul, map_inv] at h
  change -(m B).toAdd + (m g).toAdd + (m B').toAdd +
    (m (GeneralLinearGroup.scalar (Fin 3) a)).toAdd = (m H).toAdd at h
  rw [hmG, hmB, hmA, hmH] at h
  omega

theorem innerDataCanBeLost : InnerDataCanBeLost := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let L := GaloisField 2 3
  let K := RatFunc L
  have h : Module.finrank (ZMod 2) L = 3 := GaloisField.finrank 2 (by decide)
  obtain ⟨k, f, a, fd, gal, σ, c, hdeg, hc⟩ := cubicCocycle h
  letI := f
  letI := a
  letI := fd
  letI := gal
  have hn : 0 < (3 : ℕ) := by decide
  obtain ⟨actions, hActions⟩ := action_correspondence (k := k) (K := K) hn
  let ρ := actions c
  have hρ : Implements ρ c := (hActions c ρ).2 rfl
  obtain ⟨hA, hdegree, s, htransport, _⟩ := descended_form hn c ρ hρ
  obtain ⟨_, _, _, d, _, _, hTranspose, hClass⟩ :=
    oppositeTwisting hA s ρ c htransport hρ
  obtain ⟨H, hH, hD⟩ := hTranspose σ (rotationUnit L) hc.symm
  have hnot : ¬ Nonempty (ρ.fixedSubalgebra ≃ₐ[k] ρ.fixedSubalgebraᵐᵒᵖ) :=
    fun e => oppositeRotation_not_cohomologous σ hdeg hc H hH hD
      ((h1_eq_iff c d).1 (hClass.2 e))
  let A := ρ.fixedSubalgebra
  letI : Module.Finite k A := hA.2.2
  let hO := centralSimple_opposite hA
  letI : Module.Finite k Aᵐᵒᵖ := hO.2.2
  let b := Module.finBasis k A
  let b' := Module.finBasis k Aᵐᵒᵖ
  exact ⟨k, K, A, f, inferInstance, a, fd, gal, inferInstance, inferInstance,
    hA, hdegree, ⟨s⟩, hnot, _, _, inferInstance, inferInstance, b, b', oppositeNormOne hA b b'⟩

end DistinctInnerClasses

private theorem transpose_inv {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (a : Matrix.SpecialLinearGroup I R) : (a.transpose)⁻¹ = (a⁻¹).transpose := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change ((a⁻¹ : Matrix.SpecialLinearGroup I R) : Matrix I I R).transpose *
    (a : Matrix I I R).transpose = 1
  rw [← Matrix.transpose_mul]
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
    using congrArg (fun y : Matrix.SpecialLinearGroup I R => (y : Matrix I I R).transpose)
      (mul_inv_cancel a)

private theorem transposeInverse_involution {I R : Type*}
    [Fintype I] [DecidableEq I] [CommRing R] (x : Matrix.SpecialLinearGroup I R) :
    (((x⁻¹).transpose)⁻¹).transpose = x := by
  rw [transpose_inv, inv_inv]
  apply Subtype.ext
  exact Matrix.transpose_transpose _

private def transposeInverse {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R] :
    Matrix.SpecialLinearGroup I R ≃* Matrix.SpecialLinearGroup I R where
  toFun x := (x⁻¹).transpose
  invFun x := (x⁻¹).transpose
  left_inv := transposeInverse_involution
  right_inv := transposeInverse_involution
  map_mul' x y := by
    rw [_root_.mul_inv_rev]
    apply Subtype.ext
    exact Matrix.transpose_mul _ _

private theorem transposeInverse_not_conjugation {I k : Type*} [Fintype I]
    [DecidableEq I] [Field k] (hI : 3 ≤ Fintype.card I) (g : GL I k) :
    ∃ x : Matrix.SpecialLinearGroup I k,
      ((x⁻¹ : Matrix.SpecialLinearGroup I k) : Matrix I I k).transpose ≠
        (g : Matrix I I k) * (x : Matrix I I k) * (↑g⁻¹ : Matrix I I k) := by
  classical
  by_contra! h
  have hz (i j t : I) (hij : i ≠ j) (htj : t ≠ j) : (g : Matrix I I k) t i = 0 := by
    have he := h (Matrix.SpecialLinearGroup.transvection hij (1 : k))
    have he' := congrArg (· * (g : Matrix I I k)) he
    rw [Matrix.SpecialLinearGroup.transvection_inv, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_single, mul_assoc ((g : Matrix I I k) * _),
      Units.inv_mul, mul_one, add_mul, one_mul, mul_add, mul_one,
      add_right_inj] at he'
    have he'' := congrArg (fun m : Matrix I I k => m t j) he'
    simpa [Matrix.single_mul_apply_of_ne _ _ _ _ _ htj] using he''.symm
  have hg : (g : Matrix I I k) = 0 := by
    ext t i
    have hne : (Finset.univ \ ({i, t} : Finset I)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hh
      have hsub : (Finset.univ : Finset I) ⊆ {i, t} := by
        intro j hj
        by_contra hj'
        simpa [hh] using Finset.mem_sdiff.mpr ⟨hj, hj'⟩
      have hle := Finset.card_le_card hsub
      have hpair : ({i, t} : Finset I).card ≤ 2 := Finset.card_insert_le _ _
      simp only [Finset.card_univ] at hle
      omega
    obtain ⟨j, hj⟩ := hne
    have hj' : j ≠ i ∧ j ≠ t := by
      simpa using (Finset.mem_sdiff.mp hj).2
    exact hz i j t hj'.1.symm hj'.2.symm
  have : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  exact Units.ne_zero g hg

theorem transposeInverseOuter : TransposeInverseOuter.{u} := by
  intro k _ n hn
  refine ⟨NatIso.ofComponents (fun R => transposeInverse.toGrpIso) ?_, fun _ _ => rfl, ?_⟩
  · intro R S f
    apply GrpCat.ext
    intro x
    change transposeInverse (Matrix.SpecialLinearGroup.map f.hom.toRingHom x) =
      Matrix.SpecialLinearGroup.map f.hom.toRingHom (transposeInverse x)
    change ((Matrix.SpecialLinearGroup.map f.hom.toRingHom x)⁻¹).transpose =
      Matrix.SpecialLinearGroup.map f.hom.toRingHom ((x⁻¹).transpose)
    rw [← map_inv]
    apply Subtype.ext
    rfl
  · intro K _ _ g
    exact transposeInverse_not_conjugation (by simpa) g

end

end LinearAlgebraicGroups.Descent.InnerTypeA
