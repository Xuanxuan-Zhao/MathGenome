import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneMatrixWitnesses
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRankOneExtension
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped Matrix CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneMatrixWitnesses

open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalRankOneMatrixWitnesses
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.IntegralRootRelations (upper lower diagonal)
open CocharacterDynamics (cocharacterPoint unitPoint mapPoints_unitPoint)
open RootData.RootGroups (additivePoints)
open Specs.Unipotent (Index)

open private elementaryHom elementaryHom_closed elementaryHom_point
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SpecialLinearDatum

open private rootPoint_eq rootPoint_comp additiveLineGroup additiveLinePointsIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private unitEquiv unitEquiv_unitPoint unitPointHom_apply gm_baseChange
  subgroupInclusionFactors
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private exists_rankOne_pivots_after_injective_extension rankOne_pivot_factorization
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRankOneExtension
open private elementaryWord elementaryWord_diagonal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open private baseChangePointIso groupIsoOfPointIso isAffine_baseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F]

/-- The actual standard size-two group and its coordinate evaluation on test algebras. -/
abbrev standardGroup (F : Type u) [Field F] : AffineAlgebraicGroup F :=
  StandardGroups.specialLinearGroup F (Index.{u} 2)

def standardMatrix (F : Type u) [Field F] : SpecialMatrixPoints (standardGroup F) 2 :=
  StandardGroups.specialLinearGroupPointsIso F (Index.{u} 2)

/-- A unitriangular root coordinate defines a closed subgroup of a marked size-two group. -/
private def elementarySubgroup {J : AffineAlgebraicGroup F}
    (matrix : SpecialMatrixPoints J 2) (A : AdditiveLine F)
    {i j : Index.{u} 2} (hij : i ≠ j) : ClosedSubgroup J.val :=
  ⟨A.group, elementaryHom (r := 1) (s := matrix) A hij,
    elementaryHom_closed (r := 1) (s := matrix) A hij⟩

private theorem zero_ne_one_index : (⟨0⟩ : Index.{u} 2) ≠ ⟨1⟩ :=
  fun h ↦ Fin.zero_ne_one (congrArg ULift.down h)

private abbrev positiveSubgroup {J : AffineAlgebraicGroup F}
    (matrix : SpecialMatrixPoints J 2) (A : AdditiveLine F) : ClosedSubgroup J.val :=
  elementarySubgroup matrix A zero_ne_one_index

private abbrev negativeSubgroup {J : AffineAlgebraicGroup F}
    (matrix : SpecialMatrixPoints J 2) (A : AdditiveLine F) : ClosedSubgroup J.val :=
  elementarySubgroup matrix A (Ne.symm zero_ne_one_index)

private theorem positive_matrix {J : AffineAlgebraicGroup F} (matrix : SpecialMatrixPoints J 2)
    (A : AdditiveLine F) (R : TestAlgebra F) (r : R) :
    matrix.hom.app R (rootPoint (positiveSubgroup matrix A).inclusion R r) =
      liftMatrix (upper r) := by
  rw [show (positiveSubgroup matrix A).inclusion =
    elementaryHom (r := 1) (s := matrix) A zero_ne_one_index from rfl, elementaryHom_point]
  apply Subtype.ext
  apply Matrix.ext
  rintro ⟨i⟩ ⟨j⟩
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, liftMatrix, upper, Matrix.reindex, Matrix.submatrix]

private theorem negative_matrix {J : AffineAlgebraicGroup F} (matrix : SpecialMatrixPoints J 2)
    (A : AdditiveLine F) (R : TestAlgebra F) (r : R) :
    matrix.hom.app R (rootPoint (negativeSubgroup matrix A).inclusion R r) =
      liftMatrix (lower r) := by
  rw [show (negativeSubgroup matrix A).inclusion =
    elementaryHom (r := 1) (s := matrix) A (Ne.symm zero_ne_one_index) from rfl, elementaryHom_point]
  apply Subtype.ext
  apply Matrix.ext
  rintro ⟨i⟩ ⟨j⟩
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, liftMatrix, lower, Matrix.reindex, Matrix.submatrix]

private theorem positive_membership {J : AffineAlgebraicGroup F} (matrix : SpecialMatrixPoints J 2)
    (A : AdditiveLine F) (R : TestAlgebra F) (p : GroupPoints J.val R) :
    (∃ z : GroupPoints (positiveSubgroup matrix A).group R,
      pointHom (positiveSubgroup matrix A).inclusion R z = p) ↔
      let m := (matrix.hom.app R p).val
      m ⟨0⟩ ⟨0⟩ = 1 ∧ m ⟨1⟩ ⟨1⟩ = 1 ∧ m ⟨1⟩ ⟨0⟩ = 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨r, rfl⟩ := (additivePoints A R).surjective z
    simp only [pointHom, ← rootPoint_eq, positive_matrix]
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h00, h11, h10⟩
    let r := (matrix.hom.app R p).val ⟨0⟩ ⟨1⟩
    refine ⟨additivePoints A R r, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (matrix.hom.app R)).injective
    change matrix.hom.app R (additivePoints A R r ≫ _) = _
    rw [← rootPoint_eq, positive_matrix]
    apply Subtype.ext
    apply Matrix.ext
    rintro ⟨i⟩ ⟨j⟩
    fin_cases i <;> fin_cases j
    exacts [h00.symm, rfl, h10.symm, h11.symm]

private theorem negative_membership {J : AffineAlgebraicGroup F} (matrix : SpecialMatrixPoints J 2)
    (A : AdditiveLine F) (R : TestAlgebra F) (p : GroupPoints J.val R) :
    (∃ z : GroupPoints (negativeSubgroup matrix A).group R,
      pointHom (negativeSubgroup matrix A).inclusion R z = p) ↔
      let m := (matrix.hom.app R p).val
      m ⟨0⟩ ⟨0⟩ = 1 ∧ m ⟨1⟩ ⟨1⟩ = 1 ∧ m ⟨0⟩ ⟨1⟩ = 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨r, rfl⟩ := (additivePoints A R).surjective z
    simp only [pointHom, ← rootPoint_eq, negative_matrix]
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h00, h11, h01⟩
    let r := (matrix.hom.app R p).val ⟨1⟩ ⟨0⟩
    refine ⟨additivePoints A R r, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (matrix.hom.app R)).injective
    change matrix.hom.app R (additivePoints A R r ≫ _) = _
    rw [← rootPoint_eq, negative_matrix]
    apply Subtype.ext
    apply Matrix.ext
    rintro ⟨i⟩ ⟨j⟩
    fin_cases i <;> fin_cases j
    exacts [h00.symm, h01.symm, rfl, h11.symm]

/-- A closed immersion into an affine scheme is detected on a point after an
injective change of test algebra, by its ideal on global sections. -/
private theorem closedPoint_of_injective_test {G : GroupScheme F} (hG : IsAffine G.X.left)
    (H : ClosedSubgroup G) {R S : TestAlgebra F}
    (a : R ⟶ S) (ha : Function.Injective a.hom) (p : GroupPoints G R)
    (hp : ∃ z : GroupPoints H.group S, pointHom H.inclusion S z = mapPoints a p) :
    ∃ z : GroupPoints H.group R, pointHom H.inclusion R z = p := by
  obtain ⟨z, hz⟩ := hp
  let i := H.inclusion.hom.hom
  let f := (testSpec F).map a.op
  let : IsClosedImmersion i.left := H.isClosedImmersion
  let : IsAffine G.X.left := hG
  let : IsAffine ((testSpec F).obj (op R)).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  let : IsAffine ((testSpec F).obj (op S)).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of S)))
  let : QuasiCompact f.left := inferInstance
  let : QuasiCompact p.left := by
    change QuasiCompact (X := Spec (CommRingCat.of R)) (Y := G.X.left) p.left
    infer_instance
  have hf : Function.Injective f.left.appTop := by
    let b := CommRingCat.ofHom a.hom.toRingHom
    intro x y hxy
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).injective
    apply ha
    exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality b) x).symm.trans
      ((congrArg (Scheme.ΓSpecIso _).hom hxy).trans
        (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality b) y))
  have hzi : z.left ≫ i.left = f.left ≫ p.left := congrArg Over.Hom.left hz
  have hk : i.left.ker ≤ p.left.ker := by
    have le := z.left.le_ker_comp i.left
    rw [hzi] at le
    apply Scheme.IdealSheafData.le_of_isAffine
    have ll := le ⟨⊤, isAffineOpen_top G.X.left⟩
    rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at ll
    change RingHom.ker i.left.appTop.hom ≤ RingHom.ker (f.left ≫ p.left).appTop.hom at ll
    rw [Scheme.Hom.comp_appTop] at ll
    rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
    intro x hx
    have hzero := ll hx
    change f.left.appTop (p.left.appTop x) = 0 at hzero
    exact hf (hzero.trans (map_zero _).symm)
  let v := IsClosedImmersion.lift i.left p.left hk
  have hv : v ≫ i.left = p.left := IsClosedImmersion.lift_fac i.left p.left hk
  refine ⟨Over.homMk v ?_, Over.OverMorphism.ext hv⟩
  rw [← Over.w i, ← Category.assoc, hv, Over.w p]

private def matrixPointEquiv {J : AffineAlgebraicGroup F} (matrix : SpecialMatrixPoints J 2)
    (R : TestAlgebra F) : Matrix.SpecialLinearGroup (Fin 2) R ≃* GroupPoints J.val R :=
  liftMatrix.trans (matrix.app R).groupIsoToMulEquiv.symm

private theorem matrixPointEquiv_natural {J : AffineAlgebraicGroup F}
    (matrix : SpecialMatrixPoints J 2) {R S : TestAlgebra F} (a : R ⟶ S)
    (p : Matrix.SpecialLinearGroup (Fin 2) R) :
    matrixPointEquiv matrix S (Matrix.SpecialLinearGroup.map a.hom.toRingHom p) =
      mapPoints a (matrixPointEquiv matrix R p) := by
  exact ConcreteCategory.congr_hom (matrix.inv.naturality a) (liftMatrix p)

private theorem elementary_generate {J : AffineAlgebraicGroup F}
    (matrix : SpecialMatrixPoints J 2) (A : AdditiveLine F)
    (G : AffineAlgebraicGroup F) (i : J.val ⟶ G.val) (H : ClosedSubgroup G.val)
    (hp : ∃ f : (positiveSubgroup matrix A).group ⟶ H.group,
      f ≫ H.inclusion = (positiveSubgroup matrix A).inclusion ≫ i)
    (hn : ∃ f : (negativeSubgroup matrix A).group ⟶ H.group,
      f ≫ H.inclusion = (negativeSubgroup matrix A).inclusion ≫ i) :
    ∃ f : J.val ⟶ H.group, f ≫ H.inclusion = i := by
  obtain ⟨fpos, hfpos⟩ := hp
  obtain ⟨fneg, hfneg⟩ := hn
  apply subgroupInclusionFactors J.property.1 H i
  intro R p
  let m := (matrixPointEquiv matrix R).symm p
  obtain ⟨B, _, a, t, ha, hpivot⟩ := exists_rankOne_pivots_after_injective_extension [m]
  let : Algebra F B := (a.comp (algebraMap F R)).toAlgebra
  let S : TestAlgebra F := CommAlgCat.of F B
  let b : R ⟶ S := CommAlgCat.ofHom
    ({ toRingHom := a, commutes' := fun _ ↦ rfl } : R →ₐ[F] B)
  apply closedPoint_of_injective_test G.property.1 H b ha
  let inclusion := ((groupPointsFunctor F).map H.inclusion).app S
  let C := inclusion.hom.range
  let rho := (((groupPointsFunctor F).map i).app S).hom.comp
    (matrixPointEquiv matrix S).toMonoidHom
  have hupper (x : S) : rho (upper x) ∈ C := by
    have he : rootPoint (positiveSubgroup matrix A).inclusion S x =
        matrixPointEquiv matrix S (upper x) := by
      change _ = matrix.inv.app S (liftMatrix (upper x))
      rw [← positive_matrix matrix A S x]
      exact (ConcreteCategory.congr_hom (matrix.hom_inv_id_app S) _).symm
    refine ⟨pointHom fpos S (additivePoints A S x), ?_⟩
    change (additivePoints A S x ≫ fpos.hom.hom) ≫ H.inclusion.hom.hom =
      matrixPointEquiv matrix S (upper x) ≫ i.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hfpos, Grp.comp_hom_hom, ← Category.assoc]
    rw [← rootPoint_eq, he]
  have hlower (x : S) : rho (lower x) ∈ C := by
    have he : rootPoint (negativeSubgroup matrix A).inclusion S x =
        matrixPointEquiv matrix S (lower x) := by
      change _ = matrix.inv.app S (liftMatrix (lower x))
      rw [← negative_matrix matrix A S x]
      exact (ConcreteCategory.congr_hom (matrix.hom_inv_id_app S) _).symm
    refine ⟨pointHom fneg S (additivePoints A S x), ?_⟩
    change (additivePoints A S x ≫ fneg.hom.hom) ≫ H.inclusion.hom.hom =
      matrixPointEquiv matrix S (lower x) ≫ i.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hfneg, Grp.comp_hom_hom, ← Category.assoc]
    rw [← rootPoint_eq, he]
  have hword (d : Sˣ) : rho (elementaryWord d) ∈ C := by
    simp only [elementaryWord, map_mul]
    exact C.mul_mem (C.mul_mem (hupper _) (hlower _)) (hupper _)
  have hdiag (d : Sˣ) : rho (diagonal d) ∈ C := by
    have h := C.mul_mem (hword d) (C.inv_mem (hword 1))
    rwa [elementaryWord_diagonal d, map_mul, mul_inv_cancel_right] at h
  obtain ⟨d, hd⟩ := hpivot m (List.mem_singleton.mpr rfl)
  have hprod : rho (upper t * Matrix.SpecialLinearGroup.map a m) ∈ C := by
    rw [rankOne_pivot_factorization _ d hd]
    simp only [map_mul]
    exact C.mul_mem (C.mul_mem (hlower _) (hdiag _)) (hupper _)
  have hm : rho (Matrix.SpecialLinearGroup.map a m) ∈ C := by
    have h := C.mul_mem (C.inv_mem (hupper t)) hprod
    rwa [map_mul, inv_mul_cancel_left] at h
  have hpt : rho (Matrix.SpecialLinearGroup.map a m) = mapPoints b (pointHom i R p) := by
    change matrixPointEquiv matrix S (Matrix.SpecialLinearGroup.map b.hom.toRingHom m) ≫
      i.hom.hom = _
    rw [matrixPointEquiv_natural, MulEquiv.apply_symm_apply]
    exact Category.assoc _ _ _
  rw [hpt] at hm
  exact hm

private def diagonalHom (R : Type u) [CommRing R] :
    Rˣ →* Matrix.SpecialLinearGroup (Fin 2) R :=
  MonoidHom.mk' diagonal (by
    intro a b
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal, Matrix.mul_apply, Fin.sum_univ_two, mul_comm])

private theorem diagonal_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (t : Rˣ) :
    Matrix.SpecialLinearGroup.map f (diagonal t) = diagonal (Units.map f.toMonoidHom t) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]

private theorem exists_diagonal {J : AffineAlgebraicGroup F} (matrix : SpecialMatrixPoints J 2) :
    ∃ c : Cocharacter J.val, ∀ (R : TestAlgebra F) (t : Rˣ),
      matrix.hom.app R (cocharacterPoint c R t) = liftMatrix (diagonal t) := by
  let N : (groupPointsFunctor F).obj (multiplicativeLine F) ⟶
      (groupPointsFunctor F).obj J.val :=
    { app := fun R ↦ GrpCat.ofHom ((matrixPointEquiv matrix R).toMonoidHom.comp
        ((diagonalHom R).comp (unitEquiv R).toMonoidHom))
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro p
        obtain ⟨t, rfl⟩ := (unitEquiv R).symm.surjective p
        have ht := unitPointHom_apply R t
        change (unitEquiv R).symm t = unitPoint R t at ht
        rw [ht]
        change matrixPointEquiv matrix S (diagonal (unitEquiv S (mapPoints a (unitPoint R t)))) =
          mapPoints a (matrixPointEquiv matrix R (diagonal (unitEquiv R (unitPoint R t))))
        rw [mapPoints_unitPoint, unitEquiv_unitPoint, unitEquiv_unitPoint,
          ← matrixPointEquiv_natural, diagonal_map] }
  have ha : IsAffine (multiplicativeLine F).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of
      (MonoidAlgebra F Specs.DiagonalizableGroups.IntegerCharacters))))
  obtain ⟨c, hc⟩ := (groupHomComparison F _ _ ha).surjective N
  change (groupPointsFunctor F).map c = N at hc
  refine ⟨c, fun R t ↦ ?_⟩
  rw [cocharacterPoint, hc]
  change matrix.hom.app R (matrixPointEquiv matrix R (diagonal (unitEquiv R (unitPoint R t)))) = _
  rw [unitEquiv_unitPoint]
  exact ConcreteCategory.congr_hom (matrix.inv_hom_id_app R) _

private theorem exists_weylSection {J : AffineAlgebraicGroup F} (matrix : SpecialMatrixPoints J 2) :
    ∃ w : 𝟙_ (SchemeOver F) ⟶ J.val.X,
      (matrix.hom.app (CommAlgCat.of F F) (toUnit _ ≫ w)).val =
        (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F).submatrix ULift.down ULift.down := by
  let R := CommAlgCat.of F F
  let S := (testSpec F).obj (op R)
  have hS : IsTerminal S := by
    refine Over.mkIdTerminal.ofIso (Over.isoMk (Iso.refl (Spec (CommRingCat.of F))) ?_)
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap F F)) = 𝟙 _
    rw [Category.id_comp, show CommRingCat.ofHom (algebraMap F F) = 𝟙 (CommRingCat.of F) from
      CommRingCat.hom_ext (RingHom.ext (fun x : F => Algebra.algebraMap_self_apply x)), Spec.map_id]
  let w : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  let p : S ⟶ J.val.X := matrix.inv.app R (liftMatrix w)
  refine ⟨hS.from _ ≫ p, ?_⟩
  change (matrix.hom.app R (toUnit S ≫ (hS.from _ ≫ p))).val = _
  have hcomp : toUnit S ≫ (hS.from (𝟙_ (SchemeOver F)) ≫ p) = p := by
    rw [← Category.assoc, hS.hom_ext (toUnit S ≫ hS.from _) (𝟙 S), Category.id_comp]
  rw [hcomp]
  exact congrArg Subtype.val (ConcreteCategory.congr_hom (matrix.inv_hom_id_app R) (liftMatrix w))

/-- The elementary subgroup, diagonal and Weyl witnesses of the marked size-two group. -/
theorem matrixWitnesses : MatrixWitnesses.{u} := by
  intro F _ A J matrix
  obtain ⟨d, hd⟩ := exists_diagonal matrix
  obtain ⟨w, hw⟩ := exists_weylSection matrix
  refine ⟨{
    pos := positiveSubgroup matrix A
    neg := negativeSubgroup matrix A
    posCoord := Iso.refl _
    negCoord := Iso.refl _
    pos_matrix := ?_
    neg_matrix := ?_
    pos_membership := positive_membership matrix A
    neg_membership := negative_membership matrix A
    generates := fun G i _ H ↦ elementary_generate matrix A G i H
    diag := d
    diag_matrix := hd
    weyl := w
    weyl_matrix := hw }⟩
  · intro R r
    simpa only [Iso.refl_hom, Category.id_comp] using positive_matrix matrix A R r
  · intro R r
    simpa only [Iso.refl_hom, Category.id_comp] using negative_matrix matrix A R r

/-- The witnesses with the natural matrix comparison supplied by the standard group. -/
def standardWitnesses (F : Type u) [Field F] (A : AdditiveLine F) :
    Witnesses A (standardMatrix F) :=
  Classical.choice (matrixWitnesses F A (standardGroup F) (standardMatrix F))

section ScalarExtension

variable {K : Type u} [Field K] [Algebra F K]

private theorem representBaseChange {P : GroupScheme F} {Q : GroupScheme K}
    (hP : IsAffine P.X.left) (hQ : IsAffine Q.X.left)
    (N : (groupPointsFunctor K).obj Q ≅ restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj P) :
    ∃ e : Q ≅ (groupBaseChange F K).obj P, ∀ (R : TestAlgebra K) (p : GroupPoints Q R),
      baseChangePoint F K P.X R (pointHom e.hom R p) = N.hom.app R p := by
  let := hP
  let := hQ
  let := isAffine_baseChange K P
  let B := baseChangePointIso K P
  let e := groupIsoOfPointIso (N ≪≫ B.symm)
  have he : (groupPointsFunctor K).map e.hom = (N ≪≫ B.symm).hom :=
    (groupHomEquiv Q ((groupBaseChange F K).obj P) hQ).apply_symm_apply _
  refine ⟨e, fun R p ↦ ?_⟩
  calc
    _ = B.hom.app R (((groupPointsFunctor K).map e.hom).app R p) := rfl
    _ = _ := by
      rw [he]
      exact ConcreteCategory.congr_hom (B.inv_hom_id_app R) (N.hom.app R p)

private def restrictedMatrixPoints :
    Specs.StandardGroups.specialLinearPoints K (Index.{u} 2) ≅
      restrictTestAlgebra F K ⋙ Specs.StandardGroups.specialLinearPoints F (Index.{u} 2) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro R S f; rfl)

private def restrictedAdditivePoints :
    Specs.StandardGroups.additivePoints K ≅
      restrictTestAlgebra F K ⋙ Specs.StandardGroups.additivePoints F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro R S f; rfl)

private theorem matrixBaseChange {J : AffineAlgebraicGroup F} {J' : AffineAlgebraicGroup K}
    (matrix : SpecialMatrixPoints J 2) (matrix' : SpecialMatrixPoints J' 2) :
    ∃ e : J'.val ≅ (groupBaseChange F K).obj J.val,
      ∀ (R : TestAlgebra K) (p : GroupPoints J'.val R),
        matrix.hom.app ((restrictTestAlgebra F K).obj R)
          (baseChangePoint F K J.val.X R (pointHom e.hom R p)) = matrix'.hom.app R p := by
  let N := matrix' ≪≫ restrictedMatrixPoints (F := F) (K := K) ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra F K) matrix.symm
  obtain ⟨e, he⟩ := representBaseChange J.property.1 J'.property.1 N
  refine ⟨e, fun R p ↦ ?_⟩
  rw [he]
  exact ConcreteCategory.congr_hom (matrix.inv_hom_id_app ((restrictTestAlgebra F K).obj R))
    (matrix'.hom.app R p)

private theorem additiveBaseChange (A : AdditiveLine F) (B : AdditiveLine K) :
    ∃ a : B.group ≅ (groupBaseChange F K).obj A.group,
      ∀ (R : TestAlgebra K) (r : R),
        baseChangePoint F K A.group.X R (rootPoint a.hom R r) =
          rootPoint (𝟙 A.group) ((restrictTestAlgebra F K).obj R) r := by
  let N := (additiveLinePointsIso B).symm ≪≫ restrictedAdditivePoints (F := F) (K := K) ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra F K) (additiveLinePointsIso A)
  obtain ⟨a, ha⟩ := representBaseChange (additiveLineGroup A).property.1
    (additiveLineGroup B).property.1 N
  refine ⟨a, fun R r ↦ ?_⟩
  rw [rootPoint_eq, ha]
  change additivePoints A ((restrictTestAlgebra F K).obj R)
    ((additivePoints B R).symm (additivePoints B R r)) = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem pointHom_comp {k : Type u} [Field k] {G H L : GroupScheme k}
    (f : G ⟶ H) (g : H ⟶ L) (R : TestAlgebra k) (p : GroupPoints G R) :
    pointHom (f ≫ g) R p = pointHom g R (pointHom f R p) :=
  (Category.assoc _ _ _).symm

private theorem pointHom_id {k : Type u} [Field k] {G : GroupScheme k}
    (R : TestAlgebra k) (p : GroupPoints G R) : pointHom (𝟙 G) R p = p :=
  Category.comp_id _

private theorem baseChangePoint_comp {G H : GroupScheme F} (f : G ⟶ H)
    (R : TestAlgebra K) (p : GroupPoints ((groupBaseChange F K).obj G) R) :
    baseChangePoint F K H.X R (pointHom ((groupBaseChange F K).map f) R p) =
      pointHom f ((restrictTestAlgebra F K).obj R) (baseChangePoint F K G.X R p) :=
  baseChangePointsSchemeNaturality F K f.hom.hom R p

set_option maxHeartbeats 600000 in
/-- The marked scalar extension preserves the elementary parameters and the diagonal unit. -/
theorem matrixScalarExtension : MatrixScalarExtension.{u} := by
  intro F K _ _ _ A B J J' matrix matrix' W
  dsimp only
  obtain ⟨e, he⟩ := matrixBaseChange matrix matrix'
  obtain ⟨a, ha⟩ := additiveBaseChange A B
  obtain ⟨m, hm⟩ := gm_baseChange F K
  have hroot (f : A.group ⟶ J.val) (R : TestAlgebra K) (r : R) :
      matrix'.hom.app R (rootPoint (a.hom ≫ (groupBaseChange F K).map f ≫ e.inv) R r) =
        matrix.hom.app ((restrictTestAlgebra F K).obj R)
          (rootPoint f ((restrictTestAlgebra F K).obj R) r) := by
    rw [← he, rootPoint_comp]
    change matrix.hom.app _ (baseChangePoint F K J.val.X R
      (pointHom e.hom R (pointHom ((groupBaseChange F K).map f ≫ e.inv) R
        (rootPoint a.hom R r)))) = _
    rw [pointHom_comp, ← pointHom_comp e.inv, e.inv_hom_id, pointHom_id,
      baseChangePoint_comp, ha, rootPoint_eq f]
    rfl
  refine ⟨e, a, m, he, ha, hm, ?_, ?_, ?_⟩
  · intro R r
    exact (hroot (W.posCoord.hom ≫ W.pos.inclusion) R r).trans
      (W.pos_matrix ((restrictTestAlgebra F K).obj R) r)
  · intro R r
    exact (hroot (W.negCoord.hom ≫ W.neg.inclusion) R r).trans
      (W.neg_matrix ((restrictTestAlgebra F K).obj R) r)
  · intro R t
    rw [← he]
    change matrix.hom.app _ (baseChangePoint F K J.val.X R
      (pointHom e.hom R (pointHom (m.hom ≫ (groupBaseChange F K).map W.diag ≫ e.inv) R
        (unitPoint R t)))) = _
    rw [pointHom_comp m.hom, pointHom_comp ((groupBaseChange F K).map W.diag),
      ← pointHom_comp e.inv, e.inv_hom_id, pointHom_id, baseChangePoint_comp]
    rw [show baseChangePoint F K (multiplicativeLine F).X R (pointHom m.hom R (unitPoint R t)) =
      unitPoint ((restrictTestAlgebra F K).obj R) t from hm R t]
    exact W.diag_matrix ((restrictTestAlgebra F K).obj R) t

end ScalarExtension

/-- Scalar extension for the standard groups with their actual coordinate comparisons. -/
def standardMatrixScalarExtension (F K : Type u) [Field F] [Field K] [Algebra F K]
    (A : AdditiveLine F) (B : AdditiveLine K) :=
  matrixScalarExtension F K A B (standardGroup F) (standardGroup K)
    (standardMatrix F) (standardMatrix K) (standardWitnesses F A)

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneMatrixWitnesses
