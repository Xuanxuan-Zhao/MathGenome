import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.DivisionNormOneAdelicCompactness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology Filter Matrix
open scoped TensorProduct RestrictedProduct MatrixGroups

universe u v z

namespace LinearAlgebraicGroups.Arithmetic.DivisionNormOneAdelicCompactness

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups (groupHomEquiv groupPointsFunctor TestAlgebra Points mapPoints
  testSpec SchemeOver)
open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.OuterTypeAModels (RepresentsNormOne)
open Specs.Unipotent (Index)
open Specs.StandardGroups (GLCoordinates universalMatrix generalLinearPoints)
open Specs.DivisionOctonionOrthogonalTensors
open Descent.InnerTypeA.Specification (NormOneCoordinates normOneIdeal)
open IsotropicInnerTypeA.Spec (NormOnePresentation)
open AdelicGroups ArithmeticLatticeProjection
open RM03.CSA (IsCentralSimple)
open RM03.CSA.NormOneGroup (normOne normOneFunctor mapNormOne changeCoefficients
  normAt_basis_independent)

open private existsPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA
open private coordinateMap coordinateMap_spec glPoint_eval affineGroupIsoOfPoints
  affineGroupIsoOfPoints_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private matrixCoordinates_value from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.DivisionOctonionOrthogonalTensors
open private coord_change from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

set_option allowUnsafeReducibility true in
attribute [local reducible] _root_.Specs.RM03.CSA.isCentralSimple RM03.CSA.IsCentralSimple

section RegularRealization

variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (hA : IsCentralSimple K A) (b : Module.Basis I K A)

private def normOnePointsIsoOf {G : AffineAlgebraicGroup K}
    (p : ∀ R : TestAlgebra K, Points G.val.X R ≃ normOne (R := R) hA b)
    (hmul : ∀ R (x y : ((groupPointsFunctor K).obj G.val).obj R),
      (p R (x * y)).val = (p R x).val * (p R y).val)
    (hnat : ∀ {R S : TestAlgebra K} (f : R ⟶ S) (x : Points G.val.X R),
      (p S (mapPoints f x)).val =
        Algebra.TensorProduct.map f.hom (.id K A) (p R x).val) :
    (groupPointsFunctor K).obj G.val ≅ normOneFunctor hA b := by
  refine NatIso.ofComponents (fun R => ?_) ?_
  · letI := RM03.CSA.NormOneGroup.normOneGroup (R := R) hA b
    exact (show ((groupPointsFunctor K).obj G.val).obj R ≃* normOne (R := R) hA b from
      { toEquiv := p R
        map_mul' := fun x y => Subtype.ext (hmul R x y) }).toGrpIso
  · intro R S f
    ext x : 2
    exact Subtype.ext (hnat f x)

private def normOnePointsIso {G : AffineAlgebraicGroup K}
    (h : RepresentsNormOne hA b G) :
    (groupPointsFunctor K).obj G.val ≅ normOneFunctor hA b :=
  normOnePointsIsoOf hA b (Classical.choose h) (Classical.choose_spec h).1
    (Classical.choose_spec h).2

private theorem representsNormOne_changeBasis {J : Type u} [Fintype J]
    (c : Module.Basis J K A) {G : AffineAlgebraicGroup K} (h : RepresentsNormOne hA b G) :
    RepresentsNormOne hA c G := by
  obtain ⟨p, hm, hn⟩ := h
  refine ⟨fun R => (p R).trans (Equiv.subtypeEquivRight (fun x => ?_)), hm, hn⟩
  rw [show _root_.Specs.RM03.CSA.NormOneGroup.normAt hA b x =
    _root_.Specs.RM03.CSA.NormOneGroup.normAt hA c x from normAt_basis_independent hA b c x]

end RegularRealization

section RegularMatrices

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
variable {I : Type z} [Fintype I]
variable (hA : IsCentralSimple K A) (b : Module.Basis I K A)

private def regularUnits {R : Type u} [CommRing R] [Algebra K R] :
    normOne (R := R) hA b →* (R ⊗[K] A)ˣ :=
  (show normOne (R := R) hA b →* R ⊗[K] A from
    { toFun := Subtype.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl }).toHomUnits

private def regularMatrix [DecidableEq I] {R : Type u} [CommRing R] [Algebra K R] :
    normOne (R := R) hA b →* GL I R :=
  ((matrixCoordinates (b.baseChange R)).toMonoidHom.comp leftUnit).comp (regularUnits hA b)

private theorem regularMatrix_field [DecidableEq I] {R : Type u} [Field R] [Algebra K R] :
    regularMatrix (R := R) hA b = divisionNormOneMatrixHom hA b := rfl

private theorem regularMatrix_entry [DecidableEq I]
    {R : Type u} [CommRing R] [Algebra K R] (x : normOne (R := R) hA b) (i j : I) :
    (regularMatrix hA b x).val i j =
      (b.baseChange R).repr (x.val * (1 ⊗ₜ[K] b j)) i := by
  change (matrixCoordinates (b.baseChange R) (leftUnit (regularUnits hA b x))).val i j = _
  rw [matrixCoordinates_value, LinearMap.toMatrix_apply, Module.Basis.baseChange_apply]
  rfl

private theorem regularMatrix_mulVec_one [DecidableEq I]
    {R : Type u} [CommRing R] [Algebra K R] (x : normOne (R := R) hA b) :
    (regularMatrix hA b x).val.mulVec ((b.baseChange R).equivFun 1) =
      (b.baseChange R).equivFun x.val := by
  have h := (DivisionOctonionOrthogonalTensors.matrixCoordinateComparison
    (b.baseChange R) (leftUnit (regularUnits hA b x)) 1).1
  change (regularMatrix hA b x).val.mulVec ((b.baseChange R).equivFun 1) =
    (b.baseChange R).equivFun (x.val * 1) at h
  simpa only [mul_one] using h

private def reindexMatrix {J L R : Type*} [CommRing R] [Fintype J] [DecidableEq J]
    [Fintype L] [DecidableEq L] (e : J ≃ L) : GL J R →* GL L R :=
  Units.map (Matrix.reindexRingEquiv R e).toMonoidHom

private theorem reindexMatrix_symm {J L R : Type*} [CommRing R] [Fintype J] [DecidableEq J]
    [Fintype L] [DecidableEq L] (e : J ≃ L) (x : GL J R) :
    reindexMatrix e.symm (reindexMatrix e x) = x := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change x.val (e.symm (e i)) (e.symm (e j)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

private theorem reindexMatrix_trans {J L N R : Type*} [CommRing R] [Fintype J]
    [DecidableEq J] [Fintype L] [DecidableEq L] [Fintype N] [DecidableEq N]
    (e : J ≃ L) (f : L ≃ N) (x : GL J R) :
    reindexMatrix (e.trans f) x = reindexMatrix f (reindexMatrix e x) := by
  apply Units.ext
  rfl

private theorem regularMatrix_range_reindex [DecidableEq I] {J : Type*}
    [Fintype J] [DecidableEq J] {R : Type u} [CommRing R] [Algebra K R] (e : I ≃ J) :
    ((reindexMatrix e).comp (regularMatrix (R := R) hA b)).range =
      (regularMatrix (R := R) hA (b.reindex e)).range := by
  let c := b.reindex e
  have hc : c.baseChange R = (b.baseChange R).reindex e := by
    ext j
    simp [c]
  let p : normOne (R := R) hA b ≃ normOne (R := R) hA c :=
    Equiv.subtypeEquivRight (fun x => by rw [normAt_basis_independent hA b c x])
  have he (x : normOne (R := R) hA b) :
      reindexMatrix e (regularMatrix hA b x) = regularMatrix hA c (p x) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change (regularMatrix hA b x).val (e.symm i) (e.symm j) = _
    rw [regularMatrix_entry, regularMatrix_entry, hc]
    simp [c, p]
  ext y
  show (∃ x : normOne (R := R) hA b, reindexMatrix e (regularMatrix hA b x) = y) ↔
    (∃ x : normOne (R := R) hA c, regularMatrix hA c x = y)
  simp_rw [he]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨p x, hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := p.surjective x
    exact ⟨y, hx⟩

private theorem reindexMatrix_natural {J L R S : Type*} [CommRing R] [CommRing S]
    [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
    (e : J ≃ L) (f : R →+* S) (x : GL J R) :
    reindexMatrix e (GeneralLinearGroup.map f x) = GeneralLinearGroup.map f (reindexMatrix e x) := by
  apply Units.ext
  rfl

private theorem continuous_reindexMatrix {J L R : Type*} [CommRing R] [TopologicalSpace R]
    [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] (e : J ≃ L) :
    Continuous (reindexMatrix (R := R) e) := by
  refine Continuous.units_map (f := (Matrix.reindexRingEquiv R e).toMonoidHom) ?_
  exact continuous_matrix fun i j => (continuous_apply (e.symm j)).comp
    (continuous_apply (e.symm i))

private theorem reindexMatrix_integral {J L R : Type*} [CommRing R]
    [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
    (e : J ≃ L) (O : Subring R) (x : GL J R) :
    reindexMatrix e x ∈ (GeneralLinearGroup.map O.subtype).range ↔
      x ∈ (GeneralLinearGroup.map O.subtype).range := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨reindexMatrix e.symm y, ?_⟩
    rw [← reindexMatrix_natural, hy, reindexMatrix_symm]
  · rintro ⟨y, rfl⟩
    exact ⟨reindexMatrix e y, (reindexMatrix_natural _ _ _).symm⟩

variable {n : ℕ}

private def regularMatrixNat (c : Module.Basis (Index.{u} n) K A) :
    normOneFunctor hA c ⟶ generalLinearPoints K (Index.{u} n) where
  app R := by
    change GrpCat.of (normOne (R := R) hA c) ⟶ GrpCat.of (GL (Index.{u} n) R)
    exact GrpCat.ofHom (regularMatrix (R := R) hA c)
  naturality R S f := by
    ext x : 2
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    symm
    change f.hom ((regularMatrix hA c x).val i j) =
      (regularMatrix hA c (mapNormOne hA c f.hom x)).val i j
    rw [regularMatrix_entry, regularMatrix_entry]
    change f.hom ((c.baseChange R).repr (x.val * (1 ⊗ₜ[K] c j)) i) =
      (c.baseChange S).repr (changeCoefficients f.hom x.val * (1 ⊗ₜ[K] c j)) i
    rw [← show changeCoefficients f.hom ((1 : R) ⊗ₜ[K] c j) =
        (1 : S) ⊗ₜ[K] c j by simp [changeCoefficients, Algebra.TensorProduct.map_tmul],
      ← map_mul]
    exact (coord_change c f.hom _ _).symm

/-- The regular representation is closed because its coordinate matrix recovers
the universal norm-one element by acting on the identity. -/
private theorem existsRegularRealization (c : Module.Basis (Index.{u} n) K A)
    {G : AffineAlgebraicGroup K} (h : RepresentsNormOne hA c G) :
    ∃ i : MatrixRealization G, ∃ e : Index.{u} i.size ≃ Index.{u} n,
      ∀ (R : Type u) [CommRing R] [Algebra K R] (x : PointsIn i R),
        reindexMatrix e (asMatrix i R x) =
          regularMatrix hA c
            (show normOne (R := R) hA c from
              (normOnePointsIso hA c h).hom.app (CommAlgCat.of K R) x) := by
  obtain ⟨P⟩ := existsPresentation hA c
  let N := P.group
  let pN := normOnePointsIsoOf hA c P.point P.point_mul P.point_natural
  let pG := normOnePointsIso hA c h
  let L := StandardGroups.generalLinearGroup K (Index.{u} n)
  let m := StandardGroups.generalLinearGroupPointsIso K (Index.{u} n)
  let α := regularMatrixNat hA c
  let q := pN.hom ≫ α ≫ m.inv
  let f : N.val ⟶ L.val := (groupHomEquiv N.val L.val N.prop.1).symm q
  have hf : (groupPointsFunctor K).map f = q :=
    (groupHomEquiv N.val L.val N.prop.1).apply_symm_apply _
  let Q := NormOneCoordinates hA c
  let T := CommAlgCat.of K Q
  let d : CommAlgCat.of K (GLCoordinates K (Index.{u} n)) ⟶ T :=
    coordinateMap (k := K) f.hom.hom
  have hd : (testSpec K).map d.op = f.hom.hom := coordinateMap_spec _
  let x : normOne (R := Q) hA c := P.point T (𝟙 ((testSpec K).obj (op T)))
  have hx (j : Index.{u} n) : (c.baseChange Q).repr x.val j =
      Ideal.Quotient.mk (normOneIdeal hA c) (MvPolynomial.X j) := by
    have hid : (testSpec K).map (CommAlgCat.ofHom (AlgHom.id K Q)).op =
        𝟙 ((testSpec K).obj (op T)) := by
      change (testSpec K).map (𝟙 (op T)) = _
      exact (testSpec K).map_id _
    have hcoord := P.coordinate T (AlgHom.id K Q) j
    rw [hid] at hcoord
    exact hcoord
  have hentry (i j : Index.{u} n) :
      d.hom (universalMatrix K (Index.{u} n) i j) =
        (regularMatrix hA c x).val i j := by
    rw [← glPoint_eval, hd]
    have hp := congrArg (fun β => β.app T (𝟙 ((testSpec K).obj (op T)))) hf
    change f.hom.hom = m.inv.app T (regularMatrix hA c x) at hp
    rw [hp]
    exact congrArg (fun a : GL (Index.{u} n) Q => a.val i j)
      (GrpCat.hom_inv_apply (m.app T) (regularMatrix hA c x))
  have hsurj : Function.Surjective d.hom := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    let w (j : Index.{u} n) : K := c.repr 1 j
    let y (i : Index.{u} n) : GLCoordinates K (Index.{u} n) :=
      ∑ j, universalMatrix K (Index.{u} n) i j * algebraMap K _ (w j)
    have hy (i : Index.{u} n) : d.hom (y i) =
        Ideal.Quotient.mk (normOneIdeal hA c) (MvPolynomial.X i) := by
      have hw (j : Index.{u} n) :
          (c.baseChange Q).equivFun 1 j = algebraMap K Q (w j) := by
        change (c.baseChange Q).repr ((1 : Q) ⊗ₜ[K] (1 : A)) j = _
        rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
      rw [← hx]
      have hvec := congrFun (regularMatrix_mulVec_one hA c x) i
      simp only [y, map_sum, map_mul, AlgHom.commutes, hentry]
      simpa only [Matrix.mulVec, dotProduct, hw, Module.Basis.equivFun_apply] using hvec
    refine ⟨MvPolynomial.aeval y p, ?_⟩
    have he : d.hom.comp (MvPolynomial.aeval y) =
        Ideal.Quotient.mkₐ K (normOneIdeal hA c) := by
      ext j
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
      exact hy j
    exact DFunLike.congr_fun he p
  have hfclosed : IsClosedImmersion f.hom.hom.left := by
    have he := congrArg Over.Hom.left hd
    rw [algSpec_map_left] at he
    exact he ▸ IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom d.hom.toRingHom) hsurj
  let e : G.val ≅ N.val :=
    affineGroupIsoOfPoints G.prop.1 N.prop.1 (pG ≪≫ pN.symm)
  have he : (groupPointsFunctor K).map e.hom = (pG ≪≫ pN.symm).hom :=
    affineGroupIsoOfPoints_map G.prop.1 N.prop.1 _
  let i : MatrixRealization G :=
    { size := n
      ambient := L
      matrix := m
      embedding := e.hom ≫ f
      closed := by
        change IsClosedImmersion (e.hom.hom.hom.left ≫ f.hom.hom.left)
        letI : IsIso e.hom.hom.hom.left :=
          (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso e.hom
        letI := hfclosed
        infer_instance }
  refine ⟨i, Equiv.refl _, fun R _ _ x => ?_⟩
  let S := CommAlgCat.of K R
  change m.hom.app S (((groupPointsFunctor K).map (e.hom ≫ f)).app S x) = _
  rw [Functor.map_comp, hf, he]
  change m.hom.app S (m.inv.app S (α.app S (pN.hom.app S
    (pN.inv.app S (pG.hom.app S x))))) = _
  let t : (normOneFunctor hA c).obj S := pG.hom.app S x
  calc
    _ = α.app S (pN.hom.app S (pN.inv.app S t)) :=
      GrpCat.hom_inv_apply (m.app S) _
    _ = α.app S t := congrArg (fun z : (normOneFunctor hA c).obj S => α.app S z)
      (GrpCat.hom_inv_apply (pN.app S) t)
    _ = _ := by apply Units.ext; rfl

end RegularMatrices

section MatrixAdeles

open Specs.AnisotropicTensorQuotients
open TensorAdelicReduction (integralMatrices)
open private MatrixAdeles matrixAt continuous_matrixAt adelicMatrixGroup mem_localConditions
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients
open private integralMatrices_isOpen from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TensorAdelicReduction

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K} {n : ℕ}
variable (D : GlobalFieldData.{u, v} K)

private abbrev FullPlace := Outside D ∅

private abbrev fullPlace (w : D.Place) : FullPlace D :=
  ⟨w, Finset.notMem_empty _⟩

private theorem finitePlaceTendsto :
    Tendsto (fun w : D.FinitePlace => fullPlace D (.inl w)) cofinite cofinite := by
  apply Function.Injective.tendsto_cofinite
  intro x y h
  exact Sum.inl.inj (congrArg Subtype.val h)

private abbrev finiteMatrixSubgroup (w : D.FinitePlace) :=
  integralMatrices (I := Fin n) (D.integers w).toSubring

private abbrev FiniteMatrixProduct :=
  Πʳ w : D.FinitePlace, [GL (Fin n) (D.FiniteCompletion w),
    ↑(finiteMatrixSubgroup (n := n) D w)]

private def finiteMatrixPart : MatrixAdeles D (Fin n) → FiniteMatrixProduct (n := n) D := by
  cases D with
  | number h => letI := h; exact Prod.fst
  | function F t => exact id

private theorem continuous_finiteMatrixPart :
    Continuous (finiteMatrixPart (n := n) D) := by
  cases D with
  | number h => letI := h; exact continuous_fst
  | function F t => exact continuous_id

private theorem finiteMatrixPart_apply (x : MatrixAdeles D (Fin n)) (w : D.FinitePlace) :
    finiteMatrixPart D x w = matrixAt D (.inl w) x := by
  cases D <;> rfl

private theorem finiteMatrixSubgroup_open (w : D.FinitePlace) :
    IsOpen (finiteMatrixSubgroup (n := n) D w :
      Set (GL (Fin n) (D.FiniteCompletion w))) := by
  exact integralMatrices_isOpen (D.integers w) (D.integers_properties w).2.1

private def fullMatrixTuple (x : FiniteMatrixProduct (n := n) D)
    (y : ∀ w : D.InfinitePlace, GL (Fin n) (D.Completion (.inr w))) :
    MatrixAdeles D (Fin n) := by
  cases D with
  | number h => letI := h; exact (x, y)
  | function F t => exact x

private theorem fullMatrixTuple_at
    (x : FiniteMatrixProduct (n := n) D) (y : ∀ w : D.InfinitePlace,
      GL (Fin n) (D.Completion (.inr w))) (w : D.Place) :
    matrixAt D w (fullMatrixTuple D x y) =
      (match w with | .inl s => x s | .inr s => y s) := by
  cases D with
  | number h => cases w <;> rfl
  | function F t =>
    cases w with
    | inl w => rfl
    | inr w => exact w.elim

private theorem continuous_fullMatrixTuple {X : Type*} [TopologicalSpace X]
    {x : X → FiniteMatrixProduct (n := n) D}
    {y : X → (∀ w : D.InfinitePlace, GL (Fin n) (D.Completion (.inr w)))}
    (hx : Continuous x) (hy : Continuous y) :
    Continuous (fun a => fullMatrixTuple D (x a) (y a)) := by
  cases D with
  | number h => letI := h; exact hx.prodMk hy
  | function F t => exact hx

private theorem fullMatrix_ext {a b : MatrixAdeles D (Fin n)}
    (h : ∀ w : D.Place, matrixAt D w a = matrixAt D w b) : a = b := by
  cases D with
  | number hK =>
    letI := hK
    apply Prod.ext
    · exact RestrictedProduct.ext _ _ (fun w => h (.inl w))
    · exact funext (fun w => h (.inr w))
  | function F t =>
    exact RestrictedProduct.ext _ _ (fun w => h (.inl w))

private theorem globalMatrixCompactQuotient (M : MatrixModel K (Fin n))
    (h : GlobalMatrixQuotientCompact D M) :
    ∃ δ : GL (Fin n) K →* MatrixAdeles D (Fin n),
      (∀ r w, matrixAt D w (δ r) = GeneralLinearGroup.map (D.embedding w) r) ∧
      CompactMatrixQuotient (adelicMatrixGroup D M) (M K (RingHom.id K)) δ := by
  cases D with
  | number hK =>
    letI := hK
    obtain ⟨δ, hδ, hQ⟩ := h
    have he : adelicMatrixGroup (GlobalFieldData.number.{u,v} hK) M =
        localConditions numberAtPlace (fun (w : NumberPlace K) => M w.Completion w.embedding) := by
      ext x
      simp only [adelicMatrixGroup, mem_localConditions]
      constructor <;> intro hx w <;> cases w
      · exact hx (.inl _)
      · exact hx (.inr _)
      · exact hx (.inl _)
      · exact hx (.inr _)
    refine ⟨δ, fun r w => ?_, he ▸ hQ⟩
    cases w with
    | inl w => exact hδ r (.inl w)
    | inr w => exact hδ r (.inr w)
  | function F t =>
    obtain ⟨δ, hδ, hQ⟩ := h
    have he : adelicMatrixGroup (GlobalFieldData.function F t) M =
        localConditions functionAtPlace (fun (w : FunctionPlace K) => M w.Completion w.embedding) := by
      ext x
      simp only [adelicMatrixGroup, mem_localConditions]
      exact ⟨fun h w => h (.inl w), fun h w => by
        cases w with
        | inl w => exact h w
        | inr w => exact w.elim⟩
    refine ⟨δ, fun r w => ?_, he ▸ hQ⟩
    cases w with
    | inl w => exact hδ r w
    | inr w => exact w.elim

variable (i : MatrixRealization G) (M : MatrixModel K (Fin n))
variable (f : ∀ w : D.Place, LocalPoints D i w →* GL (Fin n) (D.Completion w))
variable (hf : ∀ w, Function.Injective (f w))
variable (hr : ∀ w, (f w).range = M (D.Completion w) (D.embedding w))
variable (ht : ∀ w, IsInducing (f w))
variable (hO : ∀ w : D.FinitePlace, ∀ x : LocalPoints D i (.inl w),
  f (.inl w) x ∈ finiteMatrixSubgroup D w ↔ x ∈ localSubgroup D i (.inl w))

private def localMatrixEquiv (w : D.Place) :
    LocalPoints D i w ≃* M (D.Completion w) (D.embedding w) :=
  MulEquiv.ofBijective
    ((f w).codRestrict _ (fun x => (hr w) ▸ (show f w x ∈ (f w).range from ⟨x, rfl⟩))) (by
      constructor
      · exact fun _ _ h => hf w (congrArg Subtype.val h)
      · intro x
        have hx : x.val ∈ (f w).range := (hr w).symm ▸ x.property
        obtain ⟨y, hy⟩ := hx
        exact ⟨y, Subtype.ext hy⟩)

private def matrixAdelesToPoints (x : adelicMatrixGroup D M) : Adeles D i ∅ := by
  let g (w : FullPlace D) : LocalPoints D i w.val :=
    (localMatrixEquiv D i M f hf hr w.val).symm
      ⟨matrixAt D w.val x.val, (mem_localConditions _ _ _).mp x.property w.val⟩
  refine ⟨g, ?_⟩
  have hg (w : D.Place) : f w (g (fullPlace D w)) = matrixAt D w x.val :=
    congrArg Subtype.val ((localMatrixEquiv D i M f hf hr w).apply_symm_apply _)
  have hfin : {w | finiteMatrixPart D x.val w ∉ finiteMatrixSubgroup D w}.Finite :=
    mem_cofinite.mp (finiteMatrixPart D x.val).eventually
  apply mem_cofinite.mpr
  refine (hfin.image (fun w => fullPlace D (.inl w))).subset ?_
  rintro ⟨w, hw⟩ hx
  cases w with
  | inl w =>
    refine ⟨w, ?_, rfl⟩
    intro hw'
    apply hx
    apply (hO w _).mp
    change f (.inl w) (g (fullPlace D (.inl w))) ∈ finiteMatrixSubgroup D w
    rw [hg (.inl w), ← finiteMatrixPart_apply]
    exact hw'
  | inr w =>
    exact (hx (Subgroup.mem_top _)).elim

private theorem matrixAdelesToPoints_apply (x : adelicMatrixGroup D M) (w : FullPlace D) :
    f w.val (matrixAdelesToPoints D i M f hf hr hO x w) = matrixAt D w.val x.val :=
  congrArg Subtype.val ((localMatrixEquiv D i M f hf hr w.val).apply_symm_apply _)

include ht in
private theorem continuous_matrixAdelesToPoints :
    Continuous (matrixAdelesToPoints D i M f hf hr hO) := by
  let g := matrixAdelesToPoints D i M f hf hr hO
  have hc (w : FullPlace D) : Continuous (fun x => g x w) := by
    apply (ht w.val).continuous_iff.mpr
    change Continuous (fun x => f w.val (g x w))
    simp only [g, matrixAdelesToPoints_apply]
    exact (continuous_matrixAt D w.val).comp continuous_subtype_val
  rw [(adelicBasis D i ∅).continuous_iff]
  rintro U ⟨T, V, hV, hT, rfl⟩
  have he : g ⁻¹' box D i ∅ V =
      (fun x w => g x w) ⁻¹' (↑T : Set (FullPlace D)).pi V ∩
      (fun x : adelicMatrixGroup D M => finiteMatrixPart D x.val) ⁻¹'
        {a | ∀ w : D.FinitePlace, fullPlace D (.inl w) ∉ T →
          a w ∈ finiteMatrixSubgroup D w} := by
    ext x
    constructor
    · intro hx
      refine ⟨fun w _ => hx w, fun w hw => ?_⟩
      rw [finiteMatrixPart_apply, ← matrixAdelesToPoints_apply D i M f hf hr hO x (fullPlace D (.inl w))]
      apply (hO w _).mpr
      have h := hx (fullPlace D (.inl w))
      change g x (fullPlace D (.inl w)) ∈ V _ at h
      rwa [hT _ hw] at h
    · rintro ⟨hx, hy⟩ ⟨w, hw⟩
      by_cases hmem : (⟨w, hw⟩ : FullPlace D) ∈ T
      · exact hx _ hmem
      · rw [hT _ hmem]
        cases w with
        | inl w =>
          apply (hO w _).mp
          have hm := matrixAdelesToPoints_apply D i M f hf hr hO x (fullPlace D (.inl w))
          rw [← finiteMatrixPart_apply] at hm
          exact hm.symm ▸ hy w hmem
        | inr w => exact Subgroup.mem_top _
  change IsOpen (g ⁻¹' _)
  rw [he]
  exact ((isOpen_set_pi T.finite_toSet (fun w _ => hV w)).preimage (continuous_pi hc)).inter
    ((RestrictedProduct.isOpen_forall_imp_mem (finiteMatrixSubgroup_open D)).preimage
      ((continuous_finiteMatrixPart D).comp continuous_subtype_val))

private def pointsToMatrixAdeles (x : Adeles D i ∅) : MatrixAdeles D (Fin n) :=
  fullMatrixTuple D
    (RestrictedProduct.mapAlong _ _ _ (finitePlaceTendsto D)
      (fun w => f (.inl w)) (Eventually.of_forall fun w _ hx => (hO w _).mpr hx) x)
    (fun w => f (.inr w) (x (fullPlace D (.inr w))))

private theorem pointsToMatrixAdeles_apply (x : Adeles D i ∅) (w : FullPlace D) :
    matrixAt D w.val (pointsToMatrixAdeles D i f hO x) = f w.val (x w) := by
  rw [pointsToMatrixAdeles, fullMatrixTuple_at]
  rcases w with ⟨w, hw⟩
  cases w <;> rfl

include ht in
private theorem continuous_pointsToMatrixAdeles :
    Continuous (pointsToMatrixAdeles D i f hO) := by
  apply continuous_fullMatrixTuple D
  · apply RestrictedProduct.mapAlong_continuous
    exact fun w => (ht (.inl w)).continuous
  · exact continuous_pi fun w => (ht (.inr w)).continuous.comp
      (RestrictedProduct.continuous_eval (fullPlace D (.inr w)))

/-- The subgroup topology in matrix adeles agrees with the restricted product
topology on scheme points. At each finite place the integral subgroups match. -/
private def adelicMatrixEquiv :
    adelicMatrixGroup D M ≃ₜ* Adeles D i ∅ := by
  let g := matrixAdelesToPoints D i M f hf hr hO
  let j (x : Adeles D i ∅) : adelicMatrixGroup D M :=
    ⟨pointsToMatrixAdeles D i f hO x, (mem_localConditions _ _ _).mpr fun w => by
      have h := pointsToMatrixAdeles_apply D i f hO x (fullPlace D w)
      change matrixAt D w (pointsToMatrixAdeles D i f hO x) = _ at h
      rw [h, ← hr w]
      exact ⟨_, rfl⟩⟩
  have hg (x : adelicMatrixGroup D M) (w : FullPlace D) :
      f w.val (g x w) = matrixAt D w.val x.val :=
    matrixAdelesToPoints_apply D i M f hf hr hO x w
  refine
    { toFun := g
      invFun := j
      left_inv := fun x => Subtype.ext (fullMatrix_ext D fun w => ?_)
      right_inv := fun x => RestrictedProduct.ext _ _ fun w => ?_
      map_mul' := fun x y => RestrictedProduct.ext _ _ fun w => ?_
      continuous_toFun := continuous_matrixAdelesToPoints D i M f hf hr ht hO
      continuous_invFun := (continuous_pointsToMatrixAdeles D i f ht hO).subtype_mk _ }
  · change matrixAt D w (pointsToMatrixAdeles D i f hO (g x)) = _
    exact (pointsToMatrixAdeles_apply D i f hO (g x) (fullPlace D w)).trans
      (hg x (fullPlace D w))
  · apply hf w.val
    rw [hg, ← pointsToMatrixAdeles_apply D i f hO x w]
  · apply hf w.val
    change f w.val (g (x * y) w) = f w.val (g x w * g y w)
    rw [map_mul, hg, hg, hg]
    exact map_mul (matrixAt D w.val) x.val y.val

end MatrixAdeles

section CompactQuotient

open Specs.AnisotropicTensorQuotients
open private MatrixAdeles matrixAt adelicMatrixGroup from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AnisotropicTensorQuotients

private theorem compactQuotientOfSurjective {P Q : Type*} [Group P] [Group Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    (A : Subgroup P) (B : Subgroup Q) (f : P →* Q)
    (hf : Continuous f) (hs : Function.Surjective f) (hAB : A ≤ B.comap f)
    (hc : CompactSpace (P ⧸ A)) : CompactSpace (Q ⧸ B) := by
  let q : P ⧸ A → Q ⧸ B := Quotient.map' f (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    rw [← map_inv, ← map_mul]
    exact hAB hxy)
  have hq : Continuous q := continuous_quot_map _ hf
  have hsurj : Function.Surjective q := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨QuotientGroup.mk z, rfl⟩
  letI := hc
  exact ⟨by simpa only [Set.image_univ, hsurj.range_eq] using isCompact_univ.image hq⟩

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K} {n : ℕ}

private theorem compactQuotientOfMatrixModel
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (e : Index.{u} i.size ≃ Fin n) (M : MatrixModel K (Fin n))
    (hR : ∀ (R : Type u) [Field R] (a : K →+* R),
      letI : Algebra K R := a.toAlgebra
      ((reindexMatrix e).comp (asMatrix i R)).range = M R a)
    (hQ : GlobalMatrixQuotientCompact D M) :
    CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) := by
  let f (w : D.Place) := (reindexMatrix e).comp (asMatrix i (D.Completion w))
  have hf (w : D.Place) : Function.Injective (f w) := by
    intro x y h
    apply (localMatrixEmbedding D i w).injective
    exact Function.LeftInverse.injective (reindexMatrix_symm e) h
  have hr (w : D.Place) : (f w).range = M (D.Completion w) (D.embedding w) :=
    hR (D.Completion w) (D.embedding w)
  have ht (w : D.Place) : IsInducing (f w) := by
    have h1 : Continuous (f w) := (continuous_reindexMatrix e).comp continuous_induced_dom
    have h2 : reindexMatrix e.symm ∘ f w = asMatrix i (D.Completion w) := by
      funext x
      exact reindexMatrix_symm e _
    apply IsInducing.of_comp h1 (continuous_reindexMatrix e.symm)
    rw [h2]
    exact ⟨rfl⟩
  have hO (w : D.FinitePlace) (x : LocalPoints D i (.inl w)) :
      f (.inl w) x ∈ finiteMatrixSubgroup D w ↔ x ∈ localSubgroup D i (.inl w) :=
    reindexMatrix_integral e _ _
  obtain ⟨δ, hδ, _, hc⟩ := globalMatrixCompactQuotient D M hQ
  let E := adelicMatrixEquiv D i M f hf hr ht hO
  let N := adelicMatrixGroup D M
  let B := ((M K (RingHom.id K)).map δ).subgroupOf N
  let q : RationalPoints G →* GL (Fin n) K := (reindexMatrix e).comp i.onPoints
  have hq : q.range = M K (RingHom.id K) := hR K (RingHom.id K)
  have hnat (w : D.Place) (g : RationalPoints G) :
      f w (localPoint D i w g) = GeneralLinearGroup.map (D.embedding w) (q g) := by
    change reindexMatrix e (asMatrix i (D.Completion w) (localPoint D i w g)) = _
    rw [localPoint_matrix, reindexMatrix_natural]
    rfl
  have hE (a : N) (w : FullPlace D) :
      f w.val (E a w) = matrixAt D w.val a.val :=
    matrixAdelesToPoints_apply D i M f hf hr hO a w
  have hdiag : B = (diagonalSubgroup D i).comap E.toMonoidHom := by
    ext a
    constructor
    · rintro ⟨r, hr, hδr⟩
      have hqr : r ∈ q.range := hq.symm ▸ hr
      obtain ⟨g, rfl⟩ := hqr
      refine ⟨g, fun w => hf w.val ?_⟩
      change f w.val (E a w) = f w.val (localPoint D i w.val g)
      calc
        _ = matrixAt D w.val a.val := hE a w
        _ = matrixAt D w.val (δ (q g)) := congrArg (matrixAt D w.val) hδr.symm
        _ = _ := (hδ (q g) w.val).trans (hnat w.val g).symm
    · rintro ⟨g, hg⟩
      refine ⟨q g, hq ▸ (show q g ∈ q.range from ⟨g, rfl⟩), fullMatrix_ext D fun w => ?_⟩
      calc
        _ = f w (localPoint D i w g) := (hδ (q g) w).trans (hnat w g).symm
        _ = f w (E a (fullPlace D w)) := congrArg (f w) (hg (fullPlace D w)).symm
        _ = _ := hE a (fullPlace D w)
  exact compactQuotientOfSurjective B (diagonalSubgroup D i) E.toMonoidHom
    E.continuous E.surjective hdiag.le hc

theorem compactQuotient : Specs.DivisionNormOneAdelicCompactness.CompactQuotient.{u,v} := by
  classical
  intro K A _ D _ _ hA I _ b G h i
  let n := Fintype.card I
  let c : Module.Basis (Index.{u} n) K A :=
    b.reindex ((Fintype.equivFin I).trans Equiv.ulift.symm)
  have hc : RepresentsNormOne hA c G := representsNormOne_changeBasis hA b c h
  obtain ⟨j, e, hj⟩ := existsRegularRealization hA c hc
  let d : Module.Basis (Fin n) K A := c.reindex Equiv.ulift
  let E := e.trans (Equiv.ulift : Index.{u} n ≃ Fin n)
  have hrange (R : Type u) [Field R] (a : K →+* R) :
      letI : Algebra K R := a.toAlgebra
      ((reindexMatrix E).comp (asMatrix j R)).range = divisionMatrixModel hA d R a := by
    letI : Algebra K R := a.toAlgebra
    let p := ((normOnePointsIso hA c hc).app (CommAlgCat.of K R)).groupIsoToMulEquiv
    have he (x : PointsIn j R) :
        reindexMatrix E (asMatrix j R x) =
          reindexMatrix Equiv.ulift (regularMatrix hA c (p x)) := by
      rw [reindexMatrix_trans, hj]
      rfl
    change _ = (divisionNormOneMatrixHom (L := R) hA d).range
    rw [← regularMatrix_field, ← regularMatrix_range_reindex hA c Equiv.ulift]
    ext y
    show (∃ x : PointsIn j R, reindexMatrix E (asMatrix j R x) = y) ↔
      (∃ x : normOne (R := R) hA c, reindexMatrix Equiv.ulift (regularMatrix hA c x) = y)
    simp_rw [he]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨p x, hx⟩
    · rintro ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := p.surjective x
      exact ⟨y, hx⟩
  have hJ : CompactSpace (Adeles D j ∅ ⧸ diagonalSubgroup D j) :=
    compactQuotientOfMatrixModel D j E _ hrange (AnisotropicTensorQuotients.divisionCompactness D hA d)
  let F := AdelicGroups.changeRealization D j i ∅
  have hF : diagonalSubgroup D j = (diagonalSubgroup D i).comap F.toMonoidHom := by
    ext x
    constructor <;> rintro ⟨g, hg⟩ <;> exact ⟨g, fun w => hg w⟩
  exact compactQuotientOfSurjective (diagonalSubgroup D j) (diagonalSubgroup D i)
    F.toMonoidHom F.continuous F.surjective hF.le hJ

end CompactQuotient

end LinearAlgebraicGroups.Arithmetic.DivisionNormOneAdelicCompactness
