import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.TorsorSpecialization
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.FiniteTypeResiduesAndPoints
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.MatrixGroupCoordinates
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTensor
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorTensor
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTorsor
namespace GaloisFormalization.PV

open scoped TensorProduct
open Matrix (GeneralLinearGroup)
open MatrixGroupCoordinates (CoordinatePolynomial CoordinateRing coordinateMap evalAt
  evalCoordinate inverseDeterminant vanishingIdeal evalAt_entry evalAt_inverseDeterminant
  evalCoordinate_mk coordinateMap_surjective coordinate_ext mem_vanishingIdeal)
open Algebra.TensorProduct (includeLeftRingHom includeRight cancelBaseChange)

universe u v w

noncomputable section

private theorem inverseDeterminant_map {A B : Type*} [CommRing A] [CommRing B] {n : ℕ}
    (f : A →+* B) (X : GeneralLinearGroup (Fin n) A) :
    inverseDeterminant (GeneralLinearGroup.map f X) = f (inverseDeterminant X) := by
  unfold MatrixGroupCoordinates.inverseDeterminant MatrixGroupCoordinates.Specs.inverseDeterminant
  rw [GeneralLinearGroup.map_det, ← map_inv]
  rfl

private theorem evalAt_map {C A B : Type*} [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] {n : ℕ}
    (f : A →ₐ[C] B) (X : GeneralLinearGroup (Fin n) A) :
    evalAt (C := C) (GeneralLinearGroup.map f.toRingHom X) = f.comp (evalAt (C := C) X) := by
  apply MvPolynomial.algHom_ext
  rintro (⟨i, j⟩ | t)
  · simp only [AlgHom.comp_apply, evalAt_entry, GeneralLinearGroup.map_apply]
    rfl
  · cases t
    simp only [AlgHom.comp_apply, evalAt_inverseDeterminant, inverseDeterminant_map]
    rfl

private def rightMultiplyPolynomial {C : Type*} [Field C] {n : ℕ}
    (g : GeneralLinearGroup (Fin n) C) : CoordinatePolynomial C n →ₐ[C] CoordinatePolynomial C n :=
  MvPolynomial.aeval (Sum.elim
    (fun ij => ∑ k : Fin n, MvPolynomial.X (Sum.inl (ij.1, k)) * MvPolynomial.C (g k ij.2))
    (fun _ => MvPolynomial.X (Sum.inr ()) * MvPolynomial.C (inverseDeterminant g)))

private theorem evalAt_rightMultiplyPolynomial {C A : Type*} [Field C] [CommRing A]
    [Algebra C A] {n : ℕ} (X : GeneralLinearGroup (Fin n) A)
    (g : GeneralLinearGroup (Fin n) C) (p : CoordinatePolynomial C n) :
    evalAt (C := C) X (rightMultiplyPolynomial g p) =
      evalAt (C := C) (X * GeneralLinearGroup.map (algebraMap C A) g) p := by
  suffices (evalAt (C := C) X).comp (rightMultiplyPolynomial g) =
      evalAt (C := C) (X * GeneralLinearGroup.map (algebraMap C A) g) from DFunLike.congr_fun this p
  apply MvPolynomial.algHom_ext
  rintro (⟨i, j⟩ | t)
  · simp only [AlgHom.comp_apply, rightMultiplyPolynomial, MvPolynomial.aeval_X, Sum.elim_inl,
      map_sum, map_mul, evalAt_entry, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, GeneralLinearGroup.map_apply]
  · cases t
    simp only [AlgHom.comp_apply, rightMultiplyPolynomial, MvPolynomial.aeval_X, Sum.elim_inr,
      map_mul, evalAt_inverseDeterminant, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    rw [← inverseDeterminant_map]
    unfold MatrixGroupCoordinates.inverseDeterminant MatrixGroupCoordinates.Specs.inverseDeterminant
    simp only [map_mul, mul_inv_rev, Units.val_mul]
    exact mul_comm _ _

section Translation

variable {C : Type*} [Field C] {n : ℕ} (G : Subgroup (GeneralLinearGroup (Fin n) C))

local notation "S" => (G : Set (GeneralLinearGroup (Fin n) C))
local notation "B" => CoordinateRing S

private theorem evalAt_rightMultiplyPolynomial_field (x g : GeneralLinearGroup (Fin n) C)
    (p : CoordinatePolynomial C n) :
    evalAt (C := C) x (rightMultiplyPolynomial g p) = evalAt (C := C) (x * g) p := by
  have h : GeneralLinearGroup.map (algebraMap C C) g = g := by
    simp [Algebra.algebraMap_self]
  rw [evalAt_rightMultiplyPolynomial, h]

private def rightTranslationHom (g : G) : B →ₐ[C] B :=
  Ideal.Quotient.liftₐ (vanishingIdeal S)
    ((coordinateMap S).comp (rightMultiplyPolynomial g.val)) fun p hp => by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply (mem_vanishingIdeal S _).mpr
      intro x
      exact (evalAt_rightMultiplyPolynomial_field x.val g.val p).trans
        ((mem_vanishingIdeal S p).mp hp (x * g))

private theorem rightTranslationHom_mk (g : G) (p : CoordinatePolynomial C n) :
    rightTranslationHom G g (coordinateMap S p) = coordinateMap S (rightMultiplyPolynomial g.val p) :=
  rfl

private theorem eval_rightTranslationHom (g x : G) (b : B) :
    evalCoordinate x (rightTranslationHom G g b) = evalCoordinate (x * g) b := by
  obtain ⟨p, rfl⟩ := coordinateMap_surjective S b
  rw [rightTranslationHom_mk, evalCoordinate_mk, evalCoordinate_mk]
  exact evalAt_rightMultiplyPolynomial_field x.val g.val p

private def rightTranslations : G →* (B ≃ₐ[C] B) where
  toFun g := AlgEquiv.ofAlgHom (rightTranslationHom G g) (rightTranslationHom G g⁻¹)
    (AlgHom.ext fun b => coordinate_ext S _ _ fun x => by
      simp [eval_rightTranslationHom, mul_assoc])
    (AlgHom.ext fun b => coordinate_ext S _ _ fun x => by
      simp [eval_rightTranslationHom, mul_assoc])
  map_one' := AlgEquiv.ext fun b => coordinate_ext S _ _ fun x => by
    change evalCoordinate x (rightTranslationHom G 1 b) = evalCoordinate x b
    rw [eval_rightTranslationHom, mul_one]
  map_mul' g h := AlgEquiv.ext fun b => coordinate_ext S _ _ fun x => by
    change evalCoordinate x (rightTranslationHom G (g * h) b) =
      evalCoordinate x (rightTranslationHom G g (rightTranslationHom G h b))
    simp [eval_rightTranslationHom, mul_assoc]

end Translation

section BaseChange

variable {C K R L B : Type*} [CommRing C] [CommRing K] [CommRing R] [CommRing L]
  [CommRing B] [Algebra C K] [Algebra C R] [Algebra C L] [Algebra C B]
  [Algebra K R] [Algebra K L]

/-- Base change of the first tensor factor along an algebra homomorphism. -/
private theorem specializeTensorEquiv (hCR : IsScalarTower C K R) (hCL : IsScalarTower C K L)
    (point : R →ₐ[K] L)
    (f : R ⊗[C] B ≃ₐ[R] R ⊗[K] R) :
    ∃ e : L ⊗[C] B ≃ₐ[L] L ⊗[K] R, ∀ b : B,
      e (1 ⊗ₜ[C] b) =
        Algebra.TensorProduct.map point (AlgHom.id K R) (f (1 ⊗ₜ[C] b)) := by
  let := hCR
  let := hCL
  let : Algebra R L := point.toRingHom.toAlgebra
  let : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq' point.comp_algebraMap.symm
  let : IsScalarTower C R L := IsScalarTower.of_algebraMap_eq'
    (point.restrictScalars C).comp_algebraMap.symm
  let e := (cancelBaseChange C R L L B).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) f).trans
      (cancelBaseChange K R L L R))
  refine ⟨e, fun b => ?_⟩
  change cancelBaseChange K R L L R
      (1 ⊗ₜ[R] f (1 ⊗ₜ[C] b)) =
    Algebra.TensorProduct.map point (AlgHom.id K R) (f (1 ⊗ₜ[C] b))
  generalize f (1 ⊗ₜ[C] b) = t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]

end BaseChange

open private constantsIn from MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotTorsor

set_option maxHeartbeats 750000 in
/-- Specializing the first factor sends the torsor ratio to the point-normalized
fundamental matrix and transports the action to right translation. -/
theorem torsorSpecialization_conditional
    (_change : Specs.galoisChangeFundamentalMatrix.{u, v})
    (hCoordinate : Specs.galoisCoordinateAlgebra.{u, v})
    (_evaluate : Specs.galoisEvaluation.{u, v})
    (hAction : Specs.galoisRingAction.{u, v})
    (_total : Specs.galoisTotalRingAction.{u, v}) :
    Specs.torsorSpecialization.{u, v, w} := by
  intro kind K _ R _ _ n δ A E Y hk hpv hY L _ _ point
  let C := Specs.constantSubfield δ
  let : Algebra C R := Algebra.compHom R (Specs.constantSubfield δ).subtype
  let : Algebra C L := Algebra.compHom L (Specs.constantSubfield δ).subtype
  have hCKR : IsScalarTower C K R := IsScalarTower.of_algebraMap_eq' rfl
  have hCKL : IsScalarTower C K L := IsScalarTower.of_algebraMap_eq' rfl
  let G := Specs.matrixGaloisGroup δ E Y
  let S : Set (GeneralLinearGroup (Fin n) C) := G
  let B := CoordinateRing S
  let : CommRing B := inferInstanceAs (CommRing (CoordinateRing S))
  let : Algebra C B := inferInstanceAs (Algebra C (CoordinateRing S))
  let V₀ := R ⊗[C] B
  let : CommRing V₀ := Algebra.TensorProduct.instCommRing
  let : Algebra R V₀ := Algebra.TensorProduct.leftAlgebra
  let P := R ⊗[K] R
  let D : Subalgebra C P := Specs.picardVessiotCoordinateAlgebra δ Y
  let V_D := R ⊗[C] D
  let : CommRing V_D := Algebra.TensorProduct.instCommRing
  let : Algebra R V_D := Algebra.TensorProduct.leftAlgebra
  let T := L ⊗[K] R
  let : CommRing T := Algebra.TensorProduct.instCommRing
  let : Algebra C T := Algebra.TensorProduct.leftAlgebra
  let : Algebra L T := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower C L T := IsScalarTower.of_algebraMap_eq' rfl
  let U := GeneralLinearGroup.map point.toRingHom Y
  let left : L →+* T := includeLeftRingHom
  let right : R →ₐ[K] T := includeRight
  let Z := (GeneralLinearGroup.map left U)⁻¹ * GeneralLinearGroup.map right.toRingHom Y
  obtain ⟨_, _, _, eD, heD⟩ := hCoordinate δ A E Y hk hpv hY
  obtain ⟨_, _, _, _, _, _, eRD, _, heRD, _⟩ :=
    picardVessiotTensor δ A E Y (Operator.tensor hpv.1.1 hpv.1.1) hk hpv hY
      (Operator.tensor_laws hpv.1.1 hpv.1.1)
  let tensorIso : V_D ≃ₐ[R] P := eRD.val
  have hTensorIso : tensorIso.toAlgHom = Operator.constantTensorMul D := heRD
  have hTensorIso_tmul (d : D) : tensorIso (1 ⊗ₜ[C] d) = (d : P) := by
    calc
      _ = Operator.constantTensorMul (S := R) D (1 ⊗ₜ[C] d) :=
        DFunLike.congr_fun hTensorIso (1 ⊗ₜ[C] d)
      _ = algebraMap R P (1 : R) * (d : P) := Operator.constantTensorMul_tmul D 1 d
      _ = (d : P) := by rw [map_one, one_mul]
  let base : V₀ ≃ₐ[R] P :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) eD.symm).trans tensorIso
  obtain ⟨e, he⟩ := specializeTensorEquiv (B := B) hCKR hCKL point base
  let q : P →ₐ[K] T := Algebra.TensorProduct.map point (AlgHom.id K R)
  let qC : P →ₐ[C] T :=
    { q.toRingHom with commutes' := fun c => q.commutes (c : K) }
  have hqZ : GeneralLinearGroup.map q.toRingHom (Specs.tensorRatio K Y) = Z := by
    have hleft : q.toRingHom.comp (includeLeftRingHom : R →+* P) =
        left.comp point.toRingHom :=
      Algebra.TensorProduct.map_comp_includeLeftRingHom point (AlgHom.id K R)
    have hright : q.toRingHom.comp (includeRight : R →ₐ[K] P).toRingHom = right.toRingHom := by
      ext r
      change q (1 ⊗ₜ[K] r) = 1 ⊗ₜ[K] r
      change (Algebra.TensorProduct.map point (AlgHom.id K R)) (1 ⊗ₜ[K] r) = _
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    change GeneralLinearGroup.map q.toRingHom
      ((GeneralLinearGroup.map (includeLeftRingHom : R →+* P) Y)⁻¹ *
        GeneralLinearGroup.map (includeRight : R →ₐ[K] P).toRingHom Y) = Z
    rw [map_mul, map_inv]
    change (GeneralLinearGroup.map (q.toRingHom.comp (includeLeftRingHom : R →+* P)) Y)⁻¹ *
      GeneralLinearGroup.map (q.toRingHom.comp (includeRight : R →ₐ[K] P).toRingHom) Y = Z
    rw [hleft, hright]
    rfl
  have hcoords (p : CoordinatePolynomial C n) :
      e (1 ⊗ₜ[C] coordinateMap S p) = evalAt (C := C) Z p := by
    refine (he _).trans ?_
    change q (tensorIso (1 ⊗ₜ[C] eD.symm (coordinateMap S p))) = _
    calc
      _ = q (eD.symm (coordinateMap S p) : P) :=
        congrArg (fun x : P => q x) (hTensorIso_tmul _)
      _ = q (evalAt (C := C) (Specs.tensorRatio K Y) p) :=
        congrArg (fun x : P => q x) (heD p)
      _ = evalAt (C := C) (GeneralLinearGroup.map q.toRingHom (Specs.tensorRatio K Y)) p :=
        (DFunLike.congr_fun (evalAt_map qC (Specs.tensorRatio K Y)) p).symm
      _ = _ := congrArg (fun X => evalAt (C := C) X p) hqZ
  obtain ⟨isoG, hisoG, hmatrix⟩ := hAction δ A E Y hk hpv hY
  let action (g : G) : T →ₐ[L] T :=
    Algebra.TensorProduct.map (AlgHom.id L L) (Specs.matrixAutomorphism δ E Y g).val.toAlgHom
  have hconstant : right.toRingHom.comp (constantsIn δ (R := R)) = algebraMap C T := by
    ext c
    exact right.commutes (c : K)
  have hratio (g : G) :
      GeneralLinearGroup.map (action g).toRingHom Z =
        Z * GeneralLinearGroup.map (algebraMap C T) g.val := by
    let τ := (Specs.matrixAutomorphism δ E Y g).val
    have hτ : GeneralLinearGroup.map τ.toRingHom Y =
        Y * GeneralLinearGroup.map (constantsIn δ) g.val :=
      (hmatrix g (Specs.matrixAutomorphism δ E Y g)).mp (hisoG g)
    have hl : (action g).toRingHom.comp left = left := by
      ext a
      change action g (a ⊗ₜ[K] 1) = a ⊗ₜ[K] 1
      change (Algebra.TensorProduct.map (AlgHom.id L L)
        (Specs.matrixAutomorphism δ E Y g).val.toAlgHom) (a ⊗ₜ[K] 1) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    have hr : (action g).toRingHom.comp right.toRingHom = right.toRingHom.comp τ.toRingHom := by
      ext r
      change (Algebra.TensorProduct.map (AlgHom.id L L) τ.toAlgHom) (1 ⊗ₜ[K] r) =
        1 ⊗ₜ[K] τ r
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rfl
    change GeneralLinearGroup.map (action g).toRingHom
      ((GeneralLinearGroup.map left U)⁻¹ * GeneralLinearGroup.map right.toRingHom Y) = _
    rw [map_mul, map_inv]
    change (GeneralLinearGroup.map ((action g).toRingHom.comp left) U)⁻¹ *
      GeneralLinearGroup.map ((action g).toRingHom.comp right.toRingHom) Y = _
    rw [hl, hr]
    change (GeneralLinearGroup.map left U)⁻¹ *
      GeneralLinearGroup.map right.toRingHom (GeneralLinearGroup.map τ.toRingHom Y) = _
    rw [hτ, map_mul]
    change (GeneralLinearGroup.map left U)⁻¹ *
      (GeneralLinearGroup.map right.toRingHom Y *
        GeneralLinearGroup.map (right.toRingHom.comp (constantsIn δ)) g.val) = _
    rw [hconstant, ← mul_assoc]
  refine ⟨e, rightTranslations G, hcoords, eval_rightTranslationHom G, ?_⟩
  intro g a b
  have hEq : e.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id L L)
      (rightTranslationHom G g)) = (action g).comp e.toAlgHom := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · ext b
      obtain ⟨p, hp⟩ := coordinateMap_surjective S b
      subst b
      change e (1 ⊗ₜ[C] rightTranslationHom G g (coordinateMap S p)) =
        action g (e (1 ⊗ₜ[C] coordinateMap S p))
      rw [rightTranslationHom_mk, hcoords, hcoords, evalAt_rightMultiplyPolynomial, ← hratio]
      exact DFunLike.congr_fun (evalAt_map ((action g).restrictScalars C) Z) p
  exact DFunLike.congr_fun hEq (a ⊗ₜ[C] b)

open private finiteType_of_matrixGenerated from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotTensor

/-- A finite separable residue point and its induced point over a finite Galois extension. -/
theorem torsorSpecializationAtResidue_conditional
    (hChange : Specs.galoisChangeFundamentalMatrix.{u, v})
    (hCoordinate : Specs.galoisCoordinateAlgebra.{u, v})
    (hEvaluate : Specs.galoisEvaluation.{u, v})
    (hAction : Specs.galoisRingAction.{u, v})
    (hTotal : Specs.galoisTotalRingAction.{u, v}) :
    Specs.torsorSpecializationAtResidue.{u, v} := by
  intro kind K _ R _ _ n δ A E Y hk hpv hY
  let : CharZero K := hk.1
  let : Nontrivial R := hpv.2.1.1
  obtain ⟨Y₀, _, hgen⟩ := hpv.2.2
  let : Algebra.FiniteType K R := finiteType_of_matrixGenerated Y₀ hgen
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let : m.IsMaximal := hm
  let F := R ⧸ m
  let : Field F := Ideal.Quotient.field m
  let : Module.Finite K F := maximalQuotientFinite K R m hm
  let i : F →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let : Algebra F (AlgebraicClosure K) := i.toRingHom.toAlgebra
  let : IsScalarTower K F (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  let L := IntermediateField.normalClosure K F (AlgebraicClosure K)
  let j : F →ₐ[K] L :=
    (normalClosure.algHomEquiv K F (AlgebraicClosure K)).symm i
  refine ⟨m, hm, inferInstance, inferInstance, ?_, L, inferInstance, inferInstance,
    inferInstance, inferInstance, j, ?_⟩
  · exact torsorSpecialization_conditional.{u, v, v} hChange hCoordinate hEvaluate hAction hTotal
      δ A E Y hk hpv hY (Ideal.Quotient.mkₐ K m)
  · exact torsorSpecialization_conditional.{u, v, u} hChange hCoordinate hEvaluate hAction hTotal
      δ A E Y hk hpv hY (j.comp (Ideal.Quotient.mkₐ K m))

end

end GaloisFormalization.PV

universe v8_closure_c8a78202a44b377a_u0 v8_closure_c8a78202a44b377a_u1 v8_closure_c8a78202a44b377a_u2
theorem _root_.«GaloisFormalization».«PV».«torsorSpecialization» : _root_.«GaloisFormalization».«PV».«Specs».«torsorSpecialization».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1, v8_closure_c8a78202a44b377a_u2} :=
  @_root_.«GaloisFormalization».«PV».«torsorSpecialization_conditional».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1, v8_closure_c8a78202a44b377a_u2} (@_root_.«GaloisFormalization».«PV».«galoisChangeFundamentalMatrix».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1}) (@_root_.«GaloisFormalization».«PV».«galoisCoordinateAlgebra».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1}) (@_root_.«GaloisFormalization».«PV».«galoisEvaluation».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1}) (@_root_.«GaloisFormalization».«PV».«galoisRingAction».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1}) (@_root_.«GaloisFormalization».«PV».«galoisTotalRingAction».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1})
theorem _root_.«GaloisFormalization».«PV».«torsorSpecializationAtResidue» : _root_.«GaloisFormalization».«PV».«Specs».«torsorSpecializationAtResidue».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1} :=
  @_root_.«GaloisFormalization».«PV».«torsorSpecializationAtResidue_conditional».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1} (@_root_.«GaloisFormalization».«PV».«galoisChangeFundamentalMatrix».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1}) (@_root_.«GaloisFormalization».«PV».«galoisCoordinateAlgebra».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1}) (@_root_.«GaloisFormalization».«PV».«galoisEvaluation».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1}) (@_root_.«GaloisFormalization».«PV».«galoisRingAction».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1}) (@_root_.«GaloisFormalization».«PV».«galoisTotalRingAction».{v8_closure_c8a78202a44b377a_u0, v8_closure_c8a78202a44b377a_u1})
