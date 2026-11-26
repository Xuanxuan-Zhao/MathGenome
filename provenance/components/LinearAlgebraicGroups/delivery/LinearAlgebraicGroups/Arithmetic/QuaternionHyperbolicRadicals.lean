import Specs.LinearAlgebraicGroups.Arithmetic.QuaternionHyperbolicRadicals
import LinearAlgebraicGroups.Arithmetic.CharacteristicTwoQuadraticPairs
import LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
import LinearAlgebraicGroups.Classification.CentralIsogenies
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.NoncommRing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix MulOpposite ValuativeRel
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct Matrix CategoryTheory.MonObj
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)

universe u v w a

namespace LinearAlgebraicGroups.Arithmetic.QuaternionHyperbolicRadicals

open LinearAlgebraicGroups.Specs
open Specs.Arithmetic.QuaternionHyperbolicRadicals
open Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair SpinModel symmetricPart IsPairIsometry)
open Specs.Arithmetic.QuaternionSpinScaleCover
open Specs.Arithmetic.CharacteristicTwoQuadraticPairs
open Specs.SymplecticDivisionForms
open Specs.SymplecticInvolutionModels (HermitianPairing quaternionConjugate)
open Specs.CharacterDescent (Cocharacter)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open LinearAlgebraicGroups.CocharacterDynamics

set_option linter.unusedSectionVars false

open private descendAffine from LinearAlgebraicGroups.Classification.CentralIsogenies
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private opposite_point unitPoint_inv evalLaurent orbit_eval from
  LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

open private antiValue_sum antiValue_add antiValue_mul antiValue_zero antiValue_one
  hermitianValue_laws hermitianValue_nondegenerate hermitianValue_single
  matrix_pairing_reversal hermitian_isometry extendEquiv matrixBaseChange
  extendEquiv_tmul matrixBaseChange_tmul
  from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

noncomputable section

variable {F K I B : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ}

include F in
private theorem two_zero : (2 : B) = 0 := by
  rw [← map_ofNat (algebraMap F B), CharP.ofNat_eq_zero F 2, map_zero]

include F in
private theorem neg_one_eq_one : (-1 : B) = 1 := by
  apply neg_eq_iff_add_eq_zero.mpr
  rw [one_add_one_eq_two, two_zero (F := F)]

private def adjointTranspose {J L : Type*} (s : AntiEquiv F B) (X : Matrix J L B) :
    Matrix L J B := Matrix.of fun i j => antiValue s (X j i)

private theorem adjointTranspose_mul {J L N : Type*} [Fintype L] (s : AntiEquiv F B)
    (X : Matrix J L B) (Y : Matrix L N B) :
    adjointTranspose s (X * Y) = adjointTranspose s Y * adjointTranspose s X := by
  ext i j
  simp [adjointTranspose, Matrix.mul_apply, antiValue_sum, antiValue_mul]

private theorem dagger_mul {J : Type*} [Fintype J] (s : AntiEquiv F B)
    (X Y : Matrix J J B) :
    dagger s (X * Y) = dagger s Y * dagger s X :=
  adjointTranspose_mul s X Y

private theorem dagger_dagger {J : Type*} (s : Involution F B) (X : Matrix J J B) :
    dagger s.anti (dagger s.anti X) = X := by
  ext i j
  exact s.square _

private def planeGram : (Matrix (Fin 2) (Fin 2) B)ˣ where
  val := !![0, 1; -1, 0]
  inv := !![0, -1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def gramUnit (H : (Matrix (Fin d) (Fin d) B)ˣ) :
    (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)ˣ where
  val := quaternionHyperbolicGram H.val
  inv := Matrix.fromBlocks (planeGram (B := B)).inv 0 0 H.inv
  val_inv := by
    change Matrix.fromBlocks (planeGram (B := B)).val 0 0 H.val * _ = _
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  inv_val := by
    change _ * Matrix.fromBlocks (planeGram (B := B)).val 0 0 H.val = _
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]

private theorem conjugation_square (Q : QuaternionHyperbolicPresentation D hB d) :
    dagger Q.conjugation.anti (quaternionHyperbolicGram Q.complement.val) =
      quaternionHyperbolicGram Q.complement.val := by
  let H := gramUnit Q.complement
  let s := Q.conjugation.anti
  let J := QuaternionPairIndex d
  let σ := fun X : Matrix J J B =>
    Q.matrixModel (D.involution.toLinearMap (Q.matrixModel.symm X))
  have hσ (X : Matrix J J B) : H.val * σ X = dagger s X * H.val := by
    dsimp [σ, H, gramUnit]
    simpa using Q.adjoint (Q.matrixModel.symm X)
  have hinv (X : Matrix J J B) : σ (σ X) = X := by
    dsimp only [σ]
    rw [AlgEquiv.symm_apply_apply]
    exact (congrArg Q.matrixModel (D.involution.involutive _)).trans
      (Q.matrixModel.apply_symm_apply X)
  have hcomm (X : Matrix J J B) : Commute (dagger s H.val * H.inv) X := by
    have h₁ := hσ (dagger s X)
    have h₂ := hσ (σ (dagger s X))
    rw [hinv] at h₂
    rw [dagger_dagger Q.conjugation X] at h₁
    have h₃ := congrArg (dagger s) h₂
    change dagger s (H.val * dagger s X) =
      dagger s (dagger s (σ (dagger s X)) * H.val) at h₃
    rw [dagger_mul, dagger_mul, dagger_dagger Q.conjugation X,
      dagger_dagger Q.conjugation (σ (dagger s X))] at h₃
    have hc := congrArg (fun Y => H.inv * Y) h₁
    change H.inv * (H.val * σ (dagger s X)) = H.inv * (X * H.val) at hc
    have h₄ : σ (dagger s X) = H.inv * (X * H.val) := by
      rw [← mul_assoc, H.inv_val, one_mul] at hc
      exact hc
    rw [h₄] at h₃
    have h := congrArg (fun Y => Y * H.inv) h₃
    change (dagger s H.val * H.inv) * X = X * (dagger s H.val * H.inv)
    simpa only [mul_assoc, H.val_inv, mul_one] using h.symm
  obtain ⟨b, hb⟩ := Matrix.mem_range_scalar_iff_commute_single'.2
    (fun i j => (hcomm (Matrix.single i j 1)).symm)
  have hval : dagger s H.val = Matrix.scalar J b * H.val := by
    have h := congrArg (fun Y => Y * H.val) hb
    change Matrix.scalar J b * H.val = (dagger s H.val * H.inv) * H.val at h
    simpa only [mul_assoc, H.inv_val, mul_one] using h.symm
  have hb₁ : b = 1 := by
    have h := congrArg (fun X : Matrix J J B => X (Sum.inl 0) (Sum.inl 1)) hval
    rw [show Matrix.scalar J b = Matrix.diagonal (fun _ => b) from rfl, Matrix.diagonal_mul] at h
    change antiValue s (-1 : B) = b * 1 at h
    rw [neg_one_eq_one (F := F), antiValue_one, mul_one] at h
    exact h.symm
  rw [hb₁, map_one, one_mul] at hval
  exact hval

private def columnMap {J L : Type*} [Fintype L] (A : Matrix J L B) :
    (L → B) →ₗ[Bᵐᵒᵖ] (J → B) where
  toFun x := A *ᵥ x
  map_add' := Matrix.mulVec_add A
  map_smul' a x := by
    ext i
    change ∑ j, A i j * (x j * unop a) = (∑ j, A i j * x j) * unop a
    simp [Finset.sum_mul, mul_assoc]

private theorem columnMap_apply {J L : Type*} [Fintype L] (A : Matrix J L B)
    (x : L → B) : columnMap A x = A *ᵥ x := rfl


private theorem class_eq_of_sub_mem {a b : B} (h : a - b ∈ Set.range (algebraMap F B)) :
    scalarClass F a = scalarClass F b := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact Submodule.Quotient.mk_eq_zero _ |>.2 h

private theorem hermitian_trace_one {J : Type*} [Fintype J]
    (s : AntiEquiv F B) (H L : Matrix J J B) (he : dagger s L * H + H * L = H)
    (x y : J → B) :
    hermitianValue s H (L *ᵥ x) y + hermitianValue s H x (L *ᵥ y) =
      hermitianValue s H x y := by
  unfold hermitianValue
  rw [matrix_pairing_reversal, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← dotProduct_add, ← Matrix.add_mulVec, he]

private theorem gram_complement (s : AntiEquiv F B)
    (H : Matrix (Fin d) (Fin d) B) (x : Fin d → B) (y : QuaternionPairIndex d → B) :
    hermitianValue s (quaternionHyperbolicGram H) (column 0 x 0) y =
    hermitianValue s H x (y ∘ Sum.inr) := by
  have hy : y = Sum.elim (y ∘ Sum.inl) (y ∘ Sum.inr) := by
    funext j
    cases j <;> rfl
  conv_lhs => rw [hy]
  simp [hermitianValue, quaternionHyperbolicGram, column, fromBlocks_mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_two, Function.comp_def]

private theorem complement_column (L : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)
    (y : Fin d → B) :
    (L *ᵥ column 0 y 0) ∘ Sum.inr = L.toBlocks₂₂ *ᵥ y := by
  funext j
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, column, Matrix.toBlocks₂₂,
    Fin.sum_univ_two, Function.comp_def]

private theorem recover (_hdeg : degree F B = 2) (Q : QuaternionHyperbolicPresentation D hB d) :
    Nonempty (ComplementRefinement Q) := by
  obtain ⟨ell, ellW, ht, hs, hq⟩ := Q.quadratic (CharP.ofNat_eq_zero F 2)
  let H := Q.complement.val
  let s := Q.conjugation.anti
  let L := Q.matrixModel ell
  have hL : dagger s L * quaternionHyperbolicGram H + quaternionHyperbolicGram H * L =
      quaternionHyperbolicGram H := by
    rw [← Q.adjoint ell, ← mul_add, ← map_add, add_comm (D.involution.toLinearMap ell), ht,
      map_one, mul_one]
  have hLW : dagger s L.toBlocks₂₂ * H + H * L.toBlocks₂₂ = H := by
    have h₁ (A : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B) :
        (A * quaternionHyperbolicGram H).toBlocks₂₂ = A.toBlocks₂₂ * H := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
      simp [quaternionHyperbolicGram, Matrix.fromBlocks_multiply]
    have h₂ (A : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B) :
        (quaternionHyperbolicGram H * A).toBlocks₂₂ = H * A.toBlocks₂₂ := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
      simp [quaternionHyperbolicGram, Matrix.fromBlocks_multiply]
    have h := congrArg Matrix.toBlocks₂₂ hL
    change (dagger s L * quaternionHyperbolicGram H).toBlocks₂₂ +
      (quaternionHyperbolicGram H * L).toBlocks₂₂ = H at h
    rw [h₁, h₂] at h
    exact h
  have hH : dagger s H = H := congrArg Matrix.toBlocks₂₂ (conjugation_square Q)
  have laws := hermitianValue_laws s Q.conjugation.square H hH
  have htrace := hermitian_trace_one s H L.toBlocks₂₂ hLW
  let p : HermitianPairing s (Fin d → B) :=
    { value := hermitianValue s H
      add_right := laws.add_right
      smul_right := laws.mul_right
      hermitian := laws.symmetric
      nondegenerate := hermitianValue_nondegenerate s Q.complement
      central_norm := fun x => by
        have hx := htrace x x
        rw [laws.symmetric x (L.toBlocks₂₂ *ᵥ x)] at hx
        change antiValue Q.conjugation.anti _ + _ = _ at hx
        rw [Q.canonical, quaternionConjugate, sub_add_cancel] at hx
        exact ⟨_, hx.symm⟩ }
  refine ⟨{
    pairing := p
    pairingFormula := rfl
    ell := ell
    ellTraceOne := ht
    semitraceFormula := hs
    complementAction := columnMap L.toBlocks₂₂
    complementTraceOne := htrace
    quadraticFormula := ?_ }⟩
  intro x y z
  have hw := class_eq_of_sub_mem (F := F) (hq 0 0 y)
  change scalarClass F (hermitianValue s (quaternionHyperbolicGram H)
    (column 0 y 0) (L *ᵥ column 0 y 0)) =
      scalarClass F (antiValue s 0 * 0 + hermitianValue s H y (ellW *ᵥ y)) at hw
  rw [gram_complement, complement_column, mul_zero, zero_add] at hw
  have h := class_eq_of_sub_mem (F := F) (hq x z y)
  change scalarClass F (hermitianValue s (quaternionHyperbolicGram H)
    (column x y z) (L *ᵥ column x y z)) =
      scalarClass F (antiValue s x * z + hermitianValue s H y (ellW *ᵥ y)) at h
  rw [map_add, ← hw] at h
  exact h

private def columnMatrix {J L : Type*} [DecidableEq L] (f : (L → B) →ₗ[Bᵐᵒᵖ] (J → B)) :
    Matrix J L B :=
  Matrix.of fun i j => f (Pi.single j 1) i

private theorem columnMatrix_apply {J L : Type*} [Fintype L] [DecidableEq L]
    (f : (L → B) →ₗ[Bᵐᵒᵖ] (J → B)) (v : L → B) :
    columnMatrix f *ᵥ v = f v := by
  have hv : (∑ j : L, op (v j) • (Pi.single j 1 : L → B)) = v := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · change (Pi.single i 1 : L → B) i * v i = v i
      simp
    · intro j _ hj
      change (Pi.single j 1 : L → B) i * v j = 0
      simp [Ne.symm hj]
    · simp
  conv_rhs => rw [← hv, map_sum]
  ext i
  simp [columnMatrix, Matrix.mulVec, dotProduct, map_smul, Finset.sum_apply]

private theorem matrix_eq_of_mulVec {J L : Type*} [Fintype L] [DecidableEq L]
    {A C : Matrix J L B} (h : ∀ x, A *ᵥ x = C *ᵥ x) : A = C := by
  ext i j
  simpa using congrFun (h (Pi.single j 1)) i

private def basisTransfer {J L : Type a} [Fintype J] [DecidableEq J]
    [Fintype L] [DecidableEq L] (b : (J → B) ≃ₗ[Bᵐᵒᵖ] (L → B)) :
    Matrix L L B ≃ₐ[F] Matrix J J B where
  toFun A := columnMatrix b.symm.toLinearMap * A * columnMatrix b.toLinearMap
  invFun A := columnMatrix b.toLinearMap * A * columnMatrix b.symm.toLinearMap
  left_inv A := by
    apply matrix_eq_of_mulVec
    intro x
    simp only [← mulVec_mulVec, columnMatrix_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  right_inv A := by
    apply matrix_eq_of_mulVec
    intro x
    simp only [← mulVec_mulVec, columnMatrix_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  map_mul' A C := by
    apply matrix_eq_of_mulVec
    intro x
    simp only [← mulVec_mulVec, columnMatrix_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  map_add' A C := by
    let X := columnMatrix b.symm.toLinearMap
    let Y := columnMatrix b.toLinearMap
    change X * (A + C) * Y = X * A * Y + X * C * Y
    rw [Matrix.mul_add, Matrix.add_mul]
  commutes' a := by
    have hscalar {M : Type a} [Fintype M] [DecidableEq M] (v : M → B) :
        algebraMap F (Matrix M M B) a *ᵥ v = a • v := by
      ext i
      rw [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]
      exact (Algebra.smul_def a (v i)).symm
    have hlin (v : J → B) : b (a • v) = a • b v := by
      have hh (M : Type a) (w : M → B) :
          op (algebraMap F B a) • w = a • w := by
        ext i
        change w i * algebraMap F B a = a • w i
        rw [Algebra.smul_def, Algebra.commutes]
      rw [← hh J, map_smul, hh]
    apply matrix_eq_of_mulVec
    intro x
    change (columnMatrix b.symm.toLinearMap * algebraMap F (Matrix L L B) a *
      columnMatrix b.toLinearMap) *ᵥ x = algebraMap F (Matrix J J B) a *ᵥ x
    simp only [← mulVec_mulVec, columnMatrix_apply, hscalar, LinearEquiv.coe_coe]
    exact b.symm_apply_eq.mpr (hlin x).symm

private theorem basisTransfer_mulVec {J L : Type a} [Fintype J] [DecidableEq J]
    [Fintype L] [DecidableEq L] (b : (J → B) ≃ₗ[Bᵐᵒᵖ] (L → B))
    (A : Matrix L L B) (v : J → B) :
    b (basisTransfer (F := F) b A *ᵥ v) = A *ᵥ b v := by
  change b ((columnMatrix b.symm.toLinearMap * A * columnMatrix b.toLinearMap) *ᵥ v) = _
  simp only [← mulVec_mulVec, columnMatrix_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

private def columnEquivOfUnit {J : Type*} [Fintype J] [DecidableEq J]
    (T : (Matrix J J B)ˣ) : (J → B) ≃ₗ[Bᵐᵒᵖ] (J → B) where
  toLinearMap := columnMap T.val
  invFun v := T.inv *ᵥ v
  left_inv v := by
    change T.inv *ᵥ T.val *ᵥ v = v
    rw [mulVec_mulVec, T.inv_val, one_mulVec]
  right_inv v := by
    change T.val *ᵥ T.inv *ᵥ v = v
    rw [mulVec_mulVec, T.val_inv, one_mulVec]

private def decomposition {n : ℕ} (s : AntiEquiv F B)
    (h : HermitianPairing s (Fin n → B)) (x z : Fin n → B)
    (hs : ∀ v, ∃! a : B × (Fin n → B) × B,
      IsHyperbolicComplement h x z a.2.1 ∧ v = op a.1 • x + a.2.1 + op a.2.2 • z) :
    (B × complementSubmodule h x z × B) ≃ₗ[Bᵐᵒᵖ] (Fin n → B) := by
  let f : (B × complementSubmodule h x z × B) →ₗ[Bᵐᵒᵖ] (Fin n → B) :=
    { toFun := fun a => op a.1 • x + a.2.1.val + op a.2.2 • z
      map_add' := by
        intro a b
        change op (a.1 + b.1) • x + (a.2.1.val + b.2.1.val) + op (a.2.2 + b.2.2) • z =
          (op a.1 • x + a.2.1.val + op a.2.2 • z) + (op b.1 • x + b.2.1.val + op b.2.2 • z)
        change (op a.1 + op b.1) • x + (a.2.1.val + b.2.1.val) + (op a.2.2 + op b.2.2) • z =
          (op a.1 • x + a.2.1.val + op a.2.2 • z) + (op b.1 • x + b.2.1.val + op b.2.2 • z)
        simp only [add_smul]
        abel
      map_smul' := by
        intro a b
        change op (b.1 * unop a) • x + a • b.2.1.val + op (b.2.2 * unop a) • z =
          a • (op b.1 • x + b.2.1.val + op b.2.2 • z)
        simp only [op_mul, op_unop, mul_smul, smul_add, RingHom.id_apply] }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨p, _, hp⟩ := hs (f a)
    have haa := hp (a.1, a.2.1.val, a.2.2) ⟨a.2.1.property, rfl⟩
    have hbb := hp (b.1, b.2.1.val, b.2.2) ⟨b.2.1.property, hab⟩
    have he := haa.trans hbb.symm
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact congrArg (fun v : B × (Fin n → B) × B => v.1) he
    · exact Subtype.ext (congrArg (fun v : B × (Fin n → B) × B => v.2.1) he)
    · exact congrArg (fun v : B × (Fin n → B) × B => v.2.2) he
  · intro v
    obtain ⟨a, ⟨ha, hav⟩, _⟩ := hs v
    exact ⟨(a.1, ⟨a.2.1, ha⟩, a.2.2), hav.symm⟩

private def coordinatesEquiv {s : AntiEquiv F B} {n m : ℕ}
    (h : HermitianPairing s (Fin n → B)) (x z : Fin n → B)
    (W : (Fin m → B) ≃ₗ[Bᵐᵒᵖ] complementSubmodule h x z) :
    (QuaternionPairIndex m → B) ≃ₗ[Bᵐᵒᵖ] (B × complementSubmodule h x z × B) where
  toFun q := (q (Sum.inl 0), W (q ∘ Sum.inr), q (Sum.inl 1))
  invFun q := column q.1 (W.symm q.2.1) q.2.2
  left_inv q := by
    funext i
    rcases i with i | i
    · fin_cases i <;> rfl
    · exact congrFun (W.symm_apply_apply (q ∘ Sum.inr)) i
  right_inv q := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · exact W.apply_symm_apply q.2.1
    · rfl
  map_add' p q := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · exact map_add W (p ∘ Sum.inr) (q ∘ Sum.inr)
    · rfl
  map_smul' a q := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · exact map_smul W a (q ∘ Sum.inr)
    · rfl

private def oppositeLine : Bᵐᵒᵖ ≃ₗ[Bᵐᵒᵖ] B where
  toFun := unop
  invFun := op
  left_inv := op_unop
  right_inv := unop_op
  map_add' := unop_add
  map_smul' a b := by
    change unop (a * b) = unop b * unop a
    rw [unop_mul]

private theorem complement_rank {s : AntiEquiv F B} {n : ℕ}
    (h : HermitianPairing s (Fin n → B)) (x z : Fin n → B)
    (e : (B × complementSubmodule h x z × B) ≃ₗ[Bᵐᵒᵖ] (Fin n → B)) :
    Module.finrank Bᵐᵒᵖ (complementSubmodule h x z) = n - 2 := by
  have hb : Module.finrank Bᵐᵒᵖ B = 1 :=
    oppositeLine.symm.finrank_eq.trans (Module.finrank_self _)
  letI : Module.Finite Bᵐᵒᵖ B := Module.Finite.equiv oppositeLine
  have hv : Module.finrank Bᵐᵒᵖ (Fin n → B) = n := by
    rw [Module.finrank_pi_fintype]
    simp [hb]
  have he := e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_prod, hb, hv] at he
  omega

private theorem adjointTranspose_one {J : Type*} [DecidableEq J] (s : AntiEquiv F B) :
    adjointTranspose s (1 : Matrix J J B) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [adjointTranspose, Matrix.one_apply, h, eq_comm]

private theorem basis_pairing {J L : Type*} [Fintype J] [Fintype L]
    (s : AntiEquiv F B) (H : Matrix L L B) (C : Matrix L J B) (p q : J → B) :
    hermitianValue s (adjointTranspose s C * H * C) p q =
      hermitianValue s H (C *ᵥ p) (C *ᵥ q) := by
  have h : (fun i => antiValue s ((C *ᵥ p) i)) =
      (fun i => antiValue s (p i)) ᵥ* adjointTranspose s C := by
    funext i
    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, adjointTranspose, antiValue_sum, antiValue_mul]
  calc
    _ = (fun i => antiValue s (p i)) ⬝ᵥ adjointTranspose s C *ᵥ H *ᵥ C *ᵥ q := by
      simp [hermitianValue, Matrix.mul_assoc]
    _ = _ := by rw [hermitianValue, h, dotProduct_mulVec]

private def transferredGram {J L : Type*} [Fintype J] [DecidableEq J]
    [Fintype L] [DecidableEq L] (s : AntiEquiv F B) (H : (Matrix L L B)ˣ)
    (b : (J → B) ≃ₗ[Bᵐᵒᵖ] (L → B)) : (Matrix J J B)ˣ := by
  let C := columnMatrix b.toLinearMap
  let K := columnMatrix b.symm.toLinearMap
  have hCK : C * K = 1 := by
    apply matrix_eq_of_mulVec
    intro x
    simp [C, K, ← mulVec_mulVec, columnMatrix_apply]
  have hKC : K * C = 1 := by
    apply matrix_eq_of_mulVec
    intro x
    simp [C, K, ← mulVec_mulVec, columnMatrix_apply]
  have hCtKt : adjointTranspose s C * adjointTranspose s K = 1 := by
    rw [← adjointTranspose_mul, hKC, adjointTranspose_one]
  have hKtCt : adjointTranspose s K * adjointTranspose s C = 1 := by
    rw [← adjointTranspose_mul, hCK, adjointTranspose_one]
  refine ⟨adjointTranspose s C * H.val * C, K * H.inv * adjointTranspose s K, ?_, ?_⟩
  · calc
      _ = adjointTranspose s C * H.val * (C * K) * H.inv * adjointTranspose s K := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCK, Matrix.mul_one, Matrix.mul_assoc (adjointTranspose s C), H.val_inv, Matrix.mul_one, hCtKt]
  · calc
      _ = K * H.inv * (adjointTranspose s K * adjointTranspose s C) * H.val * C := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hKtCt, Matrix.mul_one, Matrix.mul_assoc K, H.inv_val, Matrix.mul_one, hKC]

private theorem transferredGram_pairing {J L : Type*} [Fintype J] [DecidableEq J]
    [Fintype L] [DecidableEq L] (s : AntiEquiv F B) (H : (Matrix L L B)ˣ)
    (b : (J → B) ≃ₗ[Bᵐᵒᵖ] (L → B)) (p q : J → B) :
    hermitianValue s (transferredGram s H b).val p q = hermitianValue s H (b p) (b q) := by
  change hermitianValue s (adjointTranspose s (columnMatrix b.toLinearMap) * H.val *
    columnMatrix b.toLinearMap) p q = _
  rw [basis_pairing, columnMatrix_apply, columnMatrix_apply]
  rfl

private def complementGramUnit (T : (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)ˣ)
    (hT : T.val = quaternionHyperbolicGram T.val.toBlocks₂₂) :
    (Matrix (Fin d) (Fin d) B)ˣ where
  val := T.val.toBlocks₂₂
  inv := T.inv.toBlocks₂₂
  val_inv := by
    have h := congrArg Matrix.toBlocks₂₂ T.val_inv
    rw [hT, ← Matrix.fromBlocks_toBlocks T.inv, quaternionHyperbolicGram,
      Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at h
    simpa only [toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add] using h
  inv_val := by
    have h := congrArg Matrix.toBlocks₂₂ T.inv_val
    rw [hT, ← Matrix.fromBlocks_toBlocks T.inv, quaternionHyperbolicGram,
      Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at h
    simpa only [toBlocks_fromBlocks₂₂, Matrix.mul_zero, zero_add] using h

private theorem transported_adjoint {J L : Type a} [Fintype J] [DecidableEq J]
    [Fintype L] [DecidableEq L] (s : AntiEquiv F B) (H : (Matrix L L B)ˣ)
    (b : (J → B) ≃ₗ[Bᵐᵒᵖ] (L → B))
    (A X : Matrix L L B) (h : H.val * X = dagger s A * H.val) :
    (transferredGram s H b).val * basisTransfer (F := F) b X =
      dagger s (basisTransfer (F := F) b A) * (transferredGram s H b).val := by
  let C := columnMatrix b.toLinearMap
  let K := columnMatrix b.symm.toLinearMap
  have hCK : C * K = 1 := by
    apply matrix_eq_of_mulVec
    intro x
    simp [C, K, ← mulVec_mulVec, columnMatrix_apply]
  have hKtCt : adjointTranspose s K * adjointTranspose s C = 1 := by
    rw [← adjointTranspose_mul, hCK, adjointTranspose_one]
  change (adjointTranspose s C * H.val * C) * (K * X * C) =
    adjointTranspose s (K * A * C) * (adjointTranspose s C * H.val * C)
  rw [adjointTranspose_mul, adjointTranspose_mul]
  calc
    _ = adjointTranspose s C * (H.val * (C * K) * X) * C := by simp only [Matrix.mul_assoc]
    _ = adjointTranspose s C * (dagger s A * H.val) * C := by rw [hCK, Matrix.mul_one, h]
    _ = adjointTranspose s C * adjointTranspose s A *
        (adjointTranspose s K * adjointTranspose s C) * H.val * C := by
      rw [hKtCt, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
      rfl
    _ = _ := by simp only [Matrix.mul_assoc]

private theorem class_zero_difference {x y : B} (h : scalarClass F x = scalarClass F y) :
    x - y ∈ Set.range (algebraMap F B) := by
  have hz : scalarClass F (x - y) = 0 := by rw [map_sub, h, sub_self]
  exact (Submodule.Quotient.mk_eq_zero _).mp hz

private theorem arithmetic (hisotropy : ArithmeticQuaternionIsotropy.{u,u})
    (hrec : QuaternionPairRecovery.{u}) : ArithmeticPresentation.{u} := by
  intro F K I B _ _ _ _ _ _ _ _ _ _ _ _ _ ρ G D M hB hdeg n hn e
  obtain ⟨P⟩ := hrec D hB hdeg n e
  have hfield : IsCharacteristicTwoArithmeticField.{u,u} F :=
    Or.inr ⟨inferInstance, inferInstance, ‹IsNonarchimedeanLocalField F›⟩
  obtain ⟨x, z, hx, hqx, hqz, hxx, hzz, hxz, hzx, hsplit, hquad, _⟩ :=
    hisotropy hfield M hB hdeg n hn e P
  let V := complementSubmodule P.pairing x z
  let E := decomposition P.bar.anti P.pairing x z hsplit
  letI : Module.Finite Bᵐᵒᵖ B := Module.Finite.equiv oppositeLine
  letI : Module.Finite Bᵐᵒᵖ V :=
    Module.Finite.of_injective (complementSubmodule P.pairing x z).subtype Subtype.val_injective
  let W : (Fin (n - 2) → B) ≃ₗ[Bᵐᵒᵖ] V :=
    (LinearEquiv.piCongrRight (fun _ : Fin (n - 2) => (oppositeLine (B := B)).symm)).trans
       (Module.finBasisOfFinrankEq Bᵐᵒᵖ V (complement_rank P.pairing x z E)).equivFun.symm
  let b := (coordinatesEquiv P.pairing x z W).trans E
  let T := transferredGram P.bar.anti P.gram b
  let e' := e.trans (basisTransfer (F := F) b)
  have hpair (p q) : hermitianValue P.bar.anti T.val p q = P.pairing.value (b p) (b q) := by
    rw [transferredGram_pairing, P.pairingFormula]
  have hX : b (Pi.single (Sum.inl 0) 1) = x := by
    change op ((Pi.single (Sum.inl 0) 1 : QuaternionPairIndex (n - 2) → B) (Sum.inl 0)) • x +
      (W ((Pi.single (Sum.inl 0) 1) ∘ Sum.inr)).val +
      op ((Pi.single (Sum.inl 0) 1 : QuaternionPairIndex (n - 2) → B) (Sum.inl 1)) • z = x
    have h0 : (Pi.single (Sum.inl 0) 1 : QuaternionPairIndex (n - 2) → B) ∘ Sum.inr = 0 := by
      funext i
      simp
    simp [h0, Pi.single_apply]
  have hZ : b (Pi.single (Sum.inl 1) 1) = z := by
    change op ((Pi.single (Sum.inl 1) 1 : QuaternionPairIndex (n - 2) → B) (Sum.inl 0)) • x +
      (W ((Pi.single (Sum.inl 1) 1) ∘ Sum.inr)).val +
      op ((Pi.single (Sum.inl 1) 1 : QuaternionPairIndex (n - 2) → B) (Sum.inl 1)) • z = z
    have h0 : (Pi.single (Sum.inl 1) 1 : QuaternionPairIndex (n - 2) → B) ∘ Sum.inr = 0 := by
      funext i
      simp
    simp [h0, Pi.single_apply]
  have hW (i : Fin (n - 2)) :
      IsHyperbolicComplement P.pairing x z (b (Pi.single (Sum.inr i) 1)) := by
    change IsHyperbolicComplement P.pairing x z
      (op ((Pi.single (Sum.inr i) 1 : QuaternionPairIndex (n - 2) → B) (Sum.inl 0)) • x +
        (W ((Pi.single (Sum.inr i) 1 : QuaternionPairIndex (n - 2) → B) ∘ Sum.inr)).val +
        op ((Pi.single (Sum.inr i) 1 : QuaternionPairIndex (n - 2) → B) (Sum.inl 1)) • z)
    let y := (Pi.single (Sum.inr i) 1 : QuaternionPairIndex (n - 2) → B) ∘ Sum.inr
    have hy : IsHyperbolicComplement P.pairing x z (W y).val := (W y).property
    rw [Pi.single_eq_of_ne (by simp : Sum.inl (0 : Fin 2) ≠
        (Sum.inr i : QuaternionPairIndex (n - 2))),
      Pi.single_eq_of_ne (by simp : Sum.inl (1 : Fin 2) ≠
        (Sum.inr i : QuaternionPairIndex (n - 2))),
      MulOpposite.op_zero, zero_smul, zero_smul, zero_add, add_zero]
    exact hy
  have hentry (i j) : T.val i j = P.pairing.value (b (Pi.single i 1)) (b (Pi.single j 1)) := by
    rw [← hermitianValue_single P.bar.anti T.val i j, hpair]
  have hT : T.val = quaternionHyperbolicGram T.val.toBlocks₂₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · fin_cases i <;> fin_cases j <;>
        simp [hentry, hX, hZ, hxx, hzz, hxz, hzx, quaternionHyperbolicGram,
          neg_one_eq_one (F := F)]
    · fin_cases i
      · simpa [hentry, hX, quaternionHyperbolicGram] using (hW j).1
      · simpa [hentry, hZ, quaternionHyperbolicGram] using (hW j).2
    · fin_cases j
      · simp [hentry, hX, quaternionHyperbolicGram, P.pairing.hermitian x, (hW i).1, antiValue_zero]
      · simp [hentry, hZ, quaternionHyperbolicGram, P.pairing.hermitian z, (hW i).2, antiValue_zero]
    · rfl
  let H := complementGramUnit T hT
  have hGram : quaternionHyperbolicGram H.val = T.val := hT.symm
  have he' (a : ρ.fixedSubalgebra) (p) : b (e' a *ᵥ p) = e a *ᵥ b p :=
    basisTransfer_mulVec (F := F) b (e a) p
  have hQ (p) : scalarClass F (hermitianValue P.bar.anti (quaternionHyperbolicGram H.val)
      p (e' P.ell *ᵥ p)) = refinement P.pairing P.ellAction (b p) := by
    rw [hGram, hpair, he', refinement, P.ellActionFormula]
  let Q : QuaternionHyperbolicPresentation D hB (n - 2) :=
    { conjugation := P.bar
      canonical := P.canonical
      complement := H
      matrixModel := e'
      matrixAt := fun R => (extendEquiv (R := R) e').trans (matrixBaseChange _)
      matrixAtFormula := fun R r a => by simp only [AlgEquiv.trans_apply, extendEquiv_tmul, matrixBaseChange_tmul]
      adjoint := fun a => by
        rw [hGram]
        apply transported_adjoint
        change P.gram.val * e (D.involution.toLinearMap a) =
          dagger P.bar.anti (e a) * P.gram.val
        rw [P.adjointFormula, ← mul_assoc, ← mul_assoc, P.gram.val_inv, one_mul]
      quadratic := fun _ => by
        refine ⟨P.ell, (e' P.ell).toBlocks₂₂, P.ellTraceOne, P.semitraceFormula, ?_⟩
        intro a c y
        apply class_zero_difference (F := F)
        change scalarClass F (hermitianValue P.bar.anti (quaternionHyperbolicGram H.val)
          (column a y c) (e' P.ell *ᵥ column a y c)) =
          scalarClass F (antiValue P.bar.anti a * c +
            hermitianValue P.bar.anti H.val y ((e' P.ell).toBlocks₂₂ *ᵥ y))
        have h0 := hQ (column 0 y 0)
        rw [gram_complement, complement_column] at h0
        have hby : IsHyperbolicComplement P.pairing x z (W y).val := (W y).property
        have hcol (a c : B) : b (column a y c) = op a • x + (W y).val + op c • z := rfl
        rw [hQ, hcol, hquad _ _ _ hby, map_add, h0, hcol]
        simp }
  exact ⟨P, x, z, W, hx, hqx, hqz, hxx, hzz, hxz, hzx, Q, rfl, he',
    fun p q => hGram ▸ hpair p q, hQ⟩

private theorem grams_scalar {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {s : AntiEquiv F B} (H T : (Matrix J J B)ˣ)
    (σ : Matrix J J B → Matrix J J B)
    (hH : ∀ X, H.val * σ X = dagger s X * H.val)
    (hT : ∀ X, T.val * σ X = dagger s X * T.val)
    (hcentral : Algebra.IsCentral F B) :
    ∃ t : Fˣ, T.val = t.val • H.val := by
  letI := hcentral
  have hcomm (Y : Matrix J J B) : Commute (T.val * H.inv) Y := by
    let X : Matrix J J B := Matrix.of fun i j => s.symm (op (Y j i))
    have hX : dagger s X = Y := by
      ext i j
      simp [dagger, antiValue, X]
    have h₁ := hH X
    have h₂ := hT X
    rw [hX] at h₁ h₂
    have hh := congrArg (fun Z => H.inv * Z * H.inv) h₁
    change H.inv * (H.val * σ X) * H.inv = H.inv * (Y * H.val) * H.inv at hh
    have h₃ : σ X * H.inv = H.inv * Y := by
      calc
        _ = H.inv * (H.val * σ X) * H.inv := by
          rw [← mul_assoc, H.inv_val, one_mul]
        _ = _ := by rw [hh, mul_assoc H.inv, mul_assoc Y, H.val_inv, mul_one]
    change (T.val * H.inv) * Y = Y * (T.val * H.inv)
    rw [mul_assoc, ← h₃, ← mul_assoc, h₂, mul_assoc]
  obtain ⟨a, ha⟩ := Matrix.mem_range_scalar_iff_commute_single'.2
    (fun i j => (hcomm (Matrix.single i j 1)).symm)
  have hza : a ∈ Subalgebra.center F B := by
    rw [Subalgebra.mem_center_iff]
    intro b
    let i : J := Classical.choice ‹Nonempty J›
    have h := (hcomm (Matrix.scalar J b)).eq
    rw [← ha, ← map_mul, ← map_mul] at h
    simpa [Matrix.scalar_apply] using congrArg (fun A : Matrix J J B => A i i) h.symm
  rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot] at hza
  obtain ⟨t, ht⟩ := hza
  have hval : T.val = Matrix.scalar J a * H.val := by
    rw [ha, mul_assoc, H.inv_val, mul_one]
  have ht0 : t ≠ 0 := by
    intro hz
    have hz' : a = 0 := by rw [← ht, hz, map_zero]
    apply Units.ne_zero T
    rw [hval, hz', map_zero, zero_mul]
  refine ⟨Units.mk0 t ht0, ?_⟩
  rw [hval, ← ht]
  ext i j
  rw [show Matrix.scalar J (algebraMap F B t) = Matrix.diagonal (fun _ => algebraMap F B t) from rfl,
    Matrix.diagonal_mul]
  exact (Algebra.smul_def t (H.val i j)).symm

private theorem hermitian_smul_gram {J : Type*} [Fintype J]
    (s : AntiEquiv F B) (t : F) (H : Matrix J J B) (x y : J → B) :
    hermitianValue s (t • H) x y = t • hermitianValue s H x y := by
  unfold hermitianValue
  rw [Matrix.smul_mulVec, dotProduct_smul]

private theorem rational_preserves_forms
    (hrec : QuaternionPairRecovery.{u}) (hdeg : degree F B = 2)
    (Q : QuaternionHyperbolicPresentation D hB d)
    (W : ComplementRefinement Q) (g : ρ.fixedSubalgebraˣ) :
    let J := QuaternionPairIndex d
    let s := Q.conjugation.anti
    let H := quaternionHyperbolicGram Q.complement.val
    let T := Q.matrixModel g.val
    (D.involution.toLinearMap g.val * g.val = 1 ∧ PreservesSemitrace D g) ↔
    (∀ x y : J → B, hermitianValue s H (T *ᵥ x) (T *ᵥ y) = hermitianValue s H x y) ∧
    (∀ x : J → B, scalarClass F (hermitianValue s H (T *ᵥ x) (Q.matrixModel W.ell *ᵥ (T *ᵥ x))) =
      scalarClass F (hermitianValue s H x (Q.matrixModel W.ell *ᵥ x))) := by
  dsimp only
  let J := QuaternionPairIndex d
  let s := Q.conjugation.anti
  let H := gramUnit Q.complement
  let T := Q.matrixModel g.val
  have hEq : Q.matrixModel (D.involution.toLinearMap g.val) = H.inv * dagger s T * H.val := by
    have h := congrArg (fun X => H.inv * X) (Q.adjoint g.val)
    change H.inv * (H.val * Q.matrixModel (D.involution.toLinearMap g.val)) =
      H.inv * (dagger s T * H.val) at h
    rw [← mul_assoc, H.inv_val, one_mul, ← mul_assoc] at h
    exact h
  have hHermitian : D.involution.toLinearMap g.val * g.val = 1 ↔
      ∀ x y : J → B, hermitianValue s H.val (T *ᵥ x) (T *ᵥ y) = hermitianValue s H.val x y := by
    rw [← (Q.matrixModel.injective.eq_iff), map_mul, hEq, map_one]
    exact hermitian_isometry s H T
  rw [hHermitian]
  apply and_congr_right
  intro hisom
  symm
  let m := Fintype.card J
  let b : (J → B) ≃ₗ[Bᵐᵒᵖ] (Fin m → B) :=
    LinearEquiv.piCongrLeft Bᵐᵒᵖ (fun _ : Fin m => B) (Fintype.equivFin J)
  let e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin m) (Fin m) B :=
    Q.matrixModel.trans (basisTransfer (F := F) b.symm)
  obtain ⟨P⟩ := hrec D hB hdeg m e
  have hs : P.bar.anti = s := by
    ext x
    apply unop_injective
    exact (P.canonical x).trans (Q.canonical x).symm
  have htransfer (a : ρ.fixedSubalgebra) :
      basisTransfer (F := F) b (e a) = Q.matrixModel a := by
    apply matrix_eq_of_mulVec
    intro x
    apply b.injective
    rw [basisTransfer_mulVec]
    change basisTransfer (F := F) b.symm (Q.matrixModel a) *ᵥ b x = _
    apply b.symm.injective
    rw [basisTransfer_mulVec, b.symm_apply_apply, b.symm_apply_apply]
  have hcol (a : ρ.fixedSubalgebra) (x : J → B) :
      b (Q.matrixModel a *ᵥ x) = e a *ᵥ b x := by rw [← htransfer, basisTransfer_mulVec]
  let A := transferredGram s P.gram b
  have hadj (a : ρ.fixedSubalgebra) : A.val * Q.matrixModel (D.involution.toLinearMap a) =
      dagger s (Q.matrixModel a) * A.val := by
    rw [← htransfer (D.involution.toLinearMap a), ← htransfer a]
    apply transported_adjoint
    rw [P.adjointFormula, hs, ← mul_assoc, ← mul_assoc, P.gram.val_inv, one_mul]
  let σ := fun X => Q.matrixModel (D.involution.toLinearMap (Q.matrixModel.symm X))
  have hHσ (X : Matrix J J B) : H.val * σ X = dagger s X * H.val := by
    change quaternionHyperbolicGram Q.complement.val * σ X =
      dagger Q.conjugation.anti X * quaternionHyperbolicGram Q.complement.val
    simpa only [σ, Q.matrixModel.apply_symm_apply] using Q.adjoint (Q.matrixModel.symm X)
  have hAσ (X : Matrix J J B) : A.val * σ X = dagger s X * A.val := by
    simpa only [σ, Q.matrixModel.apply_symm_apply] using hadj (Q.matrixModel.symm X)
  haveI : Nonempty J := ⟨Sum.inl 0⟩
  obtain ⟨t, ht⟩ := grams_scalar H A σ hHσ hAσ hB.2.1
  have hp (x y : J → B) : P.pairing.value (b x) (b y) = t.val • hermitianValue s H.val x y := by
    rw [P.pairingFormula, hs, ← transferredGram_pairing s P.gram b, ← show A.val = _ from rfl, ht,
      hermitian_smul_gram]
  have hPres (x y : Fin m → B) :
      P.pairing.value (e g.val *ᵥ x) (e g.val *ᵥ y) = P.pairing.value x y := by
    obtain ⟨x, rfl⟩ := b.surjective x
    obtain ⟨y, rfl⟩ := b.surjective y
    rw [← hcol, ← hcol, hp, hp, hisom]
  rw [← P.preserves g hPres]
  have hQ (x : J → B) :
      refinement P.pairing P.ellAction (b x) =
        t.val • scalarClass F (hermitianValue s H.val x (Q.matrixModel W.ell *ᵥ x)) := by
    rw [P.refinementIndependent W.ell W.semitraceFormula, ← hcol, hp, map_smul]
  constructor
  · intro h x
    obtain ⟨x, rfl⟩ := b.surjective x
    rw [← hcol, hQ, hQ]
    exact congrArg (fun v : ScalarClasses F B => t.val • v) (h x)
  · intro h x
    have h' := h (b x)
    rw [← hcol, hQ, hQ] at h'
    exact (smul_right_injective _ t.ne_zero) h'

private theorem lift_vector_commutator (M : SpinModel G D)
    (t : (𝟙_ (SchemeOver F)) ⟶ G.val.X) {X : SchemeOver F} (y : X ⟶ M.neutral.val.X) :
    ∃ a : X ⟶ G.val.X, a ≫ M.projection.hom.hom =
      (toUnit X ≫ t ≫ M.projection.hom.hom) * y *
        (toUnit X ≫ t ≫ M.projection.hom.hom)⁻¹ * y⁻¹ := by
  rcases M.centralIsogeny with ⟨_, hflat, hsurj, N, hN, hcentre⟩
  let p := M.projection.hom.hom
  let τ := toUnit G.val.X ≫ t
  let f : G.val.X ⟶ G.val.X := τ * 𝟙 _ * τ⁻¹ * (𝟙 _)⁻¹
  letI : IsAffine G.val.X.left := G.2.1
  letI : IsAffine M.neutral.val.X.left := M.neutral.2.1
  letI : Flat p.left := hflat
  letI : Surjective p.left := hsurj
  have hcomp {Y : SchemeOver F} (a : Y ⟶ G.val.X) :
      a ≫ f = (toUnit Y ≫ t) * a * (toUnit Y ≫ t)⁻¹ * a⁻¹ := by
    simp [f, τ, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
  obtain ⟨d, hd⟩ := descendAffine p f (by
    intro Y a b hab
    have hker : (a⁻¹ * b) ≫ p = toUnit Y ≫ η[M.neutral.val.X] := by
      change (a⁻¹ * b) ≫ M.projection.hom.hom = (1 : Y ⟶ M.neutral.val.X)
      rw [MonObj.mul_comp, GrpObj.inv_comp, hab, inv_mul_cancel]
    let z := hN.lift (a⁻¹ * b) (toUnit Y) hker
    have hz : z ≫ N.inclusion.hom.hom = a⁻¹ * b := hN.lift_fst _ _ _
    have hc := (centralizes_iff _ _).mp hcentre Y z (toUnit Y ≫ t)
    change Commute (z ≫ N.inclusion.hom.hom) (toUnit Y ≫ t) at hc
    rw [hz] at hc
    rw [hcomp a, hcomp b]
    let τ' := toUnit Y ≫ t
    let k := a⁻¹ * b
    change τ' * a * τ'⁻¹ * a⁻¹ = τ' * b * τ'⁻¹ * b⁻¹
    have hb : a * k = b := by simp [k]
    have hcomm : k * τ'⁻¹ = τ'⁻¹ * k := hc.inv_right.eq
    calc
      τ' * a * τ'⁻¹ * a⁻¹ =
          (τ' * a) * (τ'⁻¹ * k * k⁻¹) * a⁻¹ := by
        rw [mul_assoc τ'⁻¹, mul_inv_cancel, mul_one]
      _ = (τ' * a) * (k * τ'⁻¹ * k⁻¹) * a⁻¹ := by rw [hcomm]
      _ = τ' * (a * k) * τ'⁻¹ * (a * k)⁻¹ := by
        rw [show (a * k)⁻¹ = k⁻¹ * a⁻¹ from _root_.mul_inv_rev _ _]
        simp only [mul_assoc]
      _ = _ := by rw [hb])
  let t' := toUnit M.neutral.val.X ≫ t ≫ p
  let f' : M.neutral.val.X ⟶ M.neutral.val.X := t' * 𝟙 _ * t'⁻¹ * (𝟙 _)⁻¹
  have hcomp' {Y : SchemeOver F} (a : Y ⟶ M.neutral.val.X) :
      a ≫ f' = (toUnit Y ≫ t ≫ p) * a * (toUnit Y ≫ t ≫ p)⁻¹ * a⁻¹ := by
    simp [f', t', MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
  letI : Epi p.left := Flat.epi_of_flat_of_surjective p.left
  letI : Epi p := Over.epi_of_epi_left p
  have he : d ≫ p = f' := by
    apply (cancel_epi p).mp
    rw [← Category.assoc, hd, hcomp' p]
    change (τ * 𝟙 _ * τ⁻¹ * (𝟙 _)⁻¹) ≫ M.projection.hom.hom = _
    simp [τ, p, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
  refine ⟨y ≫ d, ?_⟩
  rw [Category.assoc, he, hcomp']

private theorem tensor_lid_repr (V : Type*) [AddCommGroup V] [Module F V] (x : F ⊗[F] V) :
    (1 : F) ⊗ₜ[F] TensorProduct.lid F V x = x :=
  (TensorProduct.lid F V).symm_apply_apply x

private theorem tensor_lid_alg_repr (A : Type*) [Ring A] [Algebra F A] (x : F ⊗[F] A) :
    (1 : F) ⊗ₜ[F] Algebra.TensorProduct.lid F A x = x :=
  (Algebra.TensorProduct.lid F A).symm_apply_apply x

private theorem pair_isometry_at_field (g : ρ.fixedSubalgebraˣ) :
    let R := CommAlgCat.of F F
    let t := Units.map (intoTensor (F := F) R ρ.fixedSubalgebra).toMonoidHom g
    IsPairIsometry D R t ↔
      D.involution.toLinearMap g.val * g.val = 1 ∧ PreservesSemitrace D g := by
  change _ ↔ _
  unfold IsPairIsometry
  dsimp only
  let A := ρ.fixedSubalgebra
  let V := symmetricPart D.involution
  let j := V.subtype.baseChange F
  let f := fun x => TensorProduct.AlgebraTensorModule.rid F F F (D.semitrace.baseChange F x)
  have hj (s : V) : j ((1 : F) ⊗ₜ[F] s) = (1 : F) ⊗ₜ[F] s.val := rfl
  have hf (s : V) : f ((1 : F) ⊗ₜ[F] s) = D.semitrace s := by
    simp [f, LinearMap.baseChange_tmul]
  have hmul (a b : A) : (((1 : F) ⊗ₜ[F] a) * ((1 : F) ⊗ₜ[F] b)) =
      (1 : F) ⊗ₜ[F] (a * b) := by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have h₁ : ((D.involution.baseChange F).toLinearMap ((1 : F) ⊗ₜ[F] g.val) *
        ((1 : F) ⊗ₜ[F] g.val) = 1) ↔ D.involution.toLinearMap g.val * g.val = 1 := by
    change ((D.involution.toLinearMap.baseChange F) ((1 : F) ⊗ₜ[F] g.val) *
      ((1 : F) ⊗ₜ[F] g.val) = _) ↔ _
    rw [LinearMap.baseChange_tmul, hmul, Algebra.TensorProduct.one_def]
    exact (Algebra.TensorProduct.lid F A).injective.eq_iff.symm.trans (by simp)
  change (((D.involution.baseChange F).toLinearMap ((1 : F) ⊗ₜ[F] g.val) *
    ((1 : F) ⊗ₜ[F] g.val) = 1) ∧
    (∀ x, ∃ y, j y = ((1 : F) ⊗ₜ[F] g.val) * j x *
    ((1 : F) ⊗ₜ[F] g.inv) ∧ f y = f x)) ↔ _
  rw [h₁]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h s
    obtain ⟨y, hy, hy'⟩ := h ((1 : F) ⊗ₜ[F] s)
    let z := TensorProduct.lid F V y
    have hz : (1 : F) ⊗ₜ[F] z = y := tensor_lid_repr V y
    rw [← hz, hj, hj, hmul, hmul] at hy
    rw [← hz, hf, hf] at hy'
    refine ⟨z, ?_, hy'⟩
    simpa using congrArg (Algebra.TensorProduct.lid F A) hy
  · intro h x
    let z := TensorProduct.lid F V x
    have hz : (1 : F) ⊗ₜ[F] z = x := tensor_lid_repr V x
    obtain ⟨y, hy, hy'⟩ := h z
    refine ⟨(1 : F) ⊗ₜ[F] y, ?_, ?_⟩
    · rw [← hz, hj, hj, hmul, hmul, hy]
    · rw [← hz, hf, hf, hy']

private theorem matrixAt_field (Q : QuaternionHyperbolicPresentation D hB d)
    (a : F ⊗[F] ρ.fixedSubalgebra) :
    let R := CommAlgCat.of F F
    (Q.matrixAt R a).map (Algebra.TensorProduct.lid F B) =
      Q.matrixModel (Algebra.TensorProduct.lid F ρ.fixedSubalgebra a) := by
  dsimp only
  let x := Algebra.TensorProduct.lid F ρ.fixedSubalgebra a
  have hx : (1 : F) ⊗ₜ[F] x = a := tensor_lid_alg_repr _ a
  conv_lhs => rw [← hx, Q.matrixAtFormula]
  ext i j
  simp [x, Matrix.map_apply]

private theorem vector_rational_pair (M : SpinModel G D)
    (g : Points G.val.X (CommAlgCat.of F F)) :
    let R := CommAlgCat.of F F
    let t := Units.map (Algebra.TensorProduct.lid F ρ.fixedSubalgebra).toMonoidHom
      (spinVectorProjection M R g)
    D.involution.toLinearMap t.val * t.val = 1 ∧ PreservesSemitrace D t := by
  dsimp only
  let R := CommAlgCat.of F F
  let a := spinVectorProjection M R g
  let t := Units.map (Algebra.TensorProduct.lid F ρ.fixedSubalgebra).toMonoidHom a
  have ht : Units.map (intoTensor (F := F) R ρ.fixedSubalgebra).toMonoidHom t = a :=
    Units.ext (tensor_lid_alg_repr _ a.val)
  apply (pair_isometry_at_field t).mp
  rw [ht]
  exact (M.fullRange R a).mp ⟨g ≫ (M.projection ≫ M.inclusion).hom.hom, rfl⟩

private theorem rational_column_action (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (g : Points G.val.X (CommAlgCat.of F F))
    (f : B × (Fin d → B) × B → B × (Fin d → B) × B)
    (h : ∀ p, Q.matrixModel (Algebra.TensorProduct.lid F ρ.fixedSubalgebra
        (spinVectorProjection M (CommAlgCat.of F F) g).val) *ᵥ column p.1 p.2.1 p.2.2 =
      column (f p).1 (f p).2.1 (f p).2.2) :
    ActsOnColumns M Q g f := by
  intro p
  funext i
  apply (Algebra.TensorProduct.lid F B).injective
  have hp := congrFun (h p) i
  simpa [Matrix.mulVec, dotProduct, ← Matrix.map_apply, matrixAt_field Q, map_sum, map_mul] using hp

private theorem gram_column (s : AntiEquiv F B) (H : Matrix (Fin d) (Fin d) B)
    (x z x' z' : B) (y y' : Fin d → B) :
    hermitianValue s (quaternionHyperbolicGram H) (column x y z) (column x' y' z') =
      antiValue s x * z' + antiValue s z * x' + hermitianValue s H y y' := by
  simp [hermitianValue, column, quaternionHyperbolicGram, fromBlocks_mulVec,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fintype.sum_sum_type, neg_one_eq_one (F := F)]

private def pairWeights (r : Fˣ) : QuaternionPairIndex d → F :=
  Sum.elim ![r.val, (r⁻¹ : Fˣ).val] fun _ => 1

private theorem diagonal_blocks_eq {C : Type*} [Ring C] (a b : C) :
    (Matrix.fromBlocks (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) C)
      0 0 (1 : Matrix (Fin d) (Fin d) C)) =
      Matrix.diagonal (Sum.elim ![a, b] (fun _ : Fin d => 1)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;> rfl
  · simp [fromBlocks, Matrix.diagonal_apply]
  · simp [fromBlocks, Matrix.diagonal_apply]
  · by_cases h : i = j <;> simp [fromBlocks, Matrix.diagonal_apply, Matrix.one_apply, h]

private theorem rational_pair_diagonal (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) {c : Cocharacter G.val}
    (hc : IsPairDiagonal M Q c) (r : Fˣ) :
    let R := CommAlgCat.of F F
    Q.matrixModel (Algebra.TensorProduct.lid F ρ.fixedSubalgebra
      (spinVectorProjection M R (cocharacterPoint c R r)).val) =
      Matrix.diagonal (algebraMap F B ∘ pairWeights r) := by
  dsimp only
  rw [← matrixAt_field Q, hc, diagonal_blocks_eq, Matrix.diagonal_map (map_zero _)]
  apply congrArg Matrix.diagonal
  funext i
  rcases i with i | i
  · fin_cases i <;> simp [pairWeights, Algebra.smul_def]
  · simp [pairWeights]

private theorem pairWeights_distinct (r : Fˣ) (hr : r.val ≠ 1) :
    r.val ≠ (r⁻¹ : Fˣ).val ∧ (r⁻¹ : Fˣ).val ≠ 1 := by
  constructor
  · intro h
    have hsq : r.val ^ 2 = 1 := by
      rw [pow_two]
      calc
        r.val * r.val = (r⁻¹ : Fˣ).val * r.val := congrArg (fun x => x * r.val) h
        _ = 1 := r.inv_val
    apply hr
    have hz : (r.val - 1) ^ 2 = 0 := by
      rw [sub_sq, hsq, CharP.ofNat_eq_zero F 2, zero_mul, zero_mul, sub_zero,
        one_pow, one_add_one_eq_two, CharP.ofNat_eq_zero F 2]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
  · intro h
    apply hr
    have hr' : r.val * (r⁻¹ : Fˣ).val = 1 := r.val_inv
    rwa [h, mul_one] at hr'

private theorem off_weight_zero {T : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B}
    {r : Fˣ} (h : Commute T (Matrix.diagonal (algebraMap F B ∘ pairWeights r)))
    {i j : QuaternionPairIndex d} (hij : pairWeights r i ≠ pairWeights r j) :
    T i j = 0 := by
  let A : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B :=
    Matrix.diagonal (algebraMap F B ∘ pairWeights r)
  have he : (T * A : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B) i j =
      (A * T : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B) i j :=
    congrArg (fun X : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B => X i j) h.eq
  dsimp only [A] at he
  rw [mul_diagonal, diagonal_mul] at he
  have hc := Algebra.commutes (R := F) (A := B) (pairWeights r j) (T i j)
  rw [Function.comp_apply, Function.comp_apply, ← hc] at he
  by_contra ht
  exact hij ((algebraMap F B).injective (mul_right_cancel₀ ht he.symm))

private theorem weight_blocks {T : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B}
    (r : Fˣ) (hr : r.val ≠ 1)
    (h : Commute T (Matrix.diagonal (algebraMap F B ∘ pairWeights r))) :
    T = Matrix.fromBlocks
      (Matrix.diagonal ![T (Sum.inl 0) (Sum.inl 0), T (Sum.inl 1) (Sum.inl 1)])
      0 0 T.toBlocks₂₂ := by
  have hdist := pairWeights_distinct r hr
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j
    · rfl
    · exact off_weight_zero h (by simpa [pairWeights] using hdist.1)
    · exact off_weight_zero h (by simpa [pairWeights] using hdist.1.symm)
    · rfl
  · fin_cases i
    · exact off_weight_zero h (by simpa [pairWeights] using hr)
    · exact off_weight_zero h (by simpa [pairWeights] using hdist.2)
  · fin_cases j
    · exact off_weight_zero h (by simpa [pairWeights] using hr.symm)
    · exact off_weight_zero h (by simpa [pairWeights] using hdist.2.symm)
  · rfl

private theorem weight_block_action (T : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)
    {a b : B}
    (hT : T = Matrix.fromBlocks (Matrix.diagonal ![a, b]) 0 0 T.toBlocks₂₂)
    (x z : B) (y : Fin d → B) :
    T *ᵥ column x y z = column (a * x) (T.toBlocks₂₂ *ᵥ y) (b * z) := by
  conv_lhs => rw [hT]
  funext i
  rcases i with i | i
  · fin_cases i <;> simp [column, fromBlocks_mulVec, mulVec_diagonal]
  · simp [column, fromBlocks_mulVec]

private def complementBlockUnit (T : (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)ˣ)
    {a b c e : B}
    (hT : T.val = Matrix.fromBlocks (Matrix.diagonal ![a,b]) 0 0 T.val.toBlocks₂₂)
    (hU : T.inv = Matrix.fromBlocks (Matrix.diagonal ![c,e]) 0 0 T.inv.toBlocks₂₂) :
    (Matrix (Fin d) (Fin d) B)ˣ where
  val := T.val.toBlocks₂₂
  inv := T.inv.toBlocks₂₂
  val_inv := by
    have h := congrArg Matrix.toBlocks₂₂ T.val_inv
    rw [hT, hU, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at h
    simpa only [toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add] using h
  inv_val := by
    have h := congrArg Matrix.toBlocks₂₂ T.inv_val
    rw [hT, hU, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at h
    simpa only [toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add] using h

private theorem centralizer (hrec : QuaternionPairRecovery.{u}) : CentralizerColumns.{u} := by
  intro F K I B _ _ _ _ _ _ _ _ _ _ _ _ _ ρ G D M _ hB hdeg d Q c hc W g hg
  obtain ⟨a, ha0, ha⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  have ha1 : a ≠ 1 := fun h => by rw [h, map_one] at ha; exact (lt_irrefl _ ha)
  let u := Units.mk0 a ha0
  let R := CommAlgCat.of F F
  let v := cocharacterPoint c R u
  let π : Points G.val.X R →* (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)ˣ :=
    (Units.map (Q.matrixModel.toMonoidHom.comp
      (Algebra.TensorProduct.lid F ρ.fixedSubalgebra).toMonoidHom)).comp
      (spinVectorProjection M R)
  let T := π g
  let t := T.val (Sum.inl 0) (Sum.inl 0)
  let s := T.val (Sum.inl 1) (Sum.inl 1)
  have hc' : Commute g v := by
    change Commute g (unitPoint R u ≫ c.hom.hom)
    have eq := (centralizes_iff c g).mp hg _ (𝟙 _) (unitPoint R u)
    rwa [Category.id_comp] at eq
  have hdiag : (π v).val = Matrix.diagonal (algebraMap F B ∘ pairWeights u) :=
    rational_pair_diagonal M Q hc u
  have hg' : Commute T.val (Matrix.diagonal (algebraMap F B ∘ pairWeights u)) := by
    rw [← hdiag]
    exact (hc'.map π).map (Units.coeHom (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B))
  have hT := weight_blocks u ha1 hg'
  have hinv : Commute T.inv (Matrix.diagonal (algebraMap F B ∘ pairWeights u)) := by
    rw [← hdiag]
    rw [show T.inv = (π g⁻¹).val from congrArg Units.val (map_inv π g).symm]
    exact (hc'.inv_left.map π).map (Units.coeHom (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B))
  have hU := weight_blocks u ha1 hinv
  let S := complementBlockUnit T hT hU
  let r := columnEquivOfUnit S
  have hcol (x z : B) (y : Fin d → B) :
      T.val *ᵥ column x y z = column (t * x) (r y) (s * z) :=
    weight_block_action T.val hT x z y
  obtain ⟨hi, hst⟩ := vector_rational_pair M g
  obtain ⟨hH, hQ⟩ := (rational_preserves_forms hrec hdeg Q W
    (Units.map (Algebra.TensorProduct.lid F ρ.fixedSubalgebra).toMonoidHom
      (spinVectorProjection M R g))).mp ⟨hi, hst⟩
  change (∀ x y, hermitianValue Q.conjugation.anti (quaternionHyperbolicGram Q.complement.val)
    (T.val *ᵥ x) (T.val *ᵥ y) = _) at hH
  have ht : antiValue Q.conjugation.anti t * s = 1 := by
    have h := hH (column 1 0 0) (column 0 0 1)
    rw [hcol, hcol] at h
    have hr0 : r (0 : Fin d → B) = 0 := map_zero r
    simp only [mul_one, mul_zero, hr0, gram_column, antiValue_zero, antiValue_one,
      zero_mul, one_mul, add_zero] at h
    simpa [hermitianValue] using h
  have htn : t ≠ 0 := fun h => by rw [h, antiValue_zero, zero_mul] at ht; exact zero_ne_one ht
  have hs : s = (antiValue Q.conjugation.anti t)⁻¹ := eq_inv_of_mul_eq_one_right ht
  refine ⟨Units.mk0 t htn, r, ?_, ?_, ?_⟩
  · intro x y
    have h := hH (column 0 x 0) (column 0 y 0)
    rw [hcol, hcol] at h
    simp only [mul_zero] at h
    rw [gram_complement, gram_complement] at h
    rw [W.pairingFormula]
    exact h
  · intro x
    have h := hQ (column 0 x 0)
    change scalarClass F (hermitianValue Q.conjugation.anti
      (quaternionHyperbolicGram Q.complement.val) (T.val *ᵥ column 0 x 0)
      (Q.matrixModel W.ell *ᵥ (T.val *ᵥ column 0 x 0))) = _ at h
    rw [hcol, mul_zero, mul_zero, W.quadraticFormula, W.quadraticFormula] at h
    simpa only [mul_zero, map_zero, zero_add] using h
  · apply rational_column_action M Q
    rintro ⟨x,y,z⟩
    exact (hcol x z y).trans (by rw [hs]; rfl)

section Shears

variable {s : AntiEquiv F B} {V : Type*} [AddCommGroup V] [Module Bᵐᵒᵖ V]

local notation "bar" => antiValue s
local notation:75 x:75 " ◁ " a:76 => (op a • x)

private theorem bar_scalar (a : F) : bar (algebraMap F B a) = algebraMap F B a := by
  simp [antiValue, AlgEquiv.commutes]

include F in
private theorem add_self_quaternion (x : B) : x + x = 0 := by
  rw [← two_mul, two_zero (F := F), zero_mul]

private theorem class_scalar (a : F) : scalarClass F (algebraMap F B a) = 0 :=
  (Submodule.Quotient.mk_eq_zero (scalarLine F B)).mpr ⟨a, rfl⟩

private theorem class_conjugate (hs : ∀ a, bar a = quaternionConjugate hB a) (a : B) :
    scalarClass F (bar a) = scalarClass F a := by
  have hh : scalarClass F (bar a + a) = 0 := by
    rw [hs, quaternionConjugate, sub_add_cancel, class_scalar]
  rw [map_add] at hh
  exact add_right_cancel (hh.trans (by rw [← map_add, add_self_quaternion (F := F), map_zero]))

private theorem class_cancel (a b : ScalarClasses F B) : a + b + b = a := by
  obtain ⟨x, rfl⟩ := (scalarLine F B).mkQ_surjective b
  rw [add_assoc, ← map_add, add_self_quaternion (F := F), map_zero, add_zero]

private theorem hermitian_bar (h : HermitianPairing s V) (x y : V) :
    bar (h.value x y) = h.value y x :=
  (h.hermitian x y).symm

private theorem hermitian_add_left (h : HermitianPairing s V) (x y z : V) :
    h.value (x + y) z = h.value x z + h.value y z := by
  rw [← hermitian_bar h z (x + y), h.add_right, antiValue_add, hermitian_bar, hermitian_bar]

private theorem hermitian_smul_left (h : HermitianPairing s V) (x y : V) (a : B) :
    h.value (x ◁ a) y = bar a * h.value x y := by
  rw [← hermitian_bar h y (x ◁ a), h.smul_right, antiValue_mul, hermitian_bar]

private theorem hermitian_zero_right (h : HermitianPairing s V) (x : V) :
    h.value x 0 = 0 := by
  simpa using h.smul_right x x 0

private theorem norm_of_refinement
    (h : HermitianPairing s V) (ell : V →ₗ[Bᵐᵒᵖ] V) (ht : IsTraceOne h ell)
    (x : V) (b : B) (hb : scalarClass F b = refinement h ell x) :
    h.value x x = bar b + b := by
  have hh := ht x x
  rw [← hermitian_bar h x (ell x)] at hh
  change scalarClass F b = scalarClass F (h.value x (ell x)) at hb
  obtain ⟨a, ha⟩ := class_zero_difference hb
  have hb' := sub_eq_iff_eq_add.mp ha.symm
  rw [← hh, hb', antiValue_add, bar_scalar]
  calc
    _ = (bar (h.value x (ell x)) + h.value x (ell x)) +
        (algebraMap F B a + algebraMap F B a) := by
      rw [add_self_quaternion (F := F), add_zero]
    _ = _ := by abel

private def plusShear (h : HermitianPairing s V) (w : V) (b : B) :
    B × V × B → B × V × B
  | (x, y, z) => (x + h.value w y + b * z, y + w ◁ z, z)

private def minusShear (h : HermitianPairing s V) (w : V) (b : B) :
    B × V × B → B × V × B
  | (x, y, z) => (x, y + w ◁ x, z + h.value w y + b * x)

private def pairValue (h : HermitianPairing s V) (p q : B × V × B) : B :=
  bar p.1 * q.2.2 + bar p.2.2 * q.1 + h.value p.2.1 q.2.1

private def quadraticValue (h : HermitianPairing s V) (ell : V →ₗ[Bᵐᵒᵖ] V)
    (p : B × V × B) : ScalarClasses F B :=
  scalarClass F (bar p.1 * p.2.2) + refinement h ell p.2.1

private theorem shears_preserve_pairing
    (h : HermitianPairing s V) (w : V) (b : B)
    (hn : h.value w w = bar b + b) (p q : B × V × B) :
    pairValue h (plusShear h w b p) (plusShear h w b q) = pairValue h p q ∧
    pairValue h (minusShear h w b p) (minusShear h w b q) = pairValue h p q := by
  rcases p with ⟨x, y, z⟩
  rcases q with ⟨x', y', z'⟩
  constructor <;>
    simp only [pairValue, plusShear, minusShear, antiValue_add, antiValue_mul,
      hermitian_add_left, h.add_right, h.smul_right, hermitian_smul_left, hermitian_bar, hn] <;>
    noncomm_ring <;>
    simp [two_zero (F := F)]

private theorem shears_preserve_refinement (href : RefinementIdentities.{u,u,w})
    {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V]
    (hdeg : degree F B = 2) (hs : ∀ a, bar a = quaternionConjugate hB a)
    (h : HermitianPairing s V) (ell : V →ₗ[Bᵐᵒᵖ] V) (ht : IsTraceOne h ell)
    (w₀ : V) (b : B) (hb : scalarClass F b = refinement h ell w₀) (p : B × V × B) :
    quadraticValue h ell (plusShear h w₀ b p) = quadraticValue h ell p ∧
    quadraticValue h ell (minusShear h w₀ b p) = quadraticValue h ell p := by
  obtain ⟨hscale, hclass, hadd, _⟩ := href hB hdeg s hs h ell ht
  have hr (a : B) : refinement h ell (w₀ ◁ a) = scalarClass F (bar a * b * a) :=
    (hscale w₀ a).trans (hclass a _ _ hb.symm)
  rcases p with ⟨x, y, z⟩
  constructor
  · simp only [quadraticValue, plusShear, antiValue_add, antiValue_mul, add_mul, map_add, hadd, hr,
      h.smul_right, hermitian_bar]
    calc
      _ = (scalarClass F (bar x * z) + refinement h ell y +
          (scalarClass F (h.value y w₀ * z) + scalarClass F (h.value y w₀ * z))) +
          (scalarClass F (bar z * bar b * z) + scalarClass F (bar z * b * z)) := by abel
      _ = _ := by rw [← add_assoc (scalarClass F (bar x * z) + refinement h ell y),
          class_cancel, hclass z _ _ (class_conjugate hs b), ← add_assoc, class_cancel]
  · simp only [quadraticValue, minusShear, mul_add, map_add, hadd, hr, h.smul_right, ← mul_assoc]
    have hm : scalarClass F (bar x * h.value w₀ y) = scalarClass F (h.value y w₀ * x) := by
      rw [← class_conjugate hs (h.value y w₀ * x), antiValue_mul, hermitian_bar]
    rw [hm]
    calc
      _ = ((scalarClass F (bar x * z) + refinement h ell y) +
          scalarClass F (h.value y w₀ * x) + scalarClass F (h.value y w₀ * x)) +
          scalarClass F (bar x * b * x) + scalarClass F (bar x * b * x) := by abel
      _ = _ := by rw [class_cancel, class_cancel]

end Shears

private abbrev fieldAlgebra (F : Type u) [Field F] := CommAlgCat.of F F

private def evalTensor {V : Type*} [AddCommMonoid V] [Module F V] (a : F) :
    Polynomial F ⊗[F] V →ₗ[F] V :=
  (TensorProduct.lid F V).toLinearMap.comp
    (TensorProduct.map (Polynomial.aeval a).toLinearMap LinearMap.id)

@[simp] private theorem evalTensor_tmul {V : Type*} [AddCommMonoid V] [Module F V]
    (a : F) (p : Polynomial F) (v : V) :
    evalTensor a (p ⊗ₜ[F] v) = p.eval a • v := by
  simp [evalTensor]

private def evalTensorAlg {A : Type*} [Ring A] [Algebra F A] (a : F) :
    Polynomial F ⊗[F] A →ₐ[F] A :=
  (Algebra.TensorProduct.lid F A).toAlgHom.comp (tensorMap A (Polynomial.aeval a))

private theorem evalTensorAlg_apply {A : Type*} [Ring A] [Algebra F A] (a : F)
    (x : Polynomial F ⊗[F] A) : evalTensorAlg a x = evalTensor a x := by
  induction x using TensorProduct.inductionOn with
  | tmul p x => simp [evalTensorAlg, tensorMap]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem evalTensor_baseChange {V U : Type*} [AddCommMonoid V] [Module F V]
    [AddCommMonoid U] [Module F U] (f : V →ₗ[F] U) (a : F) (x : Polynomial F ⊗[F] V) :
    evalTensor a (f.baseChange (Polynomial F) x) = f (evalTensor a x) := by
  induction x using TensorProduct.inductionOn with
  | tmul p x => simp [LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem polynomial_ext_of_eval [Infinite F] {p q : Polynomial F}
    (h : ∀ a : F, a ≠ 0 → p.eval a = q.eval a) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  exact ((Set.infinite_univ (α := F)).sdiff (Set.finite_singleton (0 : F))).mono
    (fun a ha => h a ha.2)

private theorem tensorPolynomial_ext [Infinite F] {V : Type*} [AddCommGroup V] [Module F V]
    {x y : Polynomial F ⊗[F] V}
    (h : ∀ a : F, evalTensor a x = evalTensor a y) : x = y := by
  let b := Module.Basis.ofVectorSpace F V
  let p := b.baseChange (Polynomial F)
  have he (a : F) (z : Polynomial F ⊗[F] V) (i) :
      ((p.repr z) i).eval a = b.repr (evalTensor a z) i := by
    induction z using TensorProduct.inductionOn with
    | tmul q v =>
      simp [p, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_comm]
    | add z z' hz hz' => simp only [map_add, Finsupp.add_apply, Polynomial.eval_add, hz, hz']
  apply p.repr.injective
  apply Finsupp.ext
  intro i
  exact polynomial_ext_of_eval fun a _ => by rw [he a x i, he a y i, h a]

private theorem evalTensor_functional {V : Type*} [AddCommMonoid V] [Module F V]
    (f : V →ₗ[F] F) (a : F) (x : Polynomial F ⊗[F] V) :
    Polynomial.eval a (TensorProduct.AlgebraTensorModule.rid F (Polynomial F) (Polynomial F)
      (f.baseChange (Polynomial F) x)) = f (evalTensor a x) := by
  induction x using TensorProduct.inductionOn with
  | tmul p v =>
    simp [LinearMap.baseChange_tmul, Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, Polynomial.eval_add, hx, hy]

private theorem evalTensor_mul {A : Type*} [Ring A] [Algebra F A]
    (a : F) (x y : Polynomial F ⊗[F] A) :
    evalTensor a (x * y) = evalTensor a x * evalTensor a y := by
  rw [← evalTensorAlg_apply a (x * y), ← evalTensorAlg_apply a x, ← evalTensorAlg_apply a y,
    map_mul]

private theorem evalTensor_one {A : Type*} [Ring A] [Algebra F A] (a : F) :
    evalTensor a (1 : Polynomial F ⊗[F] A) = 1 := by
  rw [← evalTensorAlg_apply, map_one]

/-- Conjugation preserves a submodule functional over the polynomial ring if
it does so after each specialization at a point of the infinite base field. -/
private theorem polynomial_preserves_functional [Infinite F] {A : Type*}
    [Ring A] [Algebra F A] (S : Submodule F A) (f : S →ₗ[F] F)
    (g : (Polynomial F ⊗[F] A)ˣ)
    (h : ∀ (a : F) (x : S),
      let t := Units.map (evalTensorAlg a).toMonoidHom g
      ∃ y : S, y.val = t.val * x.val * t.inv ∧ f y = f x)
    (x : Polynomial F ⊗[F] S) :
    ∃ y : Polynomial F ⊗[F] S,
      S.subtype.baseChange (Polynomial F) y = g.val * S.subtype.baseChange (Polynomial F) x * g.inv ∧
      TensorProduct.AlgebraTensorModule.rid F (Polynomial F) (Polynomial F)
        (f.baseChange (Polynomial F) y) =
      TensorProduct.AlgebraTensorModule.rid F (Polynomial F) (Polynomial F)
        (f.baseChange (Polynomial F) x) := by
  let P := Polynomial F
  let j : S →ₗ[F] A := S.subtype
  obtain ⟨r, hr⟩ := @LinearMap.exists_leftInverse_of_injective F S A _ _ _ _ _ j S.ker_subtype
  have hrj (v : S) : r (j v) = v := DFunLike.congr_fun hr v
  let z : P ⊗[F] A := g.val * j.baseChange P x * g.inv
  let y : P ⊗[F] S := r.baseChange P z
  have he (a : F) : ∃ v : S, j v = evalTensor a z ∧ f v = f (evalTensor a x) := by
    obtain ⟨v, hv, hf⟩ := h a (evalTensor a x)
    refine ⟨v, ?_, hf⟩
    change j v = evalTensor a (g.val * j.baseChange P x * g.inv)
    rw [evalTensor_mul, evalTensor_mul, evalTensor_baseChange j a x]
    rw [← evalTensorAlg_apply a g.val, ← evalTensorAlg_apply a g.inv]
    exact hv
  have hy (a : F) (v : S) (hv : j v = evalTensor a z) : evalTensor a y = v := by
    change evalTensor a (r.baseChange P z) = v
    rw [evalTensor_baseChange r a z, ← hv, hrj]
  refine ⟨y, ?_, ?_⟩
  · change j.baseChange P y = z
    apply tensorPolynomial_ext
    intro a
    obtain ⟨v, hv, _⟩ := he a
    rw [evalTensor_baseChange j a y, hy a v hv, hv]
  · apply polynomial_ext_of_eval
    intro a _
    obtain ⟨v, hv, hf⟩ := he a
    rw [evalTensor_functional, evalTensor_functional, hy a v hv, hf]

private theorem polynomial_pair_isometry [Infinite F]
    (g : (Polynomial F ⊗[F] ρ.fixedSubalgebra)ˣ)
    (h : ∀ a : F, let t := Units.map (evalTensorAlg a).toMonoidHom g
      D.involution.toLinearMap t.val * t.val = 1 ∧ PreservesSemitrace D t) :
    IsPairIsometry D (polynomialAlgebra (fieldAlgebra F)) g := by
  constructor
  · change D.involution.toLinearMap.baseChange (Polynomial F) g.val * g.val = 1
    apply tensorPolynomial_ext
    intro a
    rw [evalTensor_mul, evalTensor_baseChange, ← evalTensorAlg_apply a g.val, evalTensor_one]
    exact (h a).1
  · exact polynomial_preserves_functional (symmetricPart D.involution) D.semitrace g
      (fun a => (h a).2)

private theorem polynomial_point_neutral (M : SpinModel G D)
    (g : Points M.full.val.X (polynomialAlgebra (fieldAlgebra F)))
    (hg : mapPoints (polynomialEvaluate (fieldAlgebra F) 0) g = 1) :
    ∃ y : Points M.neutral.val.X (polynomialAlgebra (fieldAlgebra F)),
      y ≫ M.inclusion.hom.hom = g := by
  let R := fieldAlgebra F
  let P := polynomialAlgebra R
  let incl := M.inclusion.hom.hom
  letI : IsOpenImmersion incl.left := M.openImmersion
  let T := (testSpec F).obj (Opposite.op P)
  haveI : ConnectedSpace T.left := by
    change ConnectedSpace (Spec (CommRingCat.of (Polynomial F)))
    infer_instance
  have hId : η[M.full.val.X].left
      (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of F)))) ∈ Set.range g.left := by
    let X := (testSpec F).obj (Opposite.op R)
    let a := (testSpec F).map (polynomialEvaluate R 0).op
    have e : a ≫ g = toUnit X ≫ η[M.full.val.X] := hg
    let x : X.left := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of F)))
    refine ⟨a.left x, ?_⟩
    have hx := congrArg (fun f : X ⟶ M.full.val.X => f.left x) e
    have hpt : (toUnit X).left x =
        Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of F))) := by
      change _ = (_ : Spec (CommRingCat.of F))
      exact Subsingleton.elim (_ : Spec (CommRingCat.of F)) _
    change g.left (a.left x) = η[M.full.val.X].left ((toUnit X).left x) at hx
    rw [hpt] at hx
    exact hx
  have hsubset : Set.range g.left ⊆ Set.range incl.left := by
    rw [M.identityComponent]
    exact (isConnected_range g.left.continuous).subset_connectedComponent hId
  let y := IsOpenImmersion.lift incl.left g.left hsubset
  refine ⟨Over.homMk y ?_, Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  rw [← Over.w incl, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w]

private theorem spin_projection_injective (M : SpinModel G D) (R : TestAlgebra F)
    [_root_.IsReduced R] : Function.Injective (spinVectorProjection M R) := by
  intro x y hxy
  let π : Points G.val.X R →* Points M.neutral.val.X R :=
    (((groupPointsFunctor F).map M.projection).app R).hom
  have hπ : π x = π y := by
    let : IsOpenImmersion M.inclusion.hom.hom.left := M.openImmersion
    let : Mono M.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono M.inclusion.hom.hom).mp
    apply M.fullFaithful R
    change M.fullPoints R ((x ≫ M.projection.hom.hom) ≫ M.inclusion.hom.hom) =
      M.fullPoints R ((y ≫ M.projection.hom.hom) ≫ M.inclusion.hom.hom)
    rw [Category.assoc, Category.assoc]
    exact hxy
  have hker : π (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hπ, mul_inv_cancel]
  let p : Points M.kernel.group.X R := M.isKernel.lift (x * y⁻¹) (toUnit _) hker
  have hp : p ≫ M.kernel.inclusion.hom.hom = x * y⁻¹ := M.isKernel.lift_fst _ _ _
  let a := (M.kernelPoints R p).val
  have ha : (a : R) ^ 2 = 1 := (mem_rootsOfUnity' 2 a).mp (M.kernelPoints R p).property
  have htwo : (2 : R) = 0 := by
    rw [← map_ofNat (algebraMap F R) 2, CharP.ofNat_eq_zero F 2, map_zero]
  have ha₁ : (a : R) = 1 := by
    apply sub_eq_zero.mp
    apply IsNilpotent.eq_zero
    refine ⟨2, ?_⟩
    rw [sub_sq, ha, htwo, zero_mul, zero_mul, sub_zero, one_pow, one_add_one_eq_two, htwo]
  have hp₁ : p = 1 := by
    apply (M.kernelPoints R).injective
    rw [map_one]
    exact Subtype.ext (Units.ext ha₁)
  have hxy₁ : x * y⁻¹ = 1 := by
    rw [← hp, hp₁]
    exact map_one (((groupPointsFunctor F).map M.kernel.inclusion).app R).hom
  exact mul_inv_eq_one.mp hxy₁

private abbrev PairColumns (B : Type*) (d : ℕ) := B × (Fin d → B) × B

private def orientedColumn (rev : Bool) (p : PairColumns B d) : QuaternionPairIndex d → B :=
  if rev then column p.2.2 p.2.1 p.1 else column p.1 p.2.1 p.2.2

private def pairCoordinates (rev : Bool) :
    (QuaternionPairIndex d → B) ≃ₗ[Bᵐᵒᵖ] PairColumns B d where
  toFun x := if rev then (x (Sum.inl 1), x ∘ Sum.inr, x (Sum.inl 0))
    else (x (Sum.inl 0), x ∘ Sum.inr, x (Sum.inl 1))
  invFun := orientedColumn rev
  left_inv x := by
    funext i
    rcases i with i | i
    · fin_cases i <;> cases rev <;> rfl
    · cases rev <;> rfl
  right_inv x := by cases rev <;> rfl
  map_add' x y := by cases rev <;> rfl
  map_smul' a x := by cases rev <;> rfl

private theorem pairCoordinates_apply_oriented (rev : Bool) (p : PairColumns B d) :
    pairCoordinates rev (orientedColumn rev p) = p :=
  (pairCoordinates rev).apply_symm_apply p

private theorem orientedColumn_surjective (rev : Bool) :
    Function.Surjective (orientedColumn rev : PairColumns B d → _) :=
  (pairCoordinates rev).symm.surjective

private theorem orientedColumn_injective (rev : Bool) :
    Function.Injective (orientedColumn rev : PairColumns B d → _) :=
  (pairCoordinates rev).symm.injective

private def upperIncrement {s : AntiEquiv F B} (h : HermitianPairing s (Fin d → B))
    (w : Fin d → B) : PairColumns B d →ₗ[Bᵐᵒᵖ] PairColumns B d where
  toFun p := (h.value w p.2.1, fun j => w j * p.2.2, 0)
  map_add' x y := by
    refine Prod.ext (h.add_right w x.2.1 y.2.1) (Prod.ext ?_ (zero_add _).symm)
    funext i
    exact mul_add _ _ _
  map_smul' a x := by
    refine Prod.ext (h.smul_right w x.2.1 (unop a)) (Prod.ext ?_ ?_)
    · funext i
      exact (mul_assoc _ _ _).symm
    · exact (zero_mul _).symm

private def upperCorner (b : B) : PairColumns B d →ₗ[Bᵐᵒᵖ] PairColumns B d where
  toFun x := (b * x.2.2, 0, 0)
  map_add' x y := Prod.ext (mul_add _ _ _) (Prod.ext (zero_add _).symm (zero_add _).symm)
  map_smul' a x := by
    refine Prod.ext (mul_assoc _ _ _).symm (Prod.ext ?_ ?_)
    · funext i
      exact (zero_mul _).symm
    · exact (zero_mul _).symm

private def inColumns (rev : Bool) (f : PairColumns B d →ₗ[Bᵐᵒᵖ] PairColumns B d) :
    Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B :=
  let e := pairCoordinates (B := B) (d := d) rev
  columnMatrix (e.symm.toLinearMap.comp (f.comp e.toLinearMap))

private theorem inColumns_action (rev : Bool)
    (f : PairColumns B d →ₗ[Bᵐᵒᵖ] PairColumns B d) (p : PairColumns B d) :
    inColumns rev f *ᵥ orientedColumn rev p = orientedColumn rev (f p) := by
  rw [inColumns, columnMatrix_apply]
  change (pairCoordinates rev).symm (f (pairCoordinates rev (orientedColumn rev p))) = _
  rw [pairCoordinates_apply_oriented]
  rfl

private theorem orientedColumn_add (rev : Bool) (p q : PairColumns B d) :
    orientedColumn rev (p + q) = orientedColumn rev p + orientedColumn rev q :=
  map_add (pairCoordinates rev).symm p q

private theorem orientedColumn_smul (rev : Bool) (a : F) (p : PairColumns B d) :
    orientedColumn rev (a • p) = a • orientedColumn rev p := by
  funext i
  rcases i with i | i
  · fin_cases i <;> cases rev <;> rfl
  · cases rev <;> rfl

private theorem center_smul_column (a : F) (x : Fin d → B) :
    a • x = op (algebraMap F B a) • x := by
  funext i
  change a • x i = x i * algebraMap F B a
  rw [Algebra.smul_def, Algebra.commutes]

private theorem hermitian_smul_center_left {s : AntiEquiv F B}
    (h : HermitianPairing s (Fin d → B)) (a : F) (x y : Fin d → B) :
    h.value (a • x) y = a • h.value x y := by
  rw [center_smul_column a x, hermitian_smul_left, bar_scalar, Algebra.smul_def]

private theorem hermitian_smul_center_right {s : AntiEquiv F B}
    (h : HermitianPairing s (Fin d → B)) (a : F) (x y : Fin d → B) :
    h.value x (a • y) = a • h.value x y := by
  rw [center_smul_column a y, h.smul_right, Algebra.smul_def, Algebra.commutes]

private def shearMatrix {s : AntiEquiv F B} (rev : Bool)
    (h : HermitianPairing s (Fin d → B)) (w : Fin d → B) (b : B) :
    Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B :=
  1 + inColumns rev (upperIncrement h w) + inColumns rev (upperCorner b)

private theorem shear_scaled_action {s : AntiEquiv F B} (rev : Bool)
    (h : HermitianPairing s (Fin d → B)) (w : Fin d → B) (b : B) (a : F)
    (p : PairColumns B d) :
    (1 + a • inColumns rev (upperIncrement h w) +
      a ^ 2 • inColumns rev (upperCorner b)) *ᵥ orientedColumn rev p =
      orientedColumn rev (plusShear h (a • w) (a ^ 2 • b) p) := by
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    inColumns_action, inColumns_action, ← orientedColumn_smul, ← orientedColumn_smul,
    ← orientedColumn_add, ← orientedColumn_add]
  apply congrArg (orientedColumn rev)
  rcases p with ⟨x, y, z⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change x + a • h.value w y + a ^ 2 • (b * z) =
      x + h.value (a • w) y + (a ^ 2 • b) * z
    rw [hermitian_smul_center_left, smul_mul_assoc]
  · funext i
    change y i + a • (w i * z) + a ^ 2 • (0 : B) = y i + (a • w i) * z
    rw [smul_zero, add_zero, smul_mul_assoc]
  · change z + a • (0 : B) + a ^ 2 • (0 : B) = z
    simp

private theorem shear_matrix_action {s : AntiEquiv F B} (rev : Bool)
    (h : HermitianPairing s (Fin d → B)) (w : Fin d → B) (b : B) (p : PairColumns B d) :
    shearMatrix rev h w b *ᵥ orientedColumn rev p = orientedColumn rev (plusShear h w b p) := by
  simpa [shearMatrix] using shear_scaled_action rev h w b 1 p

private theorem plus_shear_mul {s : AntiEquiv F B}
    (h : HermitianPairing s (Fin d → B)) (w v : Fin d → B) (b c : B) (p : PairColumns B d) :
    plusShear h w b (plusShear h v c p) = plusShear h (w + v) (b + c + h.value w v) p := by
  rcases p with ⟨x, y, z⟩
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · change x + h.value v y + c * z + h.value w (y + op z • v) + b * z =
      x + h.value (w + v) y + (b + c + h.value w v) * z
    rw [h.add_right, h.smul_right, hermitian_add_left]
    noncomm_ring
  · funext i
    change y i + v i * z + w i * z = y i + (w i + v i) * z
    rw [add_mul]
    abel

private theorem shear_matrix_mul {s : AntiEquiv F B} (rev : Bool)
    (h : HermitianPairing s (Fin d → B)) (w v : Fin d → B) (b c : B) :
    shearMatrix rev h w b * shearMatrix rev h v c =
      shearMatrix rev h (w + v) (b + c + h.value w v) := by
  apply matrix_eq_of_mulVec
  intro p
  obtain ⟨p, rfl⟩ := orientedColumn_surjective rev p
  rw [← mulVec_mulVec, shear_matrix_action, shear_matrix_action, plus_shear_mul, shear_matrix_action]

private theorem shear_matrix_one {s : AntiEquiv F B} (rev : Bool)
    (h : HermitianPairing s (Fin d → B)) :
    shearMatrix rev h 0 0 = 1 := by
  apply matrix_eq_of_mulVec
  intro p
  obtain ⟨⟨x, y, z⟩, rfl⟩ := orientedColumn_surjective rev p
  rw [shear_matrix_action, Matrix.one_mulVec]
  have h0 : h.value 0 y = 0 := by rw [← hermitian_bar h y 0, hermitian_zero_right, antiValue_zero]
  simp [plusShear, h0]

private def shearUnit {s : AntiEquiv F B} (rev : Bool)
    (h : HermitianPairing s (Fin d → B)) (w : Fin d → B) (b : B) :
    (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)ˣ where
  val := shearMatrix rev h w b
  inv := shearMatrix rev h w (b + h.value w w)
  val_inv := by
    have hw : w + w = 0 := funext fun i => add_self_quaternion (F := F) (w i)
    rw [shear_matrix_mul, hw]
    have hb : b + (b + h.value w w) + h.value w w = 0 := by
      rw [← add_assoc b, add_self_quaternion (F := F), zero_add, add_self_quaternion (F := F)]
    rw [hb, shear_matrix_one]
  inv_val := by
    have hw : w + w = 0 := funext fun i => add_self_quaternion (F := F) (w i)
    rw [shear_matrix_mul, hw]
    have hb : b + h.value w w + b + h.value w w = 0 := by
      rw [add_right_comm b, add_self_quaternion (F := F), zero_add, add_self_quaternion (F := F)]
    rw [hb, shear_matrix_one]

private theorem scaled_admissible {s : AntiEquiv F B}
    (h : HermitianPairing s (Fin d → B)) (ell : (Fin d → B) →ₗ[Bᵐᵒᵖ] (Fin d → B))
    {w : Fin d → B} {b : B} (hb : scalarClass F b = refinement h ell w) (a : F) :
    scalarClass F (a ^ 2 • b) = refinement h ell (a • w) := by
  have hℓ : ell (a • w) = a • ell w := by
    simp only [center_smul_column (B := B) a, map_smul]
  rw [refinement, hℓ, hermitian_smul_center_left, hermitian_smul_center_right,
    smul_smul, ← pow_two, map_smul, map_smul, hb]
  rfl

private theorem shear_rational_isometry (hrec : QuaternionPairRecovery.{u})
    (href : RefinementIdentities.{u,u,u}) (hdeg : degree F B = 2)
    (Q : QuaternionHyperbolicPresentation D hB d) (W : ComplementRefinement Q)
    (rev : Bool) (w : Fin d → B) (b : B)
    (hb : scalarClass F b = refinement W.pairing W.complementAction w) :
    let g := Units.map Q.matrixModel.symm.toMonoidHom (shearUnit rev W.pairing w b)
    D.involution.toLinearMap g.val * g.val = 1 ∧ PreservesSemitrace D g := by
  dsimp only
  apply (rational_preserves_forms hrec hdeg Q W _).mpr
  change (∀ p q, hermitianValue Q.conjugation.anti (quaternionHyperbolicGram Q.complement.val)
      (Q.matrixModel (Q.matrixModel.symm (shearMatrix rev W.pairing w b)) *ᵥ p)
      (Q.matrixModel (Q.matrixModel.symm (shearMatrix rev W.pairing w b)) *ᵥ q) =
        hermitianValue Q.conjugation.anti (quaternionHyperbolicGram Q.complement.val) p q) ∧ _
  simp only [AlgEquiv.apply_symm_apply]
  have hnorm := norm_of_refinement W.pairing W.complementAction W.complementTraceOne w b hb
  have hpair (p q : PairColumns B d) :
      hermitianValue Q.conjugation.anti (quaternionHyperbolicGram Q.complement.val)
        (column p.1 p.2.1 p.2.2) (column q.1 q.2.1 q.2.2) =
          pairValue W.pairing p q := by rw [gram_column, pairValue, W.pairingFormula]
  have hQuad (p : PairColumns B d) :
      scalarClass F (hermitianValue Q.conjugation.anti (quaternionHyperbolicGram Q.complement.val)
        (column p.1 p.2.1 p.2.2) (Q.matrixModel W.ell *ᵥ column p.1 p.2.1 p.2.2)) =
      quadraticValue W.pairing W.complementAction p := W.quadraticFormula _ _ _
  constructor
  · intro p q
    obtain ⟨⟨x, y, z⟩, rfl⟩ := orientedColumn_surjective rev p
    obtain ⟨⟨x', y', z'⟩, rfl⟩ := orientedColumn_surjective rev q
    rw [shear_matrix_action, shear_matrix_action]
    cases rev
    · exact (hpair _ _).trans ((shears_preserve_pairing W.pairing w b hnorm
        (x, y, z) (x', y', z')).1.trans (hpair _ _).symm)
    · exact (hpair _ _).trans ((shears_preserve_pairing W.pairing w b hnorm
        (z, y, x) (z', y', x')).2.trans (hpair _ _).symm)
  · change ∀ p, scalarClass F (hermitianValue Q.conjugation.anti (quaternionHyperbolicGram Q.complement.val)
      (Q.matrixModel (Q.matrixModel.symm (shearMatrix rev W.pairing w b)) *ᵥ p)
      (Q.matrixModel W.ell *ᵥ (Q.matrixModel (Q.matrixModel.symm (shearMatrix rev W.pairing w b)) *ᵥ p))) = _
    simp only [AlgEquiv.apply_symm_apply]
    intro p
    obtain ⟨⟨x, y, z⟩, rfl⟩ := orientedColumn_surjective rev p
    rw [shear_matrix_action]
    cases rev
    · exact (hQuad _).trans ((shears_preserve_refinement href hdeg Q.canonical W.pairing
        W.complementAction W.complementTraceOne w b hb (x, y, z)).1.trans (hQuad _).symm)
    · exact (hQuad _).trans ((shears_preserve_refinement href hdeg Q.canonical W.pairing
        W.complementAction W.complementTraceOne w b hb (z, y, x)).2.trans (hQuad _).symm)

private def shearPolynomialValue (Q : QuaternionHyperbolicPresentation D hB d)
    (W : ComplementRefinement Q) (rev : Bool) (w : Fin d → B) (b : B) :
    Polynomial F ⊗[F] ρ.fixedSubalgebra :=
  1 + Polynomial.X ⊗ₜ[F] Q.matrixModel.symm (inColumns rev (upperIncrement W.pairing w)) +
    (Polynomial.X ^ 2) ⊗ₜ[F] Q.matrixModel.symm (inColumns rev (upperCorner b))

private theorem evalTensorAlg_tmul {A : Type*} [Ring A] [Algebra F A] (a : F)
    (p : Polynomial F) (x : A) : evalTensorAlg a (p ⊗ₜ[F] x) = p.eval a • x :=
  (evalTensorAlg_apply a _).trans (evalTensor_tmul a p x)

private theorem evalTensorAlg_quadratic {A : Type*} [Ring A] [Algebra F A] (a : F) (x y : A) :
    evalTensorAlg a (1 + Polynomial.X ⊗ₜ[F] x + (Polynomial.X ^ 2) ⊗ₜ[F] y) =
      1 + a • x + a ^ 2 • y := by
  simp only [map_add, map_one, evalTensorAlg_tmul, Polynomial.eval_X, Polynomial.eval_pow]

private theorem algEquiv_quadratic {A C : Type*} [Ring A] [Algebra F A] [Ring C] [Algebra F C]
    (e : A ≃ₐ[F] C) (a : F) (x y : C) :
    e (1 + a • e.symm x + a ^ 2 • e.symm y) = 1 + a • x + a ^ 2 • y := by
  simp only [map_add, map_one, map_smul, AlgEquiv.apply_symm_apply]

private theorem eval_shearPolynomialValue (Q : QuaternionHyperbolicPresentation D hB d)
    (W : ComplementRefinement Q) (rev : Bool) (w : Fin d → B) (b : B) (a : F) :
    evalTensorAlg a (shearPolynomialValue Q W rev w b) =
      Q.matrixModel.symm (shearMatrix rev W.pairing (a • w) (a ^ 2 • b)) := by
  rw [shearPolynomialValue, evalTensorAlg_quadratic]
  apply Q.matrixModel.injective
  rw [algEquiv_quadratic, AlgEquiv.apply_symm_apply]
  apply matrix_eq_of_mulVec
  intro p
  obtain ⟨p, rfl⟩ := orientedColumn_surjective rev p
  rw [shear_scaled_action, shear_matrix_action]

private def shearPolynomialUnit [Infinite F] (Q : QuaternionHyperbolicPresentation D hB d)
    (W : ComplementRefinement Q) (rev : Bool) (w : Fin d → B) (b : B) :
    (Polynomial F ⊗[F] ρ.fixedSubalgebra)ˣ := by
  have h (a : F) : a ^ 2 • (b + W.pairing.value w w) =
      a ^ 2 • b + W.pairing.value (a • w) (a • w) := by
    rw [smul_add, hermitian_smul_center_left, hermitian_smul_center_right, smul_smul, pow_two]
  refine ⟨shearPolynomialValue Q W rev w b,
    shearPolynomialValue Q W rev w (b + W.pairing.value w w), ?_, ?_⟩
  · apply tensorPolynomial_ext
    intro a
    rw [← evalTensorAlg_apply, ← evalTensorAlg_apply, map_mul, map_one,
      eval_shearPolynomialValue, eval_shearPolynomialValue, h]
    apply Q.matrixModel.injective
    simp only [map_mul, map_one, AlgEquiv.apply_symm_apply]
    exact (shearUnit rev W.pairing (a • w) (a ^ 2 • b)).val_inv
  · apply tensorPolynomial_ext
    intro a
    rw [← evalTensorAlg_apply, ← evalTensorAlg_apply, map_mul, map_one,
      eval_shearPolynomialValue, eval_shearPolynomialValue, h]
    apply Q.matrixModel.injective
    simp only [map_mul, map_one, AlgEquiv.apply_symm_apply]
    exact (shearUnit rev W.pairing (a • w) (a ^ 2 • b)).inv_val

private theorem eval_shearPolynomialUnit [Infinite F] (Q : QuaternionHyperbolicPresentation D hB d)
    (W : ComplementRefinement Q) (rev : Bool) (w : Fin d → B) (b : B) (a : F) :
    Units.map (evalTensorAlg a).toMonoidHom (shearPolynomialUnit Q W rev w b) =
      Units.map Q.matrixModel.symm.toMonoidHom (shearUnit rev W.pairing (a • w) (a ^ 2 • b)) :=
  Units.ext (eval_shearPolynomialValue Q W rev w b a)

private theorem local_parameter [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : ∃ r : Fˣ, r.val ≠ 1 ∧ Infinite F := by
  obtain ⟨a, ha0, ha⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  have ha1 : a ≠ 1 := fun h => by rw [h, map_one] at ha; exact (lt_irrefl _ ha)
  have hp : 0 < valuation F a := pos_iff_ne_zero.mpr (by simpa using ha0)
  refine ⟨Units.mk0 a ha0, ha1, Infinite.of_injective (fun n : ℕ => a ^ n) ?_⟩
  intro m n h
  apply (pow_right_strictAnti₀ hp ha).injective
  simpa only [← map_pow] using congrArg (valuation F) h

private theorem evalLaurent_polynomial (r : Fˣ) :
    polynomialToLaurent (fieldAlgebra F) ≫ evalLaurent (𝟙 (fieldAlgebra F)) r =
      polynomialEvaluate (fieldAlgebra F) (r : F) := by
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  change (evalLaurent (𝟙 (fieldAlgebra F)) r).hom (Polynomial.X : Polynomial F).toLaurent =
    Polynomial.aevalTower (AlgHom.id F F) (r : F) Polynomial.X
  rw [Polynomial.toLaurent_X, Polynomial.aevalTower_X]
  change LaurentPolynomial.eval₂ (CommAlgCat.Hom.hom (𝟙 (fieldAlgebra F))).toRingHom r
    (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]

private theorem laurent_eval_ext [Infinite F] {p q : LaurentPolynomial F}
    (h : ∀ r : Fˣ, (evalLaurent (𝟙 (fieldAlgebra F)) r).hom p =
      (evalLaurent (𝟙 (fieldAlgebra F)) r).hom q) : p = q := by
  obtain ⟨n, g, hg⟩ := LaurentPolynomial.exists_T_pow (p - q)
  have hzero : g = 0 := by
    apply polynomial_ext_of_eval
    intro a ha
    let r := Units.mk0 a ha
    let e := evalLaurent (𝟙 (fieldAlgebra F)) r
    have he : e.hom g.toLaurent = g.eval a := by
      have h' := DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (evalLaurent_polynomial r)) g
      change e.hom g.toLaurent = Polynomial.aevalTower (AlgHom.id F F) a g at h'
      simpa only [Polynomial.aevalTower_id, Polynomial.coe_aeval_eq_eval] using h'
    rw [← he, hg, map_mul, map_sub, h r, sub_self, zero_mul, Polynomial.eval_zero]
  rw [hzero, map_zero] at hg
  apply sub_eq_zero.mp
  have h' := congrArg (fun f : LaurentPolynomial F => f * LaurentPolynomial.T (-(n : ℤ))) hg
  simpa only [zero_mul, LaurentPolynomial.mul_T_assoc, add_neg_cancel,
    LaurentPolynomial.T_zero, mul_one] using h'.symm

private theorem laurent_point_ext [Infinite F] {X : SchemeOver F} (ha : IsAffine X.left)
    {x y : Points X (laurentAlgebra (fieldAlgebra F))}
    (h : ∀ r : Fˣ, mapPoints (evalLaurent (𝟙 (fieldAlgebra F)) r) x =
      mapPoints (evalLaurent (𝟙 (fieldAlgebra F)) r) y) : x = y := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of F)).mpr ha
  let E := algSpec.fullyFaithful (R := CommRingCat.of F)
  let x' := E.preimage (x ≫ e.inv)
  let y' := E.preimage (y ≫ e.inv)
  have hx : (testSpec F).map x' = x ≫ e.inv := E.map_preimage _
  have hy : (testSpec F).map y' = y ≫ e.inv := E.map_preimage _
  have hh (r : Fˣ) : (evalLaurent (𝟙 (fieldAlgebra F)) r).op ≫ x' =
      (evalLaurent (𝟙 (fieldAlgebra F)) r).op ≫ y' := by
    apply E.map_injective
    rw [Functor.map_comp, Functor.map_comp, hx, hy]
    simpa only [mapPoints, Category.assoc] using congrArg (· ≫ e.inv) (h r)
  have he : x' = y' := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    exact laurent_eval_ext fun r =>
      DFunLike.congr_fun (congrArg (fun f => f.unop.hom) (hh r)) z
  apply (cancel_mono e.inv).mp
  rw [← hx, ← hy, he]

private def orientedCocharacter (rev : Bool) (c : Cocharacter G.val) : Cocharacter G.val :=
  if rev then oppositeCocharacter c else c

private def orientedDiagonal (rev : Bool) (r : Fˣ) :
    Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B :=
  Matrix.diagonal (algebraMap F B ∘ pairWeights (if rev then r⁻¹ else r))

private theorem oriented_diagonal_action (rev : Bool) (r : Fˣ) (p : PairColumns B d) :
    orientedDiagonal rev r *ᵥ orientedColumn rev p =
      orientedColumn rev ((r : F) • p.1, p.2.1, (↑r⁻¹ : F) • p.2.2) := by
  funext i
  rw [orientedDiagonal, Matrix.mulVec_diagonal]
  rcases i with i | i
  · fin_cases i <;> cases rev <;> simp [orientedColumn, column, pairWeights, Algebra.smul_def]
  · cases rev <;> simp [orientedColumn, column, pairWeights]

private theorem diagonal_conjugates_shear {s : AntiEquiv F B}
    (rev : Bool) (h : HermitianPairing s (Fin d → B)) (r : Fˣ) (w : Fin d → B) (b : B) :
    orientedDiagonal rev r * shearMatrix rev h w b * orientedDiagonal rev r⁻¹ =
      shearMatrix rev h ((r : F) • w) ((r : F) ^ 2 • b) := by
  apply matrix_eq_of_mulVec
  intro p
  obtain ⟨⟨x, y, z⟩, rfl⟩ := orientedColumn_surjective rev p
  rw [← mulVec_mulVec, ← mulVec_mulVec, oriented_diagonal_action, shear_matrix_action,
    oriented_diagonal_action, shear_matrix_action, inv_inv]
  apply congrArg (orientedColumn rev)
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change (r : F) • ((↑r⁻¹ : F) • x + h.value w y + b * ((r : F) • z)) =
      x + h.value ((r : F) • w) y + ((r : F) ^ 2 • b) * z
    rw [smul_add, smul_add, smul_smul, show (r : F) * (↑r⁻¹ : F) = 1 from r.val_inv,
      one_smul, hermitian_smul_center_left,
      mul_smul_comm, smul_smul, ← pow_two, smul_mul_assoc]
  · funext j
    change y j + w j * ((r : F) • z) = y j + ((r : F) • w j) * z
    rw [mul_smul_comm, smul_mul_assoc]
  · change (↑r⁻¹ : F) • ((r : F) • z) = z
    rw [smul_smul, show (↑r⁻¹ : F) * (r : F) = 1 from r.inv_val, one_smul]

private theorem diagonal_shear_commutator {s : AntiEquiv F B}
    (rev : Bool) (h : HermitianPairing s (Fin d → B)) (r : Fˣ) (w : Fin d → B) (b : B) :
    orientedDiagonal rev r * (shearUnit rev h w b).val * orientedDiagonal rev r⁻¹ *
        (shearUnit rev h w b).inv =
      shearMatrix rev h (((r : F) + 1) • w)
        (((r : F) + 1) ^ 2 • b + ((r : F) + 1) • h.value w w) := by
  change orientedDiagonal rev r * shearMatrix rev h w b * orientedDiagonal rev r⁻¹ *
    shearMatrix rev h w (b + h.value w w) = _
  rw [diagonal_conjugates_shear, shear_matrix_mul, hermitian_smul_center_left]
  have hs : ((r : F) + 1) ^ 2 = (r : F) ^ 2 + 1 := by
    simp [add_sq, CharTwo.two_eq_zero]
  rw [add_smul, one_smul, hs, add_smul, one_smul, add_smul, one_smul]
  congr 1
  abel

private theorem shear_commutator_parameters {s : AntiEquiv F B}
    (h : HermitianPairing s (Fin d → B)) (ell : (Fin d → B) →ₗ[Bᵐᵒᵖ] (Fin d → B))
    (r : Fˣ) (hr : (r : F) ≠ 1) (w : Fin d → B) (b : B)
    (hb : scalarClass F b = refinement h ell w) :
    ∃ v a, scalarClass F a = refinement h ell v ∧
      ∀ t : F, ((r : F) + 1) • (t • v) = t • w ∧
        ((r : F) + 1) ^ 2 • (t ^ 2 • a) + ((r : F) + 1) • h.value (t • v) (t • v) =
          t ^ 2 • b := by
  let k := (r : F) + 1
  have hk : k ≠ 0 := fun h => hr (CharTwo.add_eq_zero.mp h)
  let v := k⁻¹ • w
  let a := k⁻¹ ^ 2 • b + k⁻¹ • h.value v v
  have hv : k • v = w := by
    change k • (k⁻¹ • w) = w
    rw [smul_smul, mul_inv_cancel₀ hk, one_smul]
  have ha : k ^ 2 • a + k • h.value v v = b := by
    change k ^ 2 • (k⁻¹ ^ 2 • b + k⁻¹ • h.value v v) + k • h.value v v = b
    rw [smul_add, smul_smul, ← mul_pow, mul_inv_cancel₀ hk, one_pow, one_smul,
      smul_smul, pow_two, mul_assoc, mul_inv_cancel₀ hk, mul_one, add_assoc,
      add_self_quaternion (F := F), add_zero]
  refine ⟨v, a, ?_, fun t => ⟨?_, ?_⟩⟩
  · have hz : scalarClass F (h.value v v) = 0 := by
      obtain ⟨q, hq⟩ := h.central_norm v
      rw [hq, class_scalar]
    change scalarClass F (k⁻¹ ^ 2 • b + k⁻¹ • h.value v v) = refinement h ell v
    simp only [map_add, map_smul, hz, smul_zero, add_zero]
    exact scaled_admissible h ell hb k⁻¹
  · change k • (t • v) = t • w
    rw [smul_comm k t, hv]
  · change k ^ 2 • (t ^ 2 • a) + k • h.value (t • v) (t • v) = t ^ 2 • b
    rw [hermitian_smul_center_left, hermitian_smul_center_right, smul_smul t t, ← pow_two,
      smul_comm (k ^ 2) (t ^ 2), smul_comm k (t ^ 2), ← smul_add, ha]

private def fullRationalMatrix (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d) :
    Points M.full.val.X (fieldAlgebra F) →* (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)ˣ :=
  (Units.map (Q.matrixModel.toMonoidHom.comp
    (Algebra.TensorProduct.lid F ρ.fixedSubalgebra).toMonoidHom)).comp
    (M.fullPoints (fieldAlgebra F))

private def rationalMatrix (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d) :
    GroupPoints G.val (fieldAlgebra F) →* (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)ˣ :=
  (fullRationalMatrix M Q).comp
    (((groupPointsFunctor F).map (M.projection ≫ M.inclusion)).app (fieldAlgebra F)).hom

private theorem rationalMatrix_injective (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) : Function.Injective (rationalMatrix M Q) := by
  intro g h he
  apply spin_projection_injective M (fieldAlgebra F)
  apply Units.ext
  exact (Algebra.TensorProduct.lid F ρ.fixedSubalgebra).injective
    (Q.matrixModel.injective (congrArg Units.val he))

private theorem rationalMatrix_diagonal (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (c : Cocharacter G.val)
    (hc : IsPairDiagonal M Q c) (rev : Bool) (r : Fˣ) :
    (rationalMatrix M Q (cocharacterPoint (orientedCocharacter rev c) (fieldAlgebra F) r)).val =
      orientedDiagonal rev r := by
  cases rev
  · exact rational_pair_diagonal M Q hc r
  · change (rationalMatrix M Q (cocharacterPoint (oppositeCocharacter c) (fieldAlgebra F) r)).val =
      orientedDiagonal true r
    rw [opposite_point]
    exact rational_pair_diagonal M Q hc r⁻¹

private theorem rationalMatrix_diagonal_inv (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (c : Cocharacter G.val)
    (hc : IsPairDiagonal M Q c) (rev : Bool) (r : Fˣ) :
    (rationalMatrix M Q (cocharacterPoint (orientedCocharacter rev c) (fieldAlgebra F) r)).inv =
      orientedDiagonal rev r⁻¹ := by
  let e := (((groupPointsFunctor F).map (orientedCocharacter rev c)).app (fieldAlgebra F)).hom
  have hi : cocharacterPoint (orientedCocharacter rev c) (fieldAlgebra F) r⁻¹ =
      (cocharacterPoint (orientedCocharacter rev c) (fieldAlgebra F) r)⁻¹ := by
    change e (unitPoint (fieldAlgebra F) r⁻¹) = (e (unitPoint (fieldAlgebra F) r))⁻¹
    rw [unitPoint_inv, map_inv]
  change ((rationalMatrix M Q (cocharacterPoint (orientedCocharacter rev c) (fieldAlgebra F) r))⁻¹).val = _
  rw [← map_inv, ← hi, rationalMatrix_diagonal M Q c hc]

private theorem rationalMatrix_conjugates_shear (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) (c : Cocharacter G.val)
    (hc : IsPairDiagonal M Q c) (W : ComplementRefinement Q) (rev : Bool) (r : Fˣ)
    (g : GroupPoints G.val (fieldAlgebra F)) (w : Fin d → B) (b : B)
    (hg : (rationalMatrix M Q g).val = shearMatrix rev W.pairing w b) :
    let t := cocharacterPoint (orientedCocharacter rev c) (fieldAlgebra F) r
    (rationalMatrix M Q (t * g * t⁻¹)).val =
      shearMatrix rev W.pairing ((r : F) • w) ((r : F) ^ 2 • b) := by
  let t := cocharacterPoint (orientedCocharacter rev c) (fieldAlgebra F) r
  change (rationalMatrix M Q (t * g * t⁻¹)).val = _
  rw [map_mul, map_mul, map_inv]
  change (rationalMatrix M Q t).val * (rationalMatrix M Q g).val * (rationalMatrix M Q t).inv = _
  rw [rationalMatrix_diagonal M Q c hc, rationalMatrix_diagonal_inv M Q c hc, hg,
    diagonal_conjugates_shear]

private theorem field_evaluation (a : F) :
    (polynomialEvaluate (fieldAlgebra F) a).hom = Polynomial.aeval a := by
  change Polynomial.aevalTower (AlgHom.id F F) a = Polynomial.aeval a
  rw [Polynomial.aevalTower_id]

private theorem shear_neutral_family [Infinite F] (hrec : QuaternionPairRecovery.{u})
    (href : RefinementIdentities.{u,u,u}) (hdeg : degree F B = 2)
    (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    (W : ComplementRefinement Q) (rev : Bool) (w : Fin d → B) (b : B)
    (hb : scalarClass F b = refinement W.pairing W.complementAction w) :
    ∃ y : Points M.neutral.val.X (polynomialAlgebra (fieldAlgebra F)), ∀ a : F,
      (fullRationalMatrix M Q (mapPoints (polynomialEvaluate (fieldAlgebra F) a) y ≫
        M.inclusion.hom.hom)).val = shearMatrix rev W.pairing (a • w) (a ^ 2 • b) := by
  let R := fieldAlgebra F
  let P := polynomialAlgebra R
  let U := shearPolynomialUnit Q W rev w b
  have hU : IsPairIsometry D P U := by
    apply polynomial_pair_isometry
    intro a
    rw [eval_shearPolynomialUnit]
    exact shear_rational_isometry hrec href hdeg Q W rev (a • w) (a ^ 2 • b)
      (scaled_admissible W.pairing W.complementAction hb a)
  obtain ⟨p, hp⟩ := (M.fullRange P U).mpr hU
  have he (a : F) :
      (Algebra.TensorProduct.lid F ρ.fixedSubalgebra
        (M.fullPoints R (mapPoints (polynomialEvaluate R a) p)).val) =
          Q.matrixModel.symm (shearMatrix rev W.pairing (a • w) (a ^ 2 • b)) := by
    rw [M.fullNatural, hp]
    change Algebra.TensorProduct.lid F ρ.fixedSubalgebra
      (tensorMap ρ.fixedSubalgebra (polynomialEvaluate R a).hom U.val) = _
    rw [field_evaluation]
    exact eval_shearPolynomialValue Q W rev w b a
  have h0 : mapPoints (polynomialEvaluate R 0) p = 1 := by
    apply M.fullFaithful R
    rw [map_one]
    apply Units.ext
    apply (Algebra.TensorProduct.lid F ρ.fixedSubalgebra).injective
    rw [he 0]
    simp only [zero_smul, zero_pow (by decide : 2 ≠ 0), shear_matrix_one, map_one, Units.val_one]
  obtain ⟨y, hy⟩ := polynomial_point_neutral M p h0
  refine ⟨y, fun a => ?_⟩
  have hpy : mapPoints (polynomialEvaluate R a) y ≫ M.inclusion.hom.hom =
      mapPoints (polynomialEvaluate R a) p := by
    rw [← hy, Category.assoc]
  change Q.matrixModel (Algebra.TensorProduct.lid F ρ.fixedSubalgebra
    (M.fullPoints R (mapPoints (polynomialEvaluate R a) y ≫ M.inclusion.hom.hom)).val) = _
  rw [hpy, he a, AlgEquiv.apply_symm_apply]

private def fieldPointIso (F : Type u) [Field F] :
    (𝟙_ (SchemeOver F)) ≅ (testSpec F).obj (Opposite.op (fieldAlgebra F)) := by
  refine Over.isoMk (Iso.refl (Spec (CommRingCat.of F))) ?_
  change 𝟙 (Spec (CommRingCat.of F)) ≫ Spec.map (CommRingCat.ofHom (algebraMap F F)) = 𝟙 _
  have hm : CommRingCat.ofHom (algebraMap F F) = 𝟙 (CommRingCat.of F) := by
    ext x
    rfl
  rw [hm, Spec.map_id, Category.id_comp]

/-- The descended commutator gives a polynomial spin point. Its specialization is
computed in the full vector group, where both factors are defined. -/
private theorem commutator_family (M : SpinModel G D) (t : Points G.val.X (fieldAlgebra F))
    (y : Points M.neutral.val.X (polynomialAlgebra (fieldAlgebra F))) :
    ∃ A : Points G.val.X (polynomialAlgebra (fieldAlgebra F)), ∀ a : F,
      let v := t ≫ (M.projection ≫ M.inclusion).hom.hom
      let z := mapPoints (polynomialEvaluate (fieldAlgebra F) a) y ≫ M.inclusion.hom.hom
      mapPoints (polynomialEvaluate (fieldAlgebra F) a) A ≫ (M.projection ≫ M.inclusion).hom.hom =
        v * z * v⁻¹ * z⁻¹ := by
  let R := fieldAlgebra F
  let S := (testSpec F).obj (Opposite.op R)
  let T := (testSpec F).obj (Opposite.op (polynomialAlgebra R))
  let E := fieldPointIso F
  let p := M.projection.hom.hom
  obtain ⟨A, hA⟩ := lift_vector_commutator M (E.hom ≫ t) y
  let τ : T ⟶ M.neutral.val.X := toUnit T ≫ (E.hom ≫ t) ≫ p
  change A ≫ p = τ * y * τ⁻¹ * y⁻¹ at hA
  refine ⟨A, fun a => ?_⟩
  let x := (testSpec F).map (polynomialEvaluate R a).op
  have ht : toUnit S ≫ E.hom ≫ t ≫ p = t ≫ p := by
    rw [show toUnit S = E.inv from toUnit_unique _ _, E.inv_hom_id_assoc]
  have he : x ≫ τ = t ≫ p := by
    change x ≫ toUnit T ≫ (E.hom ≫ t) ≫ p = _
    rw [← Category.assoc x (toUnit T), show x ≫ toUnit T = toUnit S from toUnit_unique _ _,
      Category.assoc E.hom t, ht]
  have hz : (x ≫ A) ≫ p = (t ≫ p) * (x ≫ y) * (t ≫ p)⁻¹ * (x ≫ y)⁻¹ := by
    rw [Category.assoc, hA]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, he]
  let i := M.inclusion.hom.hom
  change (x ≫ A) ≫ p ≫ i = (t ≫ p ≫ i) * ((x ≫ y) ≫ i) *
    (t ≫ p ≫ i)⁻¹ * ((x ≫ y) ≫ i)⁻¹
  have h := congrArg (fun z => z ≫ M.inclusion.hom.hom) hz
  simpa only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc] using h

private theorem lift_shear_family [Infinite F] (hrec : QuaternionPairRecovery.{u})
    (href : RefinementIdentities.{u,u,u}) (hdeg : degree F B = 2)
    (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d) (c : Cocharacter G.val)
    (hc : IsPairDiagonal M Q c) (W : ComplementRefinement Q) (rev : Bool)
    (r : Fˣ) (hr : (r : F) ≠ 1) (w : Fin d → B) (b : B)
    (hb : scalarClass F b = refinement W.pairing W.complementAction w) :
    ∃ A : Points G.val.X (polynomialAlgebra (fieldAlgebra F)), ∀ a : F,
      (rationalMatrix M Q (mapPoints (polynomialEvaluate (fieldAlgebra F) a) A)).val =
        shearMatrix rev W.pairing (a • w) (a ^ 2 • b) := by
  obtain ⟨v, b', hb', hparams⟩ := shear_commutator_parameters W.pairing W.complementAction r hr w b hb
  obtain ⟨y, hy⟩ := shear_neutral_family hrec href hdeg M Q W rev v b' hb'
  let t := cocharacterPoint (orientedCocharacter rev c) (fieldAlgebra F) r
  obtain ⟨A, hA⟩ := commutator_family M t y
  refine ⟨A, fun a => ?_⟩
  let T := rationalMatrix M Q t
  let S := fullRationalMatrix M Q (mapPoints (polynomialEvaluate (fieldAlgebra F) a) y ≫
    M.inclusion.hom.hom)
  have h := congrArg (fun x => (fullRationalMatrix M Q x).val) (hA a)
  simp only [map_mul, map_inv] at h
  change (rationalMatrix M Q (mapPoints (polynomialEvaluate (fieldAlgebra F) a) A)).val =
    T.val * S.val * T.inv * S.inv at h
  have hS : S = shearUnit rev W.pairing (a • v) (a ^ 2 • b') := Units.ext (hy a)
  have hT : T.val = orientedDiagonal rev r := rationalMatrix_diagonal M Q c hc rev r
  have hTi : T.inv = orientedDiagonal rev r⁻¹ := rationalMatrix_diagonal_inv M Q c hc rev r
  rw [h, hT, hTi, hS, diagonal_shear_commutator, (hparams a).1, (hparams a).2]

private theorem contracting_shear [Infinite F] (hrec : QuaternionPairRecovery.{u})
    (href : RefinementIdentities.{u,u,u}) (hdeg : degree F B = 2)
    (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d) (c : Cocharacter G.val)
    (hc : IsPairDiagonal M Q c) (W : ComplementRefinement Q) (rev : Bool)
    (r : Fˣ) (hr : (r : F) ≠ 1) (w : Fin d → B) (b : B)
    (hb : scalarClass F b = refinement W.pairing W.complementAction w) :
    ∃ g : GroupPoints G.val (fieldAlgebra F),
      HasLimit (orientedCocharacter rev c) g 1 ∧
      (rationalMatrix M Q g).val = shearMatrix rev W.pairing w b := by
  obtain ⟨A, hA⟩ := lift_shear_family hrec href hdeg M Q c hc W rev r hr w b hb
  let R := fieldAlgebra F
  let g : GroupPoints G.val R := mapPoints (polynomialEvaluate R 1) A
  have hg : (rationalMatrix M Q g).val = shearMatrix rev W.pairing w b := by
    simpa only [g, one_smul, one_pow] using hA (1 : F)
  refine ⟨g, ⟨A, ?_, ?_⟩, hg⟩
  · apply laurent_point_ext G.2.1
    intro s
    rw [← mapPoints_comp, evalLaurent_polynomial,
      orbit_eval (𝟙 R) s (orientedCocharacter rev c) g]
    let g' : Points G.val.X R := g
    have hi : mapPoints (𝟙 R) g = g := by
      change (testSpec F).map (𝟙 (Opposite.op R)) ≫ g' = g'
      rw [(testSpec F).map_id, Category.id_comp]
    rw [hi]
    apply rationalMatrix_injective M Q
    apply Units.ext
    exact (hA (s : F)).trans (rationalMatrix_conjugates_shear M Q c hc W rev s g w b hg).symm
  · apply rationalMatrix_injective M Q
    rw [map_one]
    apply Units.ext
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_smul, shear_matrix_one, Units.val_one] using hA (0 : F)

private theorem opposite_columns (hrec : QuaternionPairRecovery.{u})
    (href : RefinementIdentities.{u,u,u}) : OppositeColumnActions.{u} := by
  intro F K I B _ _ _ _ _ _ _ _ _ _ _ _ _ ρ G D M _ hB hdeg d Q c hc W w b hb
  obtain ⟨r, hr, hinf⟩ := local_parameter (F := F)
  letI : Infinite F := hinf
  obtain ⟨gPlus, hPlus, hU⟩ := contracting_shear hrec href hdeg M Q c hc W false r hr w b hb
  obtain ⟨gMinus, hMinus, hL⟩ := contracting_shear hrec href hdeg M Q c hc W true r hr w b hb
  refine ⟨gPlus, gMinus, hPlus, hMinus, ?_, ?_⟩
  · apply rational_column_action M Q
    rintro ⟨x, y, z⟩
    change (rationalMatrix M Q gPlus).val *ᵥ column x y z = _
    rw [hU]
    exact shear_matrix_action false W.pairing w b (x, y, z)
  · apply rational_column_action M Q
    rintro ⟨x, y, z⟩
    change (rationalMatrix M Q gMinus).val *ᵥ column x y z = _
    rw [hL]
    exact shear_matrix_action true W.pairing w b (z, y, x)

private theorem pair_diagonal_noncentral (hrec : QuaternionPairRecovery.{u})
    (href : RefinementIdentities.{u,u,u}) : PairDiagonalNoncentral.{u} := by
  intro F K I B _ _ _ _ _ _ _ _ _ _ _ _ _ ρ G D M _ hB hdeg d Q c hc
  obtain ⟨r, hr, hinf⟩ := local_parameter (F := F)
  letI : Infinite F := hinf
  obtain ⟨W⟩ := recover hdeg Q
  have hb : scalarClass F (1 : B) = refinement W.pairing W.complementAction 0 := by
    rw [refinement, map_zero W.complementAction, hermitian_zero_right, map_zero]
    simpa only [map_one] using class_scalar (B := B) (1 : F)
  obtain ⟨g, _, hg⟩ := contracting_shear hrec href hdeg M Q c hc W false r hr 0 1 hb
  let R := fieldAlgebra F
  let t := cocharacterPoint c R r
  refine ⟨(testSpec F).obj (Opposite.op R), g, fun h => ?_⟩
  have hcomm : Commute g t := by
    let g' : Points G.val.X R := g
    change Commute g' (unitPoint R r ≫ c.hom.hom)
    have h' := (centralizes_iff c g').mp h _ (𝟙 _) (unitPoint R r)
    simpa only [Category.id_comp g'] using h'
  have hfix : t * g * t⁻¹ = g := by rw [hcomm.eq.symm, mul_assoc, mul_inv_cancel, mul_one]
  have hconj := rationalMatrix_conjugates_shear M Q c hc W false r g 0 1 hg
  change (rationalMatrix M Q (t * g * t⁻¹)).val =
    shearMatrix false W.pairing ((r : F) • 0) ((r : F) ^ 2 • 1) at hconj
  rw [hfix, hg, smul_zero] at hconj
  have hvec := congrArg (fun A => A *ᵥ orientedColumn false ((0, 0, 1) : PairColumns B d)) hconj
  rw [shear_matrix_action, shear_matrix_action] at hvec
  have hcoeff := congrArg Prod.fst (orientedColumn_injective false hvec)
  have hs : (r : F) ^ 2 = 1 := (algebraMap F B).injective (by
    simpa [plusShear, hermitian_zero_right, Algebra.smul_def] using hcoeff.symm)
  have hzero : ((r : F) + 1) ^ 2 = 0 := by
    simp [add_sq, CharTwo.two_eq_zero, hs, CharTwo.add_self_eq_zero]
  exact hr (CharTwo.add_eq_zero.mp (eq_zero_of_pow_eq_zero hzero))

open LinearAlgebraicGroups.Arithmetic.CharacteristicTwoQuadraticPairs
  (arithmeticQuaternionIsotropy quaternionPairRecovery refinementIdentities)

theorem recoverComplement : RecoverComplement.{u} := by
  intro F K I B _ _ _ _ _ _ _ _ ρ D hB hdeg d Q
  exact recover hdeg Q

theorem oppositeColumnActions : OppositeColumnActions.{u} :=
  opposite_columns quaternionPairRecovery refinementIdentities

theorem centralizerColumns : CentralizerColumns.{u} :=
  centralizer quaternionPairRecovery

theorem pairDiagonalNoncentral : PairDiagonalNoncentral.{u} :=
  pair_diagonal_noncentral quaternionPairRecovery refinementIdentities

theorem arithmeticPresentation : ArithmeticPresentation.{u} :=
  arithmetic arithmeticQuaternionIsotropy quaternionPairRecovery

end

end LinearAlgebraicGroups.Arithmetic.QuaternionHyperbolicRadicals
