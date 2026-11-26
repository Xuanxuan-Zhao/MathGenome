import Specs.LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SkolemNoether
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Degree
import MathGenome.Internal.D05.M11.SymplecticBlocks

open scoped TensorProduct Matrix
open Matrix MulOpposite

universe u v w z q

namespace LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

open Specs.SymplecticDivisionForms

noncomputable section

variable {F R D A : Type*} [CommRing F] [CommRing R] [Algebra F R]
  [Ring A] [Algebra F A] [Ring D] [Algebra F D]

@[simp] private theorem antiValue_add {K C : Type*} [CommRing K] [Ring C] [Algebra K C]
    (s : AntiEquiv K C) (x y : C) :
    antiValue s (x + y) = antiValue s x + antiValue s y := by
  simp [antiValue]

@[simp] private theorem antiValue_mul {K C : Type*} [CommRing K] [Ring C] [Algebra K C]
    (s : AntiEquiv K C) (x y : C) :
    antiValue s (x * y) = antiValue s y * antiValue s x := by
  simp [antiValue]

@[simp] private theorem antiValue_zero {K C : Type*} [CommRing K] [Ring C] [Algebra K C]
    (s : AntiEquiv K C) : antiValue s 0 = 0 := by simp [antiValue]

@[simp] private theorem antiValue_one {K C : Type*} [CommRing K] [Ring C] [Algebra K C]
    (s : AntiEquiv K C) : antiValue s 1 = 1 := by simp [antiValue]

@[simp] private theorem antiValue_sum {K C I : Type*} [CommRing K] [Ring C] [Algebra K C]
    (s : AntiEquiv K C) (t : Finset I) (f : I → C) :
    antiValue s (∑ i ∈ t, f i) = ∑ i ∈ t, antiValue s (f i) := by
  simp [antiValue, Finset.unop_sum]

@[simp] private theorem antiValue_smul {K C : Type*} [CommRing K] [Ring C] [Algebra K C]
    (s : AntiEquiv K C) (a : K) (x : C) :
    antiValue s (a • x) = a • antiValue s x := by
  simp [antiValue]

@[simp] private theorem extendAnti_tmul (s : AntiEquiv F A) (t : R) (x : A) :
    antiValue (extendAnti s R) (t ⊗ₜ[F] x) = t ⊗ₜ[F] antiValue s x := by
  simp [extendAnti, antiValue]

private def extendEquiv (e : A ≃ₐ[F] D) :
    (R ⊗[F] A) ≃ₐ[R] (R ⊗[F] D) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e

@[simp] private theorem extendEquiv_tmul (e : A ≃ₐ[F] D) (t : R) (x : A) :
    extendEquiv e (t ⊗ₜ[F] x) = t ⊗ₜ[F] e x := by simp [extendEquiv]

private def matrixBaseChange (I : Type*) [Fintype I] [DecidableEq I] :
    (R ⊗[F] Matrix I I D) ≃ₐ[R] Matrix I I (R ⊗[F] D) :=
  (extendEquiv (matrixEquivTensor I F D)).trans
    ((Algebra.TensorProduct.assoc F F R R D (Matrix I I F)).symm.trans
      (AlgEquiv.ofRingEquiv
        (f := (matrixEquivTensor I F (R ⊗[F] D)).symm.toRingEquiv)
        (fun t => by
          change (matrixEquivTensor I F (R ⊗[F] D)).symm
            ((t ⊗ₜ[F] (1 : D)) ⊗ₜ[F] (1 : Matrix I I F)) = _
          rw [matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _)]
          ext i j
          rw [Matrix.smul_apply, smul_eq_mul, Matrix.algebraMap_matrix_apply]
          by_cases hij : i = j <;> simp [Matrix.one_apply, hij])))

@[simp] private theorem matrixBaseChange_tmul {I : Type*} [Fintype I] [DecidableEq I]
    (t : R) (X : Matrix I I D) :
    matrixBaseChange I (t ⊗ₜ[F] X) = X.map (fun d => t ⊗ₜ[F] d) := by
  ext i j
  simp only [matrixBaseChange, AlgEquiv.trans_apply, extendEquiv_tmul,
    matrixEquivTensor_apply, TensorProduct.tmul_sum, map_sum,
    Algebra.TensorProduct.assoc_symm_tmul]
  simp [matrixEquivTensor_apply_symm, Matrix.single, Matrix.sum_apply,
    Fintype.sum_prod_type, ite_and, Matrix.map_apply, Matrix.smul_apply, eq_comm, apply_ite]

private def scalarMatrixBaseChange (I : Type*) [Fintype I] [DecidableEq I] :
    (R ⊗[F] Matrix I I F) ≃ₐ[R] Matrix I I R :=
  (matrixBaseChange I).trans (Algebra.TensorProduct.rid F R R |>.mapMatrix)

@[simp] private theorem scalarMatrixBaseChange_tmul {I : Type*} [Fintype I] [DecidableEq I]
    (t : R) (X : Matrix I I F) :
    scalarMatrixBaseChange I (t ⊗ₜ[F] X) = t • X.map (algebraMap F R) := by
  ext i j
  simp [scalarMatrixBaseChange, Matrix.map_apply, Algebra.smul_def, mul_comm]

private theorem matrixBaseChange_natural {I : Type*} [Fintype I] [DecidableEq I]
    {S : Type*} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (e : A ≃ₐ[F] Matrix I I D) (x : R ⊗[F] A) :
    matrixBaseChange I (extendEquiv e (tensorMap A f x)) =
      (matrixBaseChange I (extendEquiv e x)).map (tensorMap D f) := by
  induction x using TensorProduct.inductionOn with
  | tmul t a => ext i j; simp [tensorMap]
  | add x y hx hy => simp [hx, hy, Matrix.map_add]

private theorem scalarMatrixBaseChange_natural {I : Type*} [Fintype I] [DecidableEq I]
    {S : Type*} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (e : A ≃ₐ[F] Matrix I I F) (x : R ⊗[F] A) :
    scalarMatrixBaseChange I (extendEquiv e (tensorMap A f x)) =
      (scalarMatrixBaseChange I (extendEquiv e x)).map f := by
  induction x using TensorProduct.inductionOn with
  | tmul t a =>
    ext i j
    simp [tensorMap, Matrix.smul_apply, smul_eq_mul]
  | add x y hx hy => simp [hx, hy, Matrix.map_add]

private def matrixOpposite (I : Type*) [Fintype I] [DecidableEq I] :
    (Matrix I I D)ᵐᵒᵖ ≃ₐ[F] Matrix I I Dᵐᵒᵖ where
  toFun x i j := op (unop x j i)
  invFun x := op (fun i j => unop (x j i))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    ext i j
    change op ((unop y * unop x) j i) = ∑ k : I, op (unop x k i) * op (unop y j k)
    rw [Matrix.mul_apply, Finset.op_sum]
    rfl
  commutes' a := by
    ext i j
    change op (algebraMap F (Matrix I I D) a j i) = algebraMap F (Matrix I I Dᵐᵒᵖ) a i j
    rw [Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : i = j <;> simp [h, eq_comm]

private def matrixAnti {I : Type*} [Fintype I] [DecidableEq I]
    (b : AntiEquiv F D) : AntiEquiv F (Matrix I I D) :=
  b.mapMatrix.trans (matrixOpposite I).symm

private theorem anti_gram {K : Type*} [Field K] {C : Type*} [Ring C] [Algebra K C]
    (hC : _root_.Specs.RM03.CSA.isCentralSimple K C) (s d : AntiEquiv K C) :
    ∃ H : Cˣ, ∀ x, antiValue s x = H.inv * antiValue d x * H.val := by
  let E : C ≃ₐ[K] C := AlgEquiv.unop (d.symm.trans s)
  obtain ⟨U, hU⟩ := RM03.CSA.algEquiv_isInner hC E
  refine ⟨U⁻¹, fun x => ?_⟩
  simpa [E, antiValue] using hU (antiValue d x)

section Alternating

variable {K I J : Type*} [CommRing K] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

private theorem alternating_J (n : ℕ) : AlternatingMatrix (Matrix.J (Fin n) K) := by
  intro x
  simp [Matrix.J, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.neg_mulVec, mul_comm, Finset.sum_neg_distrib]

omit [DecidableEq I] [DecidableEq J] in
private theorem alternating_congr {H : Matrix I I K} (h : AlternatingMatrix H)
    (P : Matrix I J K) : AlternatingMatrix (P.transpose * H * P) := by
  intro x
  simp only [← mulVec_mulVec, dotProduct_transpose_mulVec]
  simpa only [dotProduct_comm] using h (P *ᵥ x)

omit [DecidableEq I] in
private theorem alternating_smul {H : Matrix I I K} (h : AlternatingMatrix H) (c : K) :
    AlternatingMatrix (c • H) := by
  intro x
  rw [smul_mulVec, dotProduct_smul, h, smul_zero]

private theorem alternating_transpose {H : Matrix I I K} (h : AlternatingMatrix H) :
    H.transpose = -H := by
  have hh : (Matrix.toLinearMap₂' K H).IsAlt := fun x => by
    exact (Matrix.toLinearMap₂'_apply' H x x).trans (h x)
  ext i j
  simpa [Matrix.toLinearMap₂'_apply', ← dotProduct_mulVec, Matrix.mulVec_single_one] using
    (LinearMap.BilinForm.IsAlt.neg_eq hh (Pi.single i 1) (Pi.single j 1)).symm

private theorem alternating_diagonal {H : Matrix I I K} (h : AlternatingMatrix H) (i : I) :
    H i i = 0 := by
  simpa [Matrix.mulVec_single_one] using h (Pi.single i 1)

private def jUnit (I : Type*) [Fintype I] [DecidableEq I] (K : Type*) [CommRing K] :
    (Matrix (I ⊕ I) (I ⊕ I) K)ˣ :=
  ⟨Matrix.J I K, -Matrix.J I K, by simp [Matrix.J_squared], by simp [Matrix.J_squared]⟩

private def transposeAdjoint (H : (Matrix I I K)ˣ) (X : Matrix I I K) : Matrix I I K :=
  H.inv * X.transpose * H.val

private theorem transposeAdjoint_add (H : (Matrix I I K)ˣ) (X Y : Matrix I I K) :
    transposeAdjoint H (X + Y) = transposeAdjoint H X + transposeAdjoint H Y := by
  simp [transposeAdjoint, mul_add, add_mul]

private theorem transposeAdjoint_smul (H : (Matrix I I K)ˣ) (t : K) (X : Matrix I I K) :
    transposeAdjoint H (t • X) = t • transposeAdjoint H X := by
  simp [transposeAdjoint]

private theorem transposeAdjoint_map {S : Type*} [CommRing S] (f : K →+* S)
    (H : (Matrix I I K)ˣ) (X : Matrix I I K) :
    (transposeAdjoint H X).map f =
      transposeAdjoint (Units.map f.mapMatrix.toMonoidHom H) (X.map f) := by
  simp [transposeAdjoint, Matrix.map_mul, Matrix.transpose_map]

end Alternating

section SplitComparison

variable {K : Type*} [Field K] {I J : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- An algebra isomorphism between two matrix presentations preserves the type
of the adjoint. This argument uses congruence of the alternating Gram form. -/
private theorem alternating_of_adjoint_equiv [Nonempty I]
    (E : Matrix I I K ≃ₐ[K] Matrix J J K) (H : (Matrix I I K)ˣ) (G : (Matrix J J K)ˣ)
    (hG : AlternatingMatrix G.val)
    (hE : ∀ X, E (transposeAdjoint H X) = transposeAdjoint G (E X)) :
    AlternatingMatrix H.val := by
  have hc : Fintype.card I = Fintype.card J := by
    have h := E.toLinearEquiv.finrank_eq
    simp only [Module.finrank_matrix, Module.finrank_self, mul_one] at h
    nlinarith
  let p : I ≃ J := Fintype.equivOfCardEq hc
  let re := Matrix.reindexAlgEquiv K K p
  let G' : (Matrix I I K)ˣ := Units.map re.symm.toMonoidHom G
  have hre (X : Matrix I I K) : (re X).transpose = re X.transpose := rfl
  have hg' : AlternatingMatrix G'.val := by
    intro x
    let y : J → K := x ∘ p.symm
    have h := hG y
    simp only [dotProduct, Matrix.mulVec] at h ⊢
    rw [← Equiv.sum_comp p (fun j => y j * ∑ k, G.val j k * y k)] at h
    simp only [Function.comp_apply, y, Equiv.symm_apply_apply] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [← Equiv.sum_comp p (fun j => G.val (p i) j * x (p.symm j))]
    simp [G', re, Matrix.reindex_apply, Matrix.submatrix_apply]
  let E' := E.trans re.symm
  have he' (X : Matrix I I K) :
      E' (transposeAdjoint H X) = transposeAdjoint G' (E' X) := by
    apply re.injective
    change re (re.symm (E _)) = re (transposeAdjoint G' (re.symm (E X)))
    rw [re.apply_symm_apply, hE]
    simp only [transposeAdjoint, map_mul]
    rw [← hre, re.apply_symm_apply]
    change _ = re (re.symm G.inv) * (E X).transpose * re (re.symm G.val)
    simp
  have hCSA : RM03.CSA.IsCentralSimple K (Matrix I I K) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨U, hU⟩ := RM03.CSA.algEquiv_isInner hCSA E'
  let gram : Matrix I I K := U.val.transpose * G'.val * U.val
  have hgram : AlternatingMatrix gram := alternating_congr hg' U.val
  have hcomm (Y : Matrix I I K) : (gram * H.inv) * Y = Y * (gram * H.inv) := by
    have h := he' Y.transpose
    simp only [hU, transposeAdjoint, Matrix.transpose_transpose, Matrix.transpose_mul] at h
    have hu : U.inv * U.val = 1 := U.inv_val
    have hG' : G'.val * G'.inv = 1 := G'.val_inv
    have hH : H.val * H.inv = 1 := H.val_inv
    have htu : U.val.transpose * U.inv.transpose = 1 := by
      rw [← Matrix.transpose_mul, hu, Matrix.transpose_one]
    have h' := congrArg (fun X : Matrix I I K => (U.val.transpose * G'.val) * X * U.val * H.inv) h
    change (U.val.transpose * G'.val) * (U.val * (H.inv * Y * H.val) * U.inv) * U.val * H.inv =
      (U.val.transpose * G'.val) * (G'.inv * ((U.inv).transpose * (Y * U.val.transpose)) * G'.val) * U.val * H.inv at h'
    simp only [mul_assoc] at h'
    rw [← mul_assoc U.inv U.val, hu, one_mul,
      hH, mul_one,
      ← mul_assoc G'.val G'.inv, hG', one_mul,
      ← mul_assoc U.val.transpose U.inv.transpose, htu, one_mul] at h'
    simpa only [gram, mul_assoc] using h'
  have hc' : gram * H.inv ∈ Subalgebra.center K (Matrix I I K) := by
    rw [Subalgebra.mem_center_iff]
    exact fun Y => (hcomm Y).symm
  have hc'' : gram * H.inv ∈ (⊥ : Subalgebra K (Matrix I I K)) :=
    Algebra.IsCentral.out hc'
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hc''
  have hval : gram = c • H.val := by
    rw [Algebra.smul_def, hc, mul_assoc, H.inv_val, mul_one]
  have hdet : gram.det ≠ 0 := by
    unfold gram
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero (isUnit_iff_ne_zero.mp ((U.isUnit).map detMonoidHom))
      (isUnit_iff_ne_zero.mp ((G'.isUnit).map detMonoidHom)))
      (isUnit_iff_ne_zero.mp ((U.isUnit).map detMonoidHom))
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hval, hz, zero_smul, Matrix.det_zero] at hdet
    exact hdet rfl
  have hrec : H.val = c⁻¹ • gram := by
    rw [hval, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hrec]
  exact alternating_smul hgram _

end SplitComparison

section Field

variable {K : Type*} [Field K] {C : Type*} [Ring C] [Algebra K C]

private def transportAnti {M : Type*} [Ring M] [Algebra K M]
    (e : C ≃ₐ[K] M) (s : AntiEquiv K C) : AntiEquiv K M :=
  e.symm.trans (s.trans (AlgEquiv.op e))

private theorem nonempty_presentation {D : Type*} [Nontrivial C] [Ring D] [Algebra K D]
    {r : ℕ} (e : C ≃ₐ[K] Matrix (Fin r) (Fin r) D) : Nonempty (Fin r) := by
  by_contra! h
  let : IsEmpty (Fin r) := h
  exact zero_ne_one (e.injective (Subsingleton.elim (e 0) (e 1)))

private theorem matrix_card_eq {I J : Type*} [Fintype I] [Fintype J]
    (E : Matrix I I K ≃ₗ[K] Matrix J J K) : Fintype.card I = Fintype.card J := by
  have h := E.finrank_eq
  simp only [Module.finrank_matrix, Module.finrank_self, mul_one] at h
  nlinarith

private theorem split_comparison_all {L : Type*} [Field L] [Algebra K L]
    {s : Involution K C} {n : ℕ} (c : SplitComparison s L n) (x : L ⊗[K] C) :
    c.equiv (antiValue (extendAnti s.anti L) x) =
      transposeAdjoint (jUnit (Fin n) L) (c.equiv x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t a =>
    rw [extendAnti_tmul]
    have h (a : C) : c.equiv (t ⊗ₜ[K] a) = t • c.equiv (1 ⊗ₜ[K] a) := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, h, transposeAdjoint_smul, c.adjoint]
    rfl
  | add x y hx hy => simp only [antiValue_add, map_add, hx, hy, transposeAdjoint_add]

private theorem scalar_gram_base_change {I L : Type*} [Fintype I] [DecidableEq I]
    [CommRing L] [Algebra K L] (s : AntiEquiv K C)
    (e : C ≃ₐ[K] Matrix I I K) (H : (Matrix I I K)ˣ)
    (h : ∀ a, e (antiValue s a) = transposeAdjoint H (e a)) (x : L ⊗[K] C) :
    let E := (extendEquiv e).trans (scalarMatrixBaseChange (R := L) I)
    E (antiValue (extendAnti s L) x) =
      transposeAdjoint (Units.map (algebraMap K L).mapMatrix.toMonoidHom H) (E x) := by
  dsimp only
  induction x using TensorProduct.inductionOn with
  | tmul t a =>
    simp only [AlgEquiv.trans_apply, extendAnti_tmul, extendEquiv_tmul, scalarMatrixBaseChange_tmul]
    rw [h, transposeAdjoint_map, transposeAdjoint_smul]
  | add x y hx hy => simp only [antiValue_add, map_add, hx, hy, transposeAdjoint_add]

private def hyperbolicIndex (n : ℕ) :
    Fin n ⊕ Fin n ≃ _root_.Specs.D05.M11.SymplecticBlocks.BlockIndex n 0 where
  toFun := Sum.elim (fun i => .inl (i, 1)) (fun i => .inl (i, 0))
  invFun := Sum.elim (fun p => if p.2 = 0 then .inr p.1 else .inl p.1) Fin.elim0
  left_inv i := by cases i <;> simp
  right_inv i := by
    rcases i with ⟨i, j⟩ | i
    · fin_cases j <;> simp
    · exact i.elim0

private theorem hyperbolic_basis {n r : ℕ} (hr : r = n + n)
    (H : (Matrix (Fin r) (Fin r) K)ˣ) (hH : AlternatingMatrix H.val) :
    ∃ (P : Matrix (Fin n ⊕ Fin n) (Fin r) K) (Q : Matrix (Fin r) (Fin n ⊕ Fin n) K),
      P * Q = 1 ∧ Q * P = 1 ∧ Q.transpose * H.val * Q = Matrix.J (Fin n) K := by
  classical
  let B : LinearMap.BilinForm K (Fin r → K) := Matrix.toLinearMap₂' K H.val
  have hB : B.IsAlt := fun x => (Matrix.toLinearMap₂'_apply' H.val x x).trans (hH x)
  have hnd : B.Nondegenerate := (LinearMap.nondegenerate_toLinearMap₂'_iff_det_ne_zero).mpr
    (isUnit_iff_ne_zero.mp (H.isUnit.map Matrix.detMonoidHom))
  obtain ⟨m, s, b, hb, hdim, _, hrad⟩ := D05.M11.SymplecticBlocks.normal_basis B hB
  have hs : s = 0 := by
    by_contra! hne
    let i : Fin s := ⟨0, Nat.pos_of_ne_zero hne⟩
    have hi : b (.inr i) ∈ LinearMap.ker B := by
      change b (.inr i) ∈ _root_.Specs.D05.M11.Radicals.leftRadical_value B
      rw [hrad]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact b.ne_zero (.inr i) (hnd.1 _ (fun y => DFunLike.congr_fun (LinearMap.mem_ker.mp hi) y))
  subst s
  have hmn : m = n := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, add_zero] at hdim
    omega
  subst m
  let b' := b.reindex (hyperbolicIndex n).symm
  let std := Pi.basisFun K (Fin r)
  let P := LinearMap.toMatrix std b' (LinearMap.id : (Fin r → K) →ₗ[K] Fin r → K)
  let Q := LinearMap.toMatrix b' std (LinearMap.id : (Fin r → K) →ₗ[K] Fin r → K)
  refine ⟨P, Q, ?_, ?_, ?_⟩
  · simp [P, Q]
  · simp [P, Q]
  · have hQ (i) : Q *ᵥ Pi.single i 1 = b' i := by
      funext j
      simp [Q, std, Matrix.col, Module.Basis.toMatrix_apply]
    have hcomp := Matrix.toLinearMap₂'_comp H.val Q Q
    ext i j
    have h := DFunLike.congr_fun (DFunLike.congr_fun hcomp (Pi.single i 1)) (Pi.single j 1)
    have hh : B (b' i) (b' j) = (Q.transpose * H.val * Q) i j := by
      simpa [B, LinearMap.compl₁₂_apply, Matrix.toLin'_apply, hQ,
        Matrix.toLinearMap₂'_apply', ← dotProduct_mulVec, Matrix.mulVec_single_one] using h
    rw [← hh]
    simp only [b', Module.Basis.reindex_apply, Equiv.symm_symm, hb]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [_root_.Specs.D05.M11.SymplecticBlocks.blockMatrix,
        _root_.Specs.D05.M11.SymplecticBlocks.J, hyperbolicIndex, Matrix.J,
        Matrix.one_apply, apply_ite (fun x : K => -x)]

private def matrixChange {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (P : Matrix J I K) (Q : Matrix I J K) (hP : P * Q = 1) (hQ : Q * P = 1) :
    Matrix I I K ≃ₐ[K] Matrix J J K where
  toFun X := P * X * Q
  invFun Y := Q * Y * P
  left_inv X := by
    change Q * (P * X * Q) * P = X
    rw [show Q * (P * X * Q) * P = (Q * P) * X * (Q * P) by
      simp only [Matrix.mul_assoc], hQ, Matrix.one_mul, Matrix.mul_one]
  right_inv X := by
    change P * (Q * X * P) * Q = X
    rw [show P * (Q * X * P) * Q = (P * Q) * X * (P * Q) by
      simp only [Matrix.mul_assoc], hP, Matrix.one_mul, Matrix.mul_one]
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    change P * (X * Y) * Q = (P * X * Q) * (P * Y * Q)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, hQ, Matrix.one_mul]
  commutes' t := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hP]

theorem fieldModel : FieldModel.{u,v,z,q} := by
  intro K _ C _ _ hC s L _ _ n r c e
  let : IsSimpleRing C := hC.1
  let : Nonempty (Fin r) := nonempty_presentation e
  let a := transportAnti e s.anti
  let tr := matrixAnti (AlgEquiv.toOpposite K K) (I := Fin r)
  have hCSA : _root_.Specs.RM03.CSA.isCentralSimple K (Matrix (Fin r) (Fin r) K) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨H, hH⟩ := anti_gram hCSA a tr
  have h (x : C) : e (antiValue s.anti x) = transposeAdjoint H (e x) := by
    have hx := hH (e x)
    change e (antiValue s.anti (e.symm (e x))) =
      H.inv * antiValue tr (e x) * H.val at hx
    rw [e.symm_apply_apply] at hx
    exact hx
  let E : (L ⊗[K] C) ≃ₐ[L] Matrix (Fin r) (Fin r) L :=
    (extendEquiv e).trans (scalarMatrixBaseChange (Fin r))
  let HL := Units.map (algebraMap K L).mapMatrix.toMonoidHom H
  have hh : AlternatingMatrix HL.val := by
    refine alternating_of_adjoint_equiv (E.symm.trans c.equiv) HL
      (jUnit (Fin n) L) (alternating_J n) ?_
    intro Y
    obtain ⟨x, rfl⟩ := E.surjective Y
    have hx := scalar_gram_base_change s.anti e H h x
    change E (antiValue (extendAnti s.anti L) x) = transposeAdjoint HL (E x) at hx
    change c.equiv (E.symm (transposeAdjoint HL (E x))) =
      transposeAdjoint (jUnit (Fin n) L) (c.equiv (E.symm (E x)))
    rw [← hx, E.symm_apply_apply, E.symm_apply_apply, split_comparison_all c]
  have hAlt : AlternatingMatrix H.val := by
    intro x
    apply (algebraMap K L).injective
    simpa [HL, dotProduct, Matrix.mulVec, map_sum, Matrix.map_apply] using
      hh (fun i => algebraMap K L (x i))
  have hr : r = n + n := by
    simpa using matrix_card_eq (E.symm.trans c.equiv).toLinearEquiv
  obtain ⟨P, Q, hP, hQ, hJ⟩ := hyperbolic_basis hr H hAlt
  let e' := e.trans (matrixChange P Q hP hQ)
  have hconj (a : C) :
      e' (antiValue s.anti a) = transposeAdjoint (jUnit (Fin n) K) (e' a) := by
    change P * e (antiValue s.anti a) * Q = _
    rw [h]
    have hh : Matrix.J (Fin n) K * (P * transposeAdjoint H (e a) * Q) =
      (P * e a * Q).transpose * Matrix.J (Fin n) K := by
      rw [← hJ]
      simp only [transposeAdjoint, Matrix.transpose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q P, hQ, Matrix.one_mul,
        ← Matrix.mul_assoc H.val H.inv, H.val_inv, Matrix.one_mul,
        ← Matrix.mul_assoc P.transpose Q.transpose, ← Matrix.transpose_mul,
        hQ, Matrix.transpose_one, Matrix.one_mul]
    change _ = (-Matrix.J (Fin n) K) * (P * e a * Q).transpose * Matrix.J (Fin n) K
    rw [mul_assoc, ← hh, ← mul_assoc, Matrix.neg_mul, Matrix.J_squared, neg_neg, Matrix.one_mul]
  let E' (R : Type q) [CommRing R] [Algebra K R] :=
    (extendEquiv (R := R) e').trans (scalarMatrixBaseChange (Fin n ⊕ Fin n))
  refine ⟨H, P, Q, hAlt, h, hP, hQ, hJ, E', ?_, ?_, ?_⟩
  · intro R _ _ x
    simp [E', e', matrixChange]
  · intro R _ _ x
    have hx := scalar_gram_base_change s.anti e' (jUnit (Fin n) K) hconj x
    change E' R (antiValue (extendAnti s.anti R) x) = _ at hx
    have hR : Units.map (algebraMap K R).mapMatrix.toMonoidHom (jUnit (Fin n) K) =
        jUnit (Fin n) R := Units.ext (Matrix.map_J (Fin n) (algebraMap K R))
    rw [hR] at hx
    have hx' : E' R (antiValue (extendAnti s.anti R) x) =
        transposeAdjoint (jUnit (Fin n) R) (E' R x) := hx
    rw [SymplecticGroup.mem_iff', ← (E' R).injective.eq_iff, map_mul, map_one, hx']
    let j := jUnit (Fin n) R
    change (E' R x).transpose * j.val * E' R x = j.val ↔
      j.inv * (E' R x).transpose * j.val * E' R x = 1
    rw [show j.inv * (E' R x).transpose * j.val * E' R x =
      j.inv * ((E' R x).transpose * j.val * E' R x) by simp only [mul_assoc]]
    constructor
    · intro h
      rw [h, j.inv_val]
    · intro h
      have hj := congrArg (fun X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R => j.val * X) h
      rwa [← mul_assoc, j.val_inv, one_mul, mul_one] at hj
  · intro R S _ _ _ _ f x
    exact scalarMatrixBaseChange_natural f e' x

end Field

section Quaternion

variable {K : Type*} [Field K] {C : Type*} [Ring C] [Algebra K C]

private def tensorTower {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (M ⊗[L] (L ⊗[K] C)) ≃ₐ[M] (M ⊗[K] C) :=
  (Algebra.TensorProduct.assoc K L M M L C).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid L M M) (.refl : C ≃ₐ[K] C))

private theorem tensorTower_pure {L M : Type*} [Field L] [Field M] [Algebra K L]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M] (x : C) :
    (tensorTower (L := L) (M := M)).symm (1 ⊗ₜ[K] x) =
      1 ⊗ₜ[L] (1 ⊗ₜ[K] x) := by
  apply (tensorTower (K := K) (C := C) (L := L) (M := M)).injective
  simp [tensorTower]

private def extendSplit {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] {s : Involution K C} {n : ℕ}
    (c : SplitComparison s L n) : SplitComparison s M n where
  equiv := (tensorTower (K := K) (C := C) (L := L) (M := M)).symm.trans ((extendEquiv c.equiv).trans (scalarMatrixBaseChange _))
  adjoint x := by
    simp only [AlgEquiv.trans_apply, tensorTower_pure, extendEquiv_tmul,
      scalarMatrixBaseChange_tmul, one_smul]
    rw [c.adjoint]
    simp [standardAdjoint, Matrix.map_mul, Matrix.map_neg, Matrix.transpose_map]

private theorem dagger_add {I : Type*} (s : AntiEquiv F D) (X Y : Matrix I I D) :
    dagger s (X + Y) = dagger s X + dagger s Y := by ext i j; simp [dagger]

private theorem dagger_smul {I : Type*} (s : AntiEquiv F D) (t : F) (X : Matrix I I D) :
    dagger s (t • X) = t • dagger s X := by ext i j; simp [dagger]

private theorem matrixBaseChange_tmul_smul {I : Type*} [Fintype I] [DecidableEq I]
    (t : R) (X : Matrix I I D) :
    matrixBaseChange I (t ⊗ₜ[F] X) = t • X.map (intoTensor R D) := by
  rw [matrixBaseChange_tmul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply]
  change _ = t • ((1 : R) ⊗ₜ[F] X i j)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem matrixCoordinates_pure {I : Type*} [Fintype I] [DecidableEq I]
    (e : A ≃ₐ[F] Matrix I I D) (x : A) :
    ((extendEquiv e).trans (matrixBaseChange (F := F) (D := D) (R := R) I))
      ((1 : R) ⊗ₜ[F] x) = (e x).map (intoTensor (F := F) R D) := by
  exact (congrArg (matrixBaseChange (F := F) (D := D) (R := R) I)
    (extendEquiv_tmul e (1 : R) x)).trans
      (by simpa only [one_smul] using matrixBaseChange_tmul_smul (F := F) (D := D) (1 : R) (e x))

private theorem quaternion_gram_base_change {I : Type*} [Fintype I] [DecidableEq I]
    (s : AntiEquiv F A) (b : AntiEquiv F D)
    (e : A ≃ₐ[F] Matrix I I D) (H : (Matrix I I D)ˣ)
    (h : ∀ a, e (antiValue s a) = H.inv * dagger b (e a) * H.val) (x : R ⊗[F] A) :
    let E := (extendEquiv e).trans (matrixBaseChange (R := R) I)
    let HR := Units.map (intoTensor R D).mapMatrix.toMonoidHom H
    E (antiValue (extendAnti s R) x) = HR.inv * dagger (extendAnti b R) (E x) * HR.val := by
  dsimp only
  have hD (X : Matrix I I D) :
      (dagger b X).map (intoTensor R D) = dagger (extendAnti b R) (X.map (intoTensor R D)) := by
    ext i j
    exact (extendAnti_tmul b (1 : R) (X j i)).symm
  induction x using TensorProduct.inductionOn with
  | tmul t a =>
    simp only [AlgEquiv.trans_apply, extendAnti_tmul, extendEquiv_tmul, matrixBaseChange_tmul_smul]
    rw [h, dagger_smul, Matrix.map_mul, Matrix.map_mul, hD]
    simp
  | add x y hx hy => simp only [antiValue_add, map_add, hx, hy, dagger_add, mul_add, add_mul]

private def plane (L : Type*) [Field L] : (Matrix (Fin 2) (Fin 2) L)ˣ where
  val := !![0, 1; -1, 0]
  inv := -!![0, 1; -1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem adjugate_plane {L : Type*} [Field L] (X : Matrix (Fin 2) (Fin 2) L) :
    X.adjugate = transposeAdjoint (plane L) X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transposeAdjoint, plane, Matrix.adjugate_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]

private theorem split_quaternion_anti {B L : Type*} [DivisionRing B] [Algebra K B]
    [Field L] [Algebra K L] (b : Involution K B)
    (e : (L ⊗[K] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L)
    (he : ∀ x : B, e (1 ⊗ₜ[K] antiValue b.anti x) = (e (1 ⊗ₜ[K] x)).adjugate)
    (x : L ⊗[K] B) :
    e (antiValue (extendAnti b.anti L) x) = transposeAdjoint (plane L) (e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t a =>
    rw [extendAnti_tmul]
    have h (a : B) : e (t ⊗ₜ[K] a) = t • e (1 ⊗ₜ[K] a) := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, h, transposeAdjoint_smul, ← adjugate_plane, he]
  | add x y hx hy => simp only [map_add, antiValue_add, hx, hy, transposeAdjoint_add]

private def blockPlane (L : Type*) [Field L] (I : Type*) [Fintype I] [DecidableEq I] :
    (Matrix (I × Fin 2) (I × Fin 2) L)ˣ :=
  Units.map (Matrix.compAlgEquiv I (Fin 2) L L).toMonoidHom
    ⟨Matrix.diagonal (fun _ => (plane L).val), Matrix.diagonal (fun _ => (plane L).inv),
      by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩

private theorem blockPlane_transpose {L I : Type*} [Field L] [Fintype I] [DecidableEq I] :
    (blockPlane L I).val.transpose = -(blockPlane L I).val := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [blockPlane, transpose_apply]
  change (Matrix.diagonal (fun _ : I => (plane L).val)) j i b a =
    -((Matrix.diagonal (fun _ : I => (plane L).val)) i j a b)
  by_cases hij : i = j
  · subst j
    fin_cases a <;> fin_cases b <;> simp [plane]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]

private theorem split_block_dagger {L T I : Type*} [Field L] [Ring T] [Algebra L T]
    [Fintype I] [DecidableEq I] (s : AntiEquiv L T)
    (e : T ≃ₐ[L] Matrix (Fin 2) (Fin 2) L)
    (he : ∀ x, e (antiValue s x) = transposeAdjoint (plane L) (e x))
    (X : Matrix I I T) :
    let W := e.mapMatrix.trans (Matrix.compAlgEquiv I (Fin 2) L L)
    W (dagger s X) = transposeAdjoint (blockPlane L I) (W X) := by
  dsimp only
  let comp := Matrix.compAlgEquiv I (Fin 2) L L
  let Xt : Matrix I I (Matrix (Fin 2) (Fin 2) L) := Matrix.of (fun i j => (e (X j i)).transpose)
  have htr : (comp (e.mapMatrix X)).transpose = comp Xt := rfl
  change comp (e.mapMatrix (dagger s X)) = _
  rw [transposeAdjoint, show (e.mapMatrix.trans comp) X = comp (e.mapMatrix X) from rfl, htr]
  let Dinv : Matrix I I (Matrix (Fin 2) (Fin 2) L) := Matrix.diagonal (fun _ => (plane L).inv)
  let Dval : Matrix I I (Matrix (Fin 2) (Fin 2) L) := Matrix.diagonal (fun _ => (plane L).val)
  change comp (e.mapMatrix (dagger s X)) = comp Dinv * comp Xt * comp Dval
  have heq : e.mapMatrix (dagger s X) = Dinv * Xt * Dval := by
    apply Matrix.ext
    intro i j
    dsimp only [Dval, Dinv]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact he (X j i)
  rw [heq, map_mul, map_mul]

private theorem matrix_pairing_reversal {I : Type*} [Fintype I]
    (s : AntiEquiv F D) (X : Matrix I I D) (v : I → D) :
    (fun i => antiValue s ((X *ᵥ v) i)) = (fun i => antiValue s (v i)) ᵥ* dagger s X := by
  funext i
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct, dagger]

private theorem hermitianValue_rev {I : Type*} [Fintype I] (s : AntiEquiv F D)
    (hs : Function.Involutive (antiValue s)) (H : Matrix I I D) (x y : I → D) :
    antiValue s (hermitianValue s H x y) = hermitianValue s (dagger s H) y x := by
  unfold hermitianValue
  calc
    _ = (fun i => antiValue s ((H *ᵥ y) i)) ⬝ᵥ x := by
      have hs' (a : D) : antiValue s (antiValue s a) = a := hs a
      simp [dotProduct, hs']
    _ = _ := by rw [matrix_pairing_reversal, ← dotProduct_mulVec]

private theorem hermitianValue_laws {I : Type*} [Fintype I]
    (s : AntiEquiv F D) (hs : Function.Involutive (antiValue s)) (H : Matrix I I D)
    (hH : dagger s H = H) : HermitianLaws s (hermitianValue s H) where
  add_right x y z := by simp [hermitianValue, mulVec_add, dotProduct_add]
  mul_right x y a := by
    have h : H *ᵥ (fun i => y i * a) = fun i => (H *ᵥ y) i * a := by
      funext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
    simp [hermitianValue, h, dotProduct, Finset.sum_mul, mul_assoc]
  symmetric x y := by rw [hermitianValue_rev s hs, hH]

private theorem extendAnti_square (s : AntiEquiv F D)
    (hs : Function.Involutive (antiValue s)) : Function.Involutive (antiValue (extendAnti s R)) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul t a => rw [extendAnti_tmul, extendAnti_tmul, hs a]
  | add x y hx hy => rw [antiValue_add, antiValue_add, hx, hy]

private theorem hermitianValue_congr {I : Type*} [Fintype I]
    (s : AntiEquiv F D) (H g : Matrix I I D) (x y : I → D) :
    hermitianValue s H (g *ᵥ x) (g *ᵥ y) = hermitianValue s (dagger s g * H * g) x y := by
  unfold hermitianValue
  rw [matrix_pairing_reversal, ← dotProduct_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]

private theorem hermitianValue_single {I : Type*} [Fintype I] [DecidableEq I]
    (s : AntiEquiv F D) (H : Matrix I I D) (i j : I) :
    hermitianValue s H (Pi.single i 1) (Pi.single j 1) = H i j := by
  have h : (fun k => antiValue s ((Pi.single i 1 : I → D) k)) = Pi.single i 1 := by
    funext k
    by_cases h : k = i <;> simp [h]
  simp [hermitianValue, h]

private theorem hermitianValue_nondegenerate {I : Type*} [Fintype I] [DecidableEq I]
    (s : AntiEquiv F D) (H : (Matrix I I D)ˣ) (x : I → D) (hx : x ≠ 0) :
    ∃ y, hermitianValue s H.val x y ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  refine ⟨H.inv *ᵥ Pi.single i 1, ?_⟩
  rw [hermitianValue, mulVec_mulVec, H.val_inv, one_mulVec, dotProduct_single_one]
  intro hz
  apply hi
  apply s.injective
  apply unop_injective
  exact hz.trans (antiValue_zero s).symm

private theorem plane_scalar {L : Type*} [Field L] (X : Matrix (Fin 2) (Fin 2) L)
    (ht : ((plane L).val * X).transpose = -((plane L).val * X))
    (hd : ∀ i, ((plane L).val * X) i i = 0) :
    ∃ a : L, X = algebraMap L (Matrix (Fin 2) (Fin 2) L) a := by
  have h₀ : X 1 0 = 0 := by
    simpa [plane, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using hd 0
  have h₁ : X 0 1 = 0 := by
    simpa [plane, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using hd 1
  have h₂ : X 0 0 = X 1 1 := by
    have h := congrArg (fun Y : Matrix (Fin 2) (Fin 2) L => Y 0 1) ht
    simpa [plane, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h
  refine ⟨X 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.algebraMap_matrix_apply, h₀, h₁, h₂]

private theorem scalar_of_split_scalar {B L : Type*} [DivisionRing B] [Algebra K B]
    [Field L] [Algebra K L] [Algebra.IsCentral K B] (T : B →ₐ[K] Matrix (Fin 2) (Fin 2) L)
    (hT : Function.Injective T) {x : B}
    (hx : ∃ a : L, T x = algebraMap L (Matrix (Fin 2) (Fin 2) L) a) :
    ∃ a : K, x = algebraMap K B a := by
  obtain ⟨a, ha⟩ := hx
  have hcent : x ∈ Subalgebra.center K B := by
    rw [Subalgebra.mem_center_iff]
    intro y
    apply hT
    rw [map_mul, map_mul, ha]
    exact (Algebra.commutes a (T y)).symm
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hcent : x ∈ (⊥ : Subalgebra K B))
  exact ⟨a, ha.symm⟩

private theorem quaternion_diagonal_scalar {B L I : Type*} [DivisionRing B] [Algebra K B]
    [Field L] [Algebra K L] [Algebra.IsCentral K B] [Fintype I] [DecidableEq I]
    (T : B →ₐ[K] Matrix (Fin 2) (Fin 2) L) (hT : Function.Injective T)
    (X : Matrix I I B)
    (hX : AlternatingMatrix ((blockPlane L I).val * Matrix.compAlgEquiv I (Fin 2) L L (T.mapMatrix X)))
    (i : I) : ∃ a : K, X i i = algebraMap K B a := by
  let M := (blockPlane L I).val * Matrix.compAlgEquiv I (Fin 2) L L (T.mapMatrix X)
  have hM (a b : Fin 2) : M (i, a) (i, b) = ((plane L).val * T (X i i)) a b := by
    let c := Matrix.compAlgEquiv I (Fin 2) L L
    let Dval : Matrix I I (Matrix (Fin 2) (Fin 2) L) := Matrix.diagonal (fun _ => (plane L).val)
    let V : Matrix I I (Matrix (Fin 2) (Fin 2) L) := T.mapMatrix X
    change (c Dval * c V) (i, a) (i, b) = _
    have hc : c Dval * c V = c (Dval * V) := (map_mul c _ _).symm
    rw [hc]
    change ((Dval * V) i i) a b = _
    dsimp only [Dval]
    rw [Matrix.diagonal_mul]
    rfl
  apply scalar_of_split_scalar T hT
  apply plane_scalar
  · ext a b
    have h := congrArg (fun Y : Matrix (I × Fin 2) (I × Fin 2) L => Y (i, a) (i, b))
      (alternating_transpose hX)
    change M (i, b) (i, a) = -M (i, a) (i, b) at h
    simpa only [transpose_apply, Matrix.neg_apply, hM] using h
  · intro a
    rw [← hM]
    exact alternating_diagonal hX (i, a)

private theorem hermitian_isometry {F D I : Type*} [CommRing F] [Ring D] [Algebra F D]
    [Fintype I] [DecidableEq I] (s : AntiEquiv F D) (H : (Matrix I I D)ˣ)
    (g : Matrix I I D) :
    H.inv * dagger s g * H.val * g = 1 ↔
      ∀ x y, hermitianValue s H.val (g *ᵥ x) (g *ᵥ y) = hermitianValue s H.val x y := by
  have h : H.inv * dagger s g * H.val * g = H.inv * (dagger s g * H.val * g) := by
    simp only [mul_assoc]
  rw [h]
  constructor
  · intro hg x y
    have hG := congrArg (fun X : Matrix I I D => H.val * X) hg
    rw [← mul_assoc, H.val_inv, one_mul, mul_one] at hG
    rw [hermitianValue_congr, hG]
  · intro hg
    have hG : dagger s g * H.val * g = H.val := by
      ext i j
      have hi := hg (Pi.single i 1) (Pi.single j 1)
      simpa only [hermitianValue_congr, hermitianValue_single] using hi
    rw [hG, H.inv_val]

private theorem quaternion_point_compare {I : Type*} [Fintype I] [DecidableEq I]
    (s : AntiEquiv F A) (b : AntiEquiv F D) (H : (Matrix I I D)ˣ)
    (e : A ≃ₐ[F] Matrix I I D)
    (h : ∀ a, e (antiValue s a) = H.inv * dagger b (e a) * H.val)
    (g : (R ⊗[F] A)ˣ) :
    let E : (R ⊗[F] A) ≃ₐ[R] Matrix I I (R ⊗[F] D) :=
      (extendEquiv e).trans (matrixBaseChange (R := R) I)
    let hR : (I → R ⊗[F] D) → (I → R ⊗[F] D) → R ⊗[F] D :=
      hermitianValue (extendAnti b R) (H.val.map (intoTensor (F := F) R D))
    antiValue (extendAnti s R) g.val * g.val = 1 ↔
      ∀ x y, hR (E g.val *ᵥ x) (E g.val *ᵥ y) = hR x y := by
  let E : (R ⊗[F] A) ≃ₐ[R] Matrix I I (R ⊗[F] D) :=
      (extendEquiv e).trans (matrixBaseChange (R := R) I)
  let HR := Units.map (intoTensor (F := F) R D).mapMatrix.toMonoidHom H
  let sR := extendAnti s R
  let bR := extendAnti b R
  let Z := E g.val
  have hG : E (antiValue sR g.val) = HR.inv * dagger bR Z * HR.val :=
    quaternion_gram_base_change s b e H h g.val
  have hprod : E (antiValue sR g.val * g.val) = HR.inv * dagger bR Z * HR.val * Z := by
    rw [map_mul, hG]
  have htest :
      antiValue sR g.val * g.val = 1 ↔ HR.inv * dagger bR Z * HR.val * Z = 1 := by
    rw [← hprod, ← E.map_one]
    exact E.injective.eq_iff.symm
  exact htest.trans (hermitian_isometry bR HR Z)

set_option maxHeartbeats 450000 in
theorem quaternionModel : QuaternionModel.{u,v,z,w,q} := by
  intro K _ C _ _ hC s L _ _ n r c B _ _ hB hd b hb e
  let : IsSimpleRing C := hC.1
  let : Nonempty (Fin r) := nonempty_presentation e
  let : Algebra.IsCentral K B := hB.2.1
  let : FiniteDimensional K B := hB.2.2
  let a := transportAnti e s.anti
  have hCSA : _root_.Specs.RM03.CSA.isCentralSimple K (Matrix (Fin r) (Fin r) B) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨H, hH⟩ := anti_gram hCSA a (matrixAnti b.anti)
  have h (x : C) : e (antiValue s.anti x) = H.inv * dagger b.anti (e x) * H.val := by
    have hx := hH (e x)
    change e (antiValue s.anti (e.symm (e x))) = H.inv * dagger b.anti (e x) * H.val at hx
    rw [e.symm_apply_apply] at hx
    exact hx
  let M := AlgebraicClosure L
  let cM : SplitComparison s M n := extendSplit c
  let : IsSimpleRing (M ⊗[K] B) := (RM03.CSA.isCentralSimple_baseChange (L := M) hB).1
  let : FiniteDimensional M (M ⊗[K] B) :=
    (RM03.CSA.isCentralSimple_baseChange (L := M) hB).2.2
  obtain ⟨m, _, ⟨eB⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed M (M ⊗[K] B)
  have hm : m = 2 := (RM03.CSA.degree_eq_matrix_size hB eB).symm.trans hd
  subst m
  let E : (M ⊗[K] C) ≃ₐ[M] Matrix (Fin r) (Fin r) (M ⊗[K] B) :=
    (extendEquiv e).trans (matrixBaseChange (Fin r))
  let cflat := Matrix.compAlgEquiv (Fin r) (Fin 2) M M
  let W := eB.mapMatrix.trans cflat
  let T := (eB.restrictScalars K).toAlgHom.comp (intoTensor M B)
  let Tflat := (cflat.restrictScalars K).toAlgHom.comp T.mapMatrix
  let J := blockPlane M (Fin r)
  have hT : Function.Injective T := eB.injective.comp
    (Algebra.TensorProduct.includeRight_injective (B := B) (algebraMap K M).injective)
  have hflat (X : Matrix (Fin r) (Fin r) (M ⊗[K] B)) :
      W (dagger (extendAnti b.anti M) X) = transposeAdjoint J (W X) :=
    split_block_dagger _ eB (split_quaternion_anti b eB (hb.adjugate M eB)) X
  have hflat' (X : Matrix (Fin r) (Fin r) B) :
      Tflat (dagger b.anti X) = transposeAdjoint J (Tflat X) := by
    have hx := hflat (X.map (intoTensor M B))
    change W (dagger (extendAnti b.anti M) (X.map (intoTensor M B))) =
      transposeAdjoint J (Tflat X) at hx
    have heq : dagger (extendAnti b.anti M) (X.map (intoTensor M B)) =
        (dagger b.anti X).map (intoTensor M B) := by
      ext i j
      exact extendAnti_tmul b.anti (1 : M) (X j i)
    rw [heq] at hx
    exact hx
  let G := J * Units.map Tflat.toMonoidHom H
  have hG (x : M ⊗[K] C) :
      W (E (antiValue (extendAnti s.anti M) x)) = transposeAdjoint G (W (E x)) := by
    have hx := quaternion_gram_base_change s.anti b.anti e H h x
    change E (antiValue (extendAnti s.anti M) x) =
      (H.inv.map (intoTensor M B)) * dagger (extendAnti b.anti M) (E x) *
        (H.val.map (intoTensor M B)) at hx
    rw [hx, map_mul, map_mul, hflat, transposeAdjoint, transposeAdjoint]
    change Tflat H.inv * (J.inv * (W (E x)).transpose * J.val) * Tflat H.val =
      (Tflat H.inv * J.inv) * (W (E x)).transpose * (J.val * Tflat H.val)
    simp only [mul_assoc]
  have hAlt : AlternatingMatrix G.val := by
    let E' := E.trans W
    have : Nonempty (Fin r × Fin 2) := inferInstance
    refine alternating_of_adjoint_equiv (E'.symm.trans cM.equiv) G
      (jUnit (Fin n) M) (alternating_J n) ?_
    intro X
    obtain ⟨x, rfl⟩ := E'.surjective X
    have hx : E' (antiValue (extendAnti s.anti M) x) = transposeAdjoint G (E' x) := hG x
    change cM.equiv (E'.symm (transposeAdjoint G (E' x))) =
      transposeAdjoint (jUnit (Fin n) M) (cM.equiv (E'.symm (E' x)))
    rw [← hx, E'.symm_apply_apply, E'.symm_apply_apply, split_comparison_all cM]
  have hsym : dagger b.anti H.val = H.val := by
    have htflat : Tflat (dagger b.anti H.val) = Tflat H.val := by
      rw [hflat', transposeAdjoint]
      have ht := alternating_transpose hAlt
      change (J.val * Tflat H.val).transpose = -(J.val * Tflat H.val) at ht
      rw [Matrix.transpose_mul, blockPlane_transpose, Matrix.mul_neg, neg_inj] at ht
      rw [mul_assoc, ht, ← mul_assoc, J.inv_val, one_mul]
    have hc : cflat (T.mapMatrix (dagger b.anti H.val)) = cflat (T.mapMatrix H.val) := htflat
    have hm := cflat.injective hc
    ext i j
    exact hT (congrArg (fun X : Matrix (Fin r) (Fin r) (Matrix (Fin 2) (Fin 2) M) => X i j) hm)
  have hdiag : ∀ i, ∃ a : K, H.val i i = algebraMap K B a :=
    quaternion_diagonal_scalar T hT H.val hAlt
  have hnorm (x : Fin r → B) : ∃ a : K, hermitianValue b.anti H.val x x = algebraMap K B a := by
    classical
    let i : Fin r := Classical.choice inferInstance
    let X : Matrix (Fin r) (Fin r) B := fun j k => if k = i then x j else 0
    have hx : X *ᵥ Pi.single i 1 = x := by
      rw [mulVec_single_one]
      funext j
      change (if i = i then x j else 0) = x j
      simp
    let Y := dagger b.anti X * H.val * X
    have hy : AlternatingMatrix (J.val * Tflat Y) := by
      have heq : J.val * Tflat Y = (Tflat X).transpose * G.val * Tflat X := by
        unfold Y
        rw [map_mul, map_mul, hflat', transposeAdjoint]
        change J.val * (J.inv * (Tflat X).transpose * J.val * Tflat H.val * Tflat X) =
          (Tflat X).transpose * (J.val * Tflat H.val) * Tflat X
        simp only [mul_assoc]
        rw [← mul_assoc J.val J.inv, J.val_inv, one_mul]
      rw [heq]
      exact alternating_congr hAlt (Tflat X)
    have he := hermitianValue_congr b.anti H.val X (Pi.single i 1) (Pi.single i 1)
    rw [hx, hermitianValue_single] at he
    rw [he]
    exact quaternion_diagonal_scalar T hT Y hy i
  let E' (R : Type q) [CommRing R] [Algebra K R] :=
    (extendEquiv (R := R) e).trans (matrixBaseChange (Fin r))
  refine ⟨H, hsym, h, hdiag, hermitianValue_laws b.anti b.square H.val hsym,
    hermitianValue_nondegenerate b.anti H, hnorm, E', ?_, ?_, ?_, ?_⟩
  · intro R _ _ x
    exact matrixCoordinates_pure (F := K) (R := R) e x
  · intro R _ _
    let bR := extendAnti b.anti R
    let HR := H.val.map (intoTensor (F := K) R B)
    have hHR : dagger bR HR = HR := by
      ext i j
      change antiValue bR (1 ⊗ₜ[K] H.val j i) = 1 ⊗ₜ[K] H.val i j
      rw [extendAnti_tmul]
      congr 1
      exact congrArg (fun X : Matrix (Fin r) (Fin r) B => X i j) hsym
    exact hermitianValue_laws bR (extendAnti_square b.anti b.square) HR hHR
  · intro R _ _ g
    exact quaternion_point_compare (F := K) (R := R) s.anti b.anti H e h g
  · intro R S _ _ _ _ f x
    exact matrixBaseChange_natural f e x

end Quaternion

end

end LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
