import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormsOrthogonal
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanDecompositionSignature
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.OrthogonalCompactGeometry
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.OrthogonalDiagramReduction
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.OrthogonalInvolutionNormalForms
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Choose.Basic

noncomputable section

open scoped TensorProduct
open Matrix LieAlgebra LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature

namespace LieAlgebrasAndRepresentations.RealFormsOrthogonal

open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (IsCompact involutionConjugation)
open Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts (complexMatrix_transpose)

attribute [local instance 100] LieRing.ofAssociativeRing

theorem matrix_real_form : matrix_real_form_type := by
  intro ι _ _ A h hs
  exact fixed_isRealForm (matrixConjugation A h hs)

theorem matrix_fixed_iff : matrix_fixed_iff_type := by
  intro ι _ _ A h hs X
  change (matrixConjugation A h hs).map X = X ↔ _
  rw [← Subtype.val_inj, matrixConjugation_val]
  constructor
  · intro hx
    calc
      _ = ((complexMatrix A * conjMatrix X.val) * (complexMatrix A)ᵀ) * complexMatrix A := by
        rw [mul_assoc (complexMatrix A * conjMatrix X.val), complex_orthogonal_left h, mul_one]
      _ = _ := congrArg (· * complexMatrix A) hx
  · intro hx
    rw [hx, mul_assoc, complex_orthogonal_right h, mul_one]

private theorem complexMatrix_injective {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Function.Injective (complexMatrix : Matrix ι ι ℝ → Matrix ι ι ℂ) := by
  intro A B h
  ext i j
  exact Complex.ofReal_injective (congrFun (congrFun h i) j)

private theorem complexMatrix_signature (p q : ℕ) :
    complexMatrix (signatureMatrix p q) = Orthogonal.indefiniteDiagonal (Fin p) (Fin q) ℂ := by
  ext i j
  cases i <;> cases j <;> simp [signatureMatrix, Orthogonal.indefiniteDiagonal, Matrix.diagonal]
  all_goals split <;> simp

section Signature

variable (p q : ℕ)

local notation "Mℂ" => Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ
local notation "P" => Orthogonal.Pso (Fin p) (Fin q) ℂ Complex.I
local notation "Q" => Orthogonal.Pso (Fin p) (Fin q) ℂ (-Complex.I)
local notation "D" => Orthogonal.indefiniteDiagonal (Fin p) (Fin q) ℂ

private theorem signature_mul_Pso : D * P = Q := by
  unfold Orthogonal.indefiniteDiagonal Orthogonal.Pso
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    cases i <;> simp
  · simp [Matrix.diagonal_apply_ne _ h]

private theorem Pso_mul_signature : Q * D = P := by
  unfold Orthogonal.indefiniteDiagonal Orthogonal.Pso
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    cases i <;> simp
  · simp [Matrix.diagonal_apply_ne _ h]

private theorem conjMatrix_Pso (z : ℂ) :
    conjMatrix (Orthogonal.Pso (Fin p) (Fin q) ℂ z) =
      Orthogonal.Pso (Fin p) (Fin q) ℂ (star z) := by
  ext i j
  by_cases h : i = j
  · subst j
    cases i <;> simp [Orthogonal.Pso]
  · simp [Orthogonal.Pso, Matrix.diagonal_apply_ne _ h]

private theorem signature_transport (Y : Mℂ) :
    D * conjMatrix (Q * Y * P) * D = Q * conjMatrix Y * P := by
  have hm : ∀ B C : Mℂ, conjMatrix (B * C) = conjMatrix B * conjMatrix C :=
    map_mul (Complex.conjAe.toRingEquiv.mapMatrix)
  rw [hm, hm, conjMatrix_Pso, conjMatrix_Pso]
  have hi : star Complex.I = -Complex.I := Complex.conj_I
  rw [star_neg, hi, neg_neg]
  calc
    _ = (D * P) * conjMatrix Y * (Q * D) := by noncomm_ring
    _ = _ := by rw [signature_mul_Pso, Pso_mul_signature]

private theorem Pso_inverse : P⁻¹ = Q :=
  Matrix.inv_eq_right_inv (Orthogonal.pso_inv (Fin p) (Fin q) ℂ Complex.I_mul_I)

private def indefiniteEquiv :
    Orthogonal.so' (Fin p) (Fin q) ℂ ≃ₗ⁅ℂ⁆ so (Fin p ⊕ Fin q) :=
  Orthogonal.soIndefiniteEquiv (Fin p) (Fin q) ℂ Complex.I_mul_I

private theorem indefiniteEquiv_val (Y : Orthogonal.so' (Fin p) (Fin q) ℂ) :
    (indefiniteEquiv p q Y).val = Q * Y.val * P :=
  (Orthogonal.soIndefiniteEquiv_apply (Fin p) (Fin q) ℂ Complex.I_mul_I Y).trans (by
    rw [Pso_inverse])

private theorem complexMatrix_mem_signature (Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ) :
    complexMatrix Y ∈ Orthogonal.so' (Fin p) (Fin q) ℂ ↔ Y ∈ soSignature p q := by
  change complexMatrix Y ∈ skewAdjointMatricesLieSubalgebra D ↔
    Y ∈ skewAdjointMatricesLieSubalgebra (signatureMatrix p q)
  simp only [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule,
    Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  rw [← complexMatrix_signature, ← complexMatrix_transpose]
  have hm : ∀ A B : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ,
      complexMatrix (A * B) = complexMatrix A * complexMatrix B :=
    map_mul Complex.ofRealHom.mapMatrix
  have hn : complexMatrix (-Y) = -complexMatrix Y := map_neg Complex.ofRealHom.mapMatrix Y
  rw [← hn, ← hm, ← hm]
  exact complexMatrix_injective.eq_iff

private def complexifySignature : soSignature p q →ₗ⁅ℝ⁆ Orthogonal.so' (Fin p) (Fin q) ℂ where
  toFun Y := ⟨complexMatrix Y.val, (complexMatrix_mem_signature p q Y.val).2 Y.property⟩
  map_add' X Y := Subtype.ext (map_add Complex.ofRealHom.mapMatrix X.val Y.val)
  map_smul' c Y := Subtype.ext <| Matrix.ext fun i j => by
    change ((c * Y.val i j : ℝ) : ℂ) = c • (Y.val i j : ℂ)
    rw [Complex.real_smul, Complex.ofReal_mul]
  map_lie' {X Y} := Subtype.ext <| by
    change complexMatrix (X.val * Y.val - Y.val * X.val) =
      complexMatrix X.val * complexMatrix Y.val - complexMatrix Y.val * complexMatrix X.val
    exact (map_sub Complex.ofRealHom.mapMatrix _ _).trans
      (congrArg₂ Sub.sub (map_mul Complex.ofRealHom.mapMatrix _ _)
        (map_mul Complex.ofRealHom.mapMatrix _ _))

private theorem signature_acts (Y : Orthogonal.so' (Fin p) (Fin q) ℂ) :
    ((signatureConjugation p q).map (indefiniteEquiv p q Y)).val =
      Q * conjMatrix Y.val * P := by
  change complexMatrix (signatureMatrix p q) * conjMatrix (indefiniteEquiv p q Y).val *
    (complexMatrix (signatureMatrix p q))ᵀ = _
  rw [indefiniteEquiv_val, complexMatrix_signature]
  have ht : Dᵀ = D := Matrix.diagonal_transpose _
  rw [ht, signature_transport]

private def intoSignatureFixed : soSignature p q →ₗ⁅ℝ⁆ (signatureConjugation p q).fixed where
  toFun Y := ⟨indefiniteEquiv p q (complexifySignature p q Y), by
    change (signatureConjugation p q).map (indefiniteEquiv p q (complexifySignature p q Y)) = _
    apply Subtype.ext
    rw [signature_acts, indefiniteEquiv_val]
    change Q * conjMatrix (complexMatrix Y.val) * P = Q * complexMatrix Y.val * P
    rw [conjMatrix_complexMatrix]⟩
  map_add' X Y := Subtype.ext <| by
    change indefiniteEquiv p q (complexifySignature p q (X + Y)) = _
    rw [map_add, map_add]
    rfl
  map_smul' c Y := Subtype.ext <| by
    change indefiniteEquiv p q (complexifySignature p q (c • Y)) =
      c • indefiniteEquiv p q (complexifySignature p q Y)
    rw [map_smul]
    exact ((indefiniteEquiv p q).toLinearEquiv.restrictScalars ℝ).map_smul _ _
  map_lie' {X Y} := Subtype.ext <| by
    change indefiniteEquiv p q (complexifySignature p q ⁅X, Y⁆) = _
    rw [(complexifySignature p q).map_lie, (indefiniteEquiv p q).map_lie]
    rfl

private theorem signature_model_aux :
    Nonempty (soSignature p q ≃ₗ⁅ℝ⁆ (signatureConjugation p q).fixed) := by
  refine ⟨LieEquiv.ofBijective (intoSignatureFixed p q) ⟨?_, ?_⟩⟩
  · intro X Y h
    have hv : indefiniteEquiv p q (complexifySignature p q X) =
        indefiniteEquiv p q (complexifySignature p q Y) := congrArg Subtype.val h
    exact Subtype.ext (complexMatrix_injective (congrArg Subtype.val ((indefiniteEquiv p q).injective hv)))
  · intro X
    let Y := (indefiniteEquiv p q).symm X.val
    have hex : indefiniteEquiv p q Y = X.val := (indefiniteEquiv p q).apply_symm_apply X.val
    have hfixed : (signatureConjugation p q).map (indefiniteEquiv p q Y) =
        indefiniteEquiv p q Y := by rw [hex]; exact X.property
    have hv : Q * conjMatrix Y.val * P = Q * Y.val * P := by
      calc
        _ = ((signatureConjugation p q).map (indefiniteEquiv p q Y)).val :=
          (signature_acts p q Y).symm
        _ = (indefiniteEquiv p q Y).val := congrArg (fun x : so (Fin p ⊕ Fin q) => x.val) hfixed
        _ = _ := indefiniteEquiv_val p q Y
    have hpq : P * Q = 1 := Orthogonal.pso_inv (Fin p) (Fin q) ℂ Complex.I_mul_I
    have cancel (T : Mℂ) : P * (Q * T * P) * Q = T := by
      calc
        _ = (P * Q) * T * (P * Q) := by noncomm_ring
        _ = _ := by rw [hpq, one_mul, mul_one]
    have hc : conjMatrix Y.val = Y.val :=
      (cancel _).symm.trans ((congrArg (fun T : Mℂ => P * T * Q) hv).trans (cancel _))
    let Z : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ := Y.val.map Complex.re
    have hz : complexMatrix Z = Y.val := by
      ext i j
      have h := congrFun (congrFun hc i) j
      change star (Y.val i j) = Y.val i j at h
      have hi := congrArg Complex.im h
      have hzero : (Y.val i j).im = 0 := by
        change -(Y.val i j).im = (Y.val i j).im at hi
        linarith
      apply Complex.ext
      · simp [Z]
      · simpa [Z] using hzero.symm
    have hm : complexMatrix Z ∈ Orthogonal.so' (Fin p) (Fin q) ℂ := by
      rw [hz]
      exact Y.property
    refine ⟨⟨Z, (complexMatrix_mem_signature p q Z).mp hm⟩, ?_⟩
    apply Subtype.ext
    change indefiniteEquiv p q (complexifySignature p q _) = X.val
    rw [← hex]
    exact congrArg (indefiniteEquiv p q) (Subtype.ext hz)

end Signature

theorem signature_model : signature_model_type := signature_model_aux

theorem orthogonalAction_fixed_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (h : IsOrthogonal A) (X : so ι) :
    X ∈ complexFixed (orthogonalAction A h) ↔
      complexMatrix A * X.val = X.val * complexMatrix A := by
  change orthogonalAction A h X = X ↔ _
  rw [← Subtype.val_inj, orthogonalAction_val]
  constructor
  · intro hx
    calc
      _ = (complexMatrix A * X.val * (complexMatrix A)ᵀ) * complexMatrix A := by
        rw [mul_assoc (complexMatrix A * X.val), complex_orthogonal_left h, mul_one]
      _ = _ := congrArg (· * complexMatrix A) hx
  · intro hx
    rw [hx, mul_assoc, complex_orthogonal_right h, mul_one]

section SignatureCompact

variable (p q : ℕ)

local notation "M" => Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ
local notation "K" => complexFixed (orthogonalAction (signatureMatrix p q) (signature_orthogonal p q))

private theorem signature_eq_blocks :
    complexMatrix (signatureMatrix p q) = (fromBlocks 1 0 0 (-1) : M) := by
  rw [complexMatrix_signature]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Orthogonal.indefiniteDiagonal, Matrix.diagonal, Matrix.one_apply]
  split <;> simp

private theorem neg_eq_self_zero {a b : Type*} (X : Matrix a b ℂ) (h : -X = X) : X = 0 := by
  have hd : (2 : ℂ) • X = 0 := by
    rw [two_smul]
    exact ((congrArg (· + X) h).symm).trans (neg_add_cancel X)
  exact (smul_eq_zero.mp hd).resolve_left (by norm_num)

private theorem signature_commutes_iff (X : M) :
    complexMatrix (signatureMatrix p q) * X = X * complexMatrix (signatureMatrix p q) ↔
      X.toBlocks₁₂ = 0 ∧ X.toBlocks₂₁ = 0 := by
  rw [signature_eq_blocks]
  conv_lhs =>
    lhs
    rw [← fromBlocks_toBlocks X]
  conv_lhs =>
    rhs
    rw [← fromBlocks_toBlocks X]
  simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.one_mul, Matrix.neg_mul,
    Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, add_zero, zero_add, Matrix.fromBlocks_inj, true_and, and_true]
  constructor
  · intro ⟨h₁₂, h₂₁⟩
    exact ⟨neg_eq_self_zero _ h₁₂.symm, neg_eq_self_zero _ h₂₁⟩
  · rintro ⟨h₁₂, h₂₁⟩
    simp [h₁₂, h₂₁]

private def blockDiagonal : (so (Fin p) × so (Fin q)) →ₗ⁅ℂ⁆ K where
  toFun X :=
    ⟨⟨fromBlocks X.1.val 0 0 X.2.val, by
      rw [Orthogonal.mem_so, Matrix.fromBlocks_transpose]
      have hp := (Orthogonal.mem_so _ _ _).mp X.1.property
      have hq := (Orthogonal.mem_so _ _ _).mp X.2.property
      rw [hp, hq]
      ext i j
      cases i <;> cases j <;> simp⟩,
    (orthogonalAction_fixed_iff _ _).2 ((signature_commutes_iff p q _).2 ⟨rfl, rfl⟩)⟩
  map_add' X Y := Subtype.ext <| Subtype.ext <| by
    change fromBlocks (X.1.val + Y.1.val) 0 0 (X.2.val + Y.2.val) =
      (fromBlocks X.1.val 0 0 X.2.val : M) + fromBlocks Y.1.val 0 0 Y.2.val
    ext i j
    cases i <;> cases j <;> simp
  map_smul' c X := Subtype.ext <| Subtype.ext <| by
    change fromBlocks (c • X.1.val) 0 0 (c • X.2.val) =
      c • (fromBlocks X.1.val 0 0 X.2.val : M)
    rw [Matrix.fromBlocks_smul, smul_zero, smul_zero]
  map_lie' {X Y} := Subtype.ext <| Subtype.ext <| by
    change fromBlocks (X.1.val * Y.1.val - Y.1.val * X.1.val) 0 0
      (X.2.val * Y.2.val - Y.2.val * X.2.val) =
      (fromBlocks X.1.val 0 0 X.2.val : M) * fromBlocks Y.1.val 0 0 Y.2.val -
      fromBlocks Y.1.val 0 0 Y.2.val * fromBlocks X.1.val 0 0 X.2.val
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    ext i j
    cases i <;> cases j <;> simp

private theorem signature_compact_aux : Nonempty (K ≃ₗ⁅ℂ⁆ so (Fin p) × so (Fin q)) := by
  refine ⟨(LieEquiv.ofBijective (blockDiagonal p q) ⟨?_, ?_⟩).symm⟩
  · intro X Y h
    have hv : (fromBlocks X.1.val 0 0 X.2.val : M) = fromBlocks Y.1.val 0 0 Y.2.val :=
      congrArg (fun x : K => x.val.val) h
    have hb := Matrix.fromBlocks_inj.mp hv
    exact Prod.ext (Subtype.ext hb.1) (Subtype.ext hb.2.2.2)
  · intro X
    let T := X.val.val
    have ht : Tᵀ = -T := (Orthogonal.mem_so _ _ _).1 X.val.property
    have hb := (signature_commutes_iff p q T).1 ((orthogonalAction_fixed_iff _ _).1 X.property)
    have h₁ : T.toBlocks₁₁ ∈ so (Fin p) := by
      rw [Orthogonal.mem_so]
      exact congrArg Matrix.toBlocks₁₁ ht
    have h₂ : T.toBlocks₂₂ ∈ so (Fin q) := by
      rw [Orthogonal.mem_so]
      exact congrArg Matrix.toBlocks₂₂ ht
    refine ⟨(⟨T.toBlocks₁₁, h₁⟩, ⟨T.toBlocks₂₂, h₂⟩), Subtype.ext (Subtype.ext ?_)⟩
    change fromBlocks T.toBlocks₁₁ 0 0 T.toBlocks₂₂ = T
    rw [← hb.1, ← hb.2, Matrix.fromBlocks_toBlocks]

end SignatureCompact

theorem signature_compact : signature_compact_type := signature_compact_aux

private theorem complexMatrix_quaternionic (n : ℕ) :
    complexMatrix (quaternionicMatrix n) = OrthogonalCompactGeometry.sourceJ n ℂ := by
  change Complex.ofRealHom.mapMatrix (-Matrix.J (Fin n) ℝ) = -Matrix.J (Fin n) ℂ
  rw [map_neg]
  exact congrArg Neg.neg (Matrix.map_J (Fin n) Complex.ofRealHom)

theorem quaternionic_model : quaternionic_model_type := by
  intro n X
  simpa only [soStar, quaternionicConjugation, complexMatrix_quaternionic] using
    matrix_fixed_iff (quaternionicMatrix n) (quaternionic_orthogonal n)
      (Or.inr (quaternionic_square n)) X

theorem quaternionic_compact : quaternionic_compact_type := by
  intro n
  apply OrthogonalCompactGeometry.quaternionic_automorphism
  intro X
  rw [orthogonalAction_val, complexMatrix_quaternionic]

theorem coefficient_compact : coefficient_compact_type := OrthogonalCompactGeometry.compact

section Centralizer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem orthogonal_involution_imp_square (hcard : 2 < Fintype.card ι)
    {A : Matrix ι ι ℝ} (hA : IsOrthogonal A) (hθ : Function.Involutive (orthogonalAction A hA)) :
    A * A = 1 ∨ A * A = -1 := by
  let B := complexMatrix A
  have hB : Bᵀ * B = 1 := complex_orthogonal_left hA
  have hBB : (B * B)ᵀ * (B * B) = 1 := by
    rw [Matrix.transpose_mul]
    calc
      _ = Bᵀ * (Bᵀ * B) * B := by noncomm_ring
      _ = _ := by rw [hB, mul_one, hB]
  have hcomm (X : so ι) : (B * B) * X.val = X.val * (B * B) := by
    have hx : B * (B * X.val * Bᵀ) * Bᵀ = X.val :=
      congrArg (fun Z : so ι => Z.val) (hθ X)
    calc
      _ = ((B * B) * X.val) * ((B * B)ᵀ * (B * B)) := by rw [hBB, mul_one]
      _ = (B * (B * X.val * Bᵀ) * Bᵀ) * (B * B) := by rw [Matrix.transpose_mul]; noncomm_ring
      _ = _ := by rw [hx]
  obtain ⟨c, hc⟩ :=
    OrthogonalInnerMatrixLifts.commuting_with_skew_is_scalar hcard (B * B) hcomm
  rw [hc, Matrix.transpose_smul, Matrix.transpose_one, smul_mul_smul_comm, one_mul] at hBB
  obtain ⟨i, _, _, _⟩ := Fintype.two_lt_card_iff.mp hcard
  have hsq : c * c = 1 := by
    simpa using congrArg (fun M : Matrix ι ι ℂ => M i i) hBB
  have hsign : c = 1 ∨ c = -1 := by
    have hz : (c - 1) * (c + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hmap : complexMatrix (A * A) = B * B := map_mul Complex.ofRealHom.mapMatrix _ _
  rcases hsign with h | h
  · left
    apply complexMatrix_injective
    change _ = Complex.ofRealHom.mapMatrix 1
    rw [map_one, hmap, hc, h, one_smul]
  · right
    apply complexMatrix_injective
    change _ = Complex.ofRealHom.mapMatrix (-1)
    rw [map_neg, map_one, hmap, hc, h, neg_one_smul]

end Centralizer

theorem orthogonal_involution_iff : orthogonal_involution_iff_type := by
  intro ι _ _ hcard A h
  exact ⟨orthogonal_involution_imp_square hcard h, orthogonalAction_involutive h⟩

section Reduction

open Specs.LieAlgebrasAndRepresentations.OrthogonalDiagramReduction
  (toAut reflectionMatrix)
open Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts
  (HasComplexRepresentative HasRealRepresentative CommutesWithConjugation)
local notation "innerAut" => Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition.inner

theorem compact_matrix_reduction : compact_matrix_reduction_type := by
  intro N hN θ hθ hθ₂
  have hsize : N = 3 ∨ 5 ≤ N := hN
  have hcard : 2 < Fintype.card (Fin N) := by simpa using (show 2 < N by omega)
  let j : Fin N := ⟨0, by omega⟩
  let ω := coefficientConjugation (Fin N)
  obtain ⟨v, r, hv, hr, hg⟩ := OrthogonalDiagramReduction.involutionReduction
    (Fin N) (OrthogonalCompactGeometry.semisimple N hN).2 (by simpa using hsize)
    ω (fun _ _ _ => rfl) (coefficient_compact N hN) θ hθ₂ j
  let a := (v.symm.trans θ).trans v
  have ha (X : so (Fin N)) : a (v X) = v (θ X) := by
    change v (θ (v.symm (v X))) = _
    rw [v.symm_apply_apply]
  have hcomm : Intertwines ω ω a := by
    intro X
    obtain ⟨Y, rfl⟩ := v.surjective X
    change ω.map (a (v Y)) = a (ω.map (v Y))
    rw [ha, hv, hv, ha, hθ]
  have hinv : Function.Involutive a := by
    intro X
    obtain ⟨Y, rfl⟩ := v.surjective X
    change a (a (v Y)) = v Y
    rw [ha, ha, hθ₂]
  change toAut a ∈ innerAut (so (Fin N)) ∨ toAut a * (toAut r)⁻¹ ∈ innerAut (so (Fin N)) at hg
  have hcomm' : CommutesWithConjugation (toAut a) := hcomm
  obtain ⟨A, hA, hrep⟩ : HasRealRepresentative (toAut a) := by
    rcases hg with hi | hi
    · exact OrthogonalInnerMatrixLifts.complex_has_real_representative hcard _
        (OrthogonalInnerMatrixLifts.inner_has_complex_representative hcard _ hi) hcomm'
    · have hR : IsOrthogonal (reflectionMatrix (Fin N) j) :=
        (OrthogonalDiagramReduction.reflectionMatrix_properties (Fin N) j).1
      have hrep : HasComplexRepresentative (toAut r) := by
        refine ⟨complexMatrix (reflectionMatrix (Fin N) j), complex_orthogonal_left hR, ?_⟩
        apply Subtype.ext
        ext X : 1
        exact Subtype.ext (hr X)
      exact OrthogonalInnerMatrixLifts.real_representative_of_inner_difference hcard hi hrep hcomm'
  have he : a = orthogonalAction A hA := by
    ext X : 1
    exact congrArg (fun g => g.val X) hrep
  refine ⟨A, hA, (orthogonal_involution_iff hcard A hA).mp (he ▸ hinv), v, hv, fun X => ?_⟩
  rw [← he, ha]

theorem matrix_normal_forms : matrix_normal_forms_type := by
  intro ι _ _ A hA
  exact ⟨OrthogonalInvolutionNormalForms.squareOne A hA,
    OrthogonalInvolutionNormalForms.squareNegOne A hA⟩

end Reduction

private theorem involutionConjugation_intertwines {L H : Type*}
    [LieRing L] [LieAlgebra ℂ L] [LieRing H] [LieAlgebra ℂ H]
    {ω : Conjugation L} {ω' : Conjugation H} {a : L ≃ₗ⁅ℂ⁆ L} {b : H ≃ₗ⁅ℂ⁆ H}
    {ha : Intertwines ω ω a} {hb : Intertwines ω' ω' b}
    {ha₂ : Function.Involutive a} {hb₂ : Function.Involutive b}
    (v : L ≃ₗ⁅ℂ⁆ H) (hv : Intertwines ω ω' v) (h : ∀ x, v (a x) = b (v x)) :
    Intertwines (involutionConjugation ω a ha ha₂) (involutionConjugation ω' b hb hb₂) v := by
  intro x
  change b (ω'.map (v x)) = v (a (ω.map x))
  rw [hv, h]

section Reindex

variable {R ι κ : Type} [CommRing R] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private def skewReindex (e : ι ≃ κ) (D : Matrix ι ι R) :
    skewAdjointMatricesLieSubalgebra D ≃ₗ⁅R⁆
      skewAdjointMatricesLieSubalgebra (Matrix.reindex e e D) := by
  let r : Matrix ι ι R ≃ₗ⁅R⁆ Matrix κ κ R := Matrix.reindexLieEquiv e
  let F := Matrix.reindexAlgEquiv R R e
  have hz (A : Matrix ι ι R) :
      A ∈ skewAdjointMatricesLieSubalgebra D ↔
        r A ∈ skewAdjointMatricesLieSubalgebra (F D) := by
    simp only [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule,
      Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
    change Aᵀ * D = D * (-A) ↔ (F A)ᵀ * F D = F D * (-F A)
    have ht : (F A)ᵀ = F Aᵀ := Matrix.transpose_reindex e e A
    rw [ht, ← map_neg F, ← map_mul, ← map_mul, F.injective.eq_iff]
  refine LieEquiv.ofSubalgebras _ _ r ?_
  ext B
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨A, hA, hB⟩
    change r A = B at hB
    rw [← hB]
    exact (hz A).mp hA
  · intro hB
    refine ⟨r.symm B, (hz _).mpr ?_, r.apply_symm_apply B⟩
    rwa [r.apply_symm_apply]

end Reindex

theorem compact_signature : compact_signature_type := by
  intro p
  let e := Equiv.sumEmpty (Fin p) (Fin 0)
  have hd : Matrix.reindex e e (signatureMatrix p 0) = (1 : Matrix (Fin p) (Fin p) ℝ) := by
    ext i j
    change signatureMatrix p 0 (Sum.inl i) (Sum.inl j) = _
    simp [Orthogonal.indefiniteDiagonal, Matrix.diagonal, Matrix.one_apply]
  refine ⟨(skewReindex e (signatureMatrix p 0)).trans (LieEquiv.ofEq _ _ ?_)⟩
  rw [hd]
  rfl

theorem compact_signature_killing : compact_signature_killing_type := by
  intro p hp X hX
  obtain ⟨e⟩ := compact_signature p
  obtain ⟨f, _⟩ := OrthogonalCompactGeometry.coefficient_fixed p
  let g := e.trans f
  rw [← LieAlgebra.killingForm_of_equiv_apply g]
  exact coefficient_compact p hp (g X) fun hz => hX (g.injective (by simpa using hz))

theorem signature_swap : signature_swap_type := by
  intro p q
  let e := Equiv.sumComm (Fin p) (Fin q)
  have hd : Matrix.reindex e e (signatureMatrix p q) = -(signatureMatrix q p) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [e, Matrix.reindex_apply, Matrix.submatrix_apply, Orthogonal.indefiniteDiagonal,
        Matrix.diagonal]
    all_goals split <;> simp
  refine ⟨(skewReindex e (signatureMatrix p q)).trans (LieEquiv.ofEq _ _ ?_)⟩
  rw [hd]
  ext A
  change A ∈ skewAdjointMatricesLieSubalgebra (-(signatureMatrix q p)) ↔
    A ∈ skewAdjointMatricesLieSubalgebra (signatureMatrix q p)
  simp only [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule,
    Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, mul_neg, neg_mul, neg_neg]
  constructor <;> intro h <;> simpa using congrArg Neg.neg h

private def reindexSo {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) : so ι ≃ₗ⁅ℂ⁆ so κ := by
  refine (skewReindex e (1 : Matrix ι ι ℂ)).trans (LieEquiv.ofEq _ _ ?_)
  have h : Matrix.reindex e e (1 : Matrix ι ι ℂ) = 1 :=
    map_one (Matrix.reindexAlgEquiv ℂ ℂ e)
  rw [h]
  rfl

private theorem reindexSo_commutes {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) :
    Intertwines (coefficientConjugation ι) (coefficientConjugation κ) (reindexSo e) := by
  intro X
  exact Subtype.ext rfl

private theorem fixed_equiv_of_normal_form {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : κ ≃ ι) {A Q : Matrix ι ι ℝ} {B : Matrix κ κ ℝ}
    (hA : IsOrthogonal A) (hQ : IsOrthogonal Q) (hB : IsOrthogonal B)
    (hA₂ : A * A = 1 ∨ A * A = -1) (hB₂ : B * B = 1 ∨ B * B = -1)
    (h : Qᵀ * A * Q = Matrix.reindex e e B) :
    Nonempty ((matrixConjugation B hB hB₂).fixed ≃ₗ⁅ℝ⁆ (matrixConjugation A hA hA₂).fixed) := by
  let F := Matrix.reindexAlgEquiv ℂ ℂ e
  let v := (reindexSo e).trans (orthogonalAction Q hQ)
  have hmul : A * Q = Q * Matrix.reindex e e B := by
    rw [← h, ← mul_assoc Q (Qᵀ * A), ← mul_assoc Q Qᵀ A, orthogonal_right hQ, one_mul]
  have hprod : complexMatrix A * complexMatrix Q = complexMatrix Q * F (complexMatrix B) := by
    change Complex.ofRealHom.mapMatrix A * Complex.ofRealHom.mapMatrix Q =
      Complex.ofRealHom.mapMatrix Q * Complex.ofRealHom.mapMatrix (Matrix.reindex e e B)
    rw [← map_mul, ← map_mul, hmul]
  have hv : Intertwines (coefficientConjugation κ) (coefficientConjugation ι) v := by
    intro X
    change (coefficientConjugation ι).map (orthogonalAction Q hQ (reindexSo e X)) =
      orthogonalAction Q hQ (reindexSo e ((coefficientConjugation κ).map X))
    rw [orthogonalAction_commutes hQ, reindexSo_commutes e]
  have ha (X : so κ) : v (orthogonalAction B hB X) = orthogonalAction A hA (v X) := by
    apply Subtype.ext
    let C := complexMatrix Q
    let D := complexMatrix A
    let E := complexMatrix B
    change C * F (E * X.val * Eᵀ) * Cᵀ = D * (C * F X.val * Cᵀ) * Dᵀ
    have ht : F Eᵀ = (F E)ᵀ := (Matrix.transpose_reindex e e E).symm
    rw [map_mul F, map_mul F, ht]
    calc
      _ = (C * F E) * F X.val * (C * F E)ᵀ := by rw [Matrix.transpose_mul]; noncomm_ring
      _ = (D * C) * F X.val * (D * C)ᵀ := by rw [show D * C = C * F E from hprod]
      _ = _ := by rw [Matrix.transpose_mul]; noncomm_ring
  obtain ⟨f, _⟩ := restrict_complex_isomorphism (matrixConjugation B hB hB₂)
    (matrixConjugation A hA hA₂) v (involutionConjugation_intertwines v hv ha)
  exact ⟨f⟩

private theorem reindexRealForm {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (τ : Conjugation (so ι)) :
    ∃ S : LieSubalgebra ℝ (so κ), IsRealForm S ∧ Nonempty (τ.fixed ≃ₗ⁅ℝ⁆ S) := by
  let r := reindexSo e
  let σ := τ.transport r
  have hi : Intertwines τ σ r := by
    intro x
    change r (τ.map (r.symm (r x))) = r (τ.map x)
    rw [r.symm_apply_apply]
  obtain ⟨f, _⟩ := restrict_complex_isomorphism τ σ r hi
  exact ⟨σ.fixed, fixed_isRealForm σ, ⟨f⟩⟩

theorem model_existence : model_existence_type := by
  constructor
  · intro p q
    let e : Fin p ⊕ Fin q ≃ Fin (p + q) := Fintype.equivOfCardEq (by simp)
    obtain ⟨S, hs, ⟨g⟩⟩ := reindexRealForm e (signatureConjugation p q)
    obtain ⟨f⟩ := signature_model p q
    exact ⟨S, hs, ⟨f.trans g⟩⟩
  · intro n
    let e : Fin n ⊕ Fin n ≃ Fin (n + n) := Fintype.equivOfCardEq (by simp)
    exact reindexRealForm e (quaternionicConjugation n)

theorem exhaustion : exhaustion_type := by
  intro N hN S hS
  let ω := coefficientConjugation (Fin N)
  obtain ⟨_, θ, hcomm, hinv, _, _, ⟨f⟩⟩ :=
    PolarRealStructures.real_form_reduction ω (coefficient_compact N hN) S hS
  obtain ⟨A, hA, hA₂, v, hv, h⟩ := compact_matrix_reduction N hN θ hcomm hinv
  obtain ⟨g, _⟩ := restrict_complex_isomorphism (involutionConjugation ω θ hcomm hinv)
    (matrixConjugation A hA hA₂) v (involutionConjugation_intertwines v hv h)
  rcases hA₂ with hpos | hneg
  · obtain ⟨p, q, e, Q, hQ, hsim⟩ := (matrix_normal_forms A hA).1 hpos
    have hsize : p + q = N := by simpa using Fintype.card_congr e
    obtain ⟨j⟩ := fixed_equiv_of_normal_form e hA hQ (signature_orthogonal p q) (Or.inl hpos)
      (Or.inl (signature_square p q)) hsim
    obtain ⟨k⟩ := signature_model p q
    exact Or.inl ⟨p, q, hsize, ⟨f.trans (g.trans (j.symm.trans k.symm))⟩⟩
  · obtain ⟨_, n, e, Q, hQ, hsim⟩ := (matrix_normal_forms A hA).2 hneg
    have hsize : n + n = N := by simpa using Fintype.card_congr e
    obtain ⟨j⟩ := fixed_equiv_of_normal_form e hA hQ (quaternionic_orthogonal n) (Or.inr hneg)
      (Or.inr (quaternionic_square n)) hsim
    exact Or.inr ⟨n, hsize, ⟨f.trans (g.trans j.symm)⟩⟩

section Separation

private theorem coefficient_compact_of_card {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : IsSimpleSize (Fintype.card ι)) : IsCompact (coefficientConjugation ι) := by
  let e := Fintype.equivFin ι
  obtain ⟨f, _⟩ := restrict_complex_isomorphism _ _ (reindexSo e) (reindexSo_commutes e)
  intro x hx
  rw [← LieAlgebra.killingForm_of_equiv_apply f]
  exact coefficient_compact _ h (f x) fun hzero => hx (f.injective (by simpa using hzero))

private def fixedEquiv {L H : Type*}
    [LieRing L] [LieAlgebra ℂ L] [LieRing H] [LieAlgebra ℂ H]
    {a : L ≃ₗ⁅ℂ⁆ L} {b : H ≃ₗ⁅ℂ⁆ H} (v : L ≃ₗ⁅ℂ⁆ H)
    (h : ∀ x, v (a x) = b (v x)) : complexFixed a ≃ₗ⁅ℂ⁆ complexFixed b := by
  apply LieEquiv.ofSubalgebras _ _ v
  ext y
  obtain ⟨x, rfl⟩ := v.surjective y
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨z, hz, hz'⟩
    have he : z = x := v.injective hz'
    subst z
    change b (v x) = v x
    rw [← h, show a x = x from hz]
  · intro hx
    exact ⟨x, v.injective ((h x).trans hx), rfl⟩

open private compact_intertwiner from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

private theorem matrix_compact_fixed_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (hc : IsCompact (coefficientConjugation ι))
    {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ} (hA : IsOrthogonal A) (hB : IsOrthogonal B)
    (hA₂ : A * A = 1 ∨ A * A = -1) (hB₂ : B * B = 1 ∨ B * B = -1)
    (f : (matrixConjugation A hA hA₂).fixed ≃ₗ⁅ℝ⁆ (matrixConjugation B hB hB₂).fixed) :
    Nonempty (complexFixed (orthogonalAction A hA) ≃ₗ⁅ℂ⁆ complexFixed (orthogonalAction B hB)) := by
  let v := reindexSo e
  let ω := coefficientConjugation ι
  let ω' := coefficientConjugation κ
  let a := orthogonalAction A hA
  let b := orthogonalAction B hB
  let c := (v.trans b).trans v.symm
  have he (x : so ι) : v (c x) = b (v x) := by
    change v (v.symm (b (v x))) = _
    rw [v.apply_symm_apply]
  have hv : Intertwines ω ω' v := reindexSo_commutes e
  have hb : Intertwines ω' ω' b := orthogonalAction_commutes hB
  have hb₂ : Function.Involutive b := orthogonalAction_involutive hB hB₂
  have hcomm : Intertwines ω ω c := by
    intro x
    apply v.injective
    change v (ω.map (c x)) = v (c (ω.map x))
    rw [← hv (c x), he, hb, hv x, he]
  have hinv : Function.Involutive c := by
    intro x
    apply v.injective
    change v (c (c x)) = v x
    rw [he, he, hb₂]
  let τ := involutionConjugation ω c hcomm hinv
  have hτ : Intertwines τ (matrixConjugation B hB hB₂) v :=
    involutionConjugation_intertwines v hv he
  obtain ⟨g, _⟩ := restrict_complex_isomorphism τ (matrixConjugation B hB hB₂) v hτ
  obtain ⟨x, hx⟩ := (forms_isomorphic_iff (matrixConjugation A hA hA₂) τ).mp ⟨f.trans g.symm⟩
  obtain ⟨w, _, hw⟩ := compact_intertwiner ω hc a c
    (orthogonalAction_commutes hA) hcomm (orthogonalAction_involutive hA hA₂) hinv x hx
  exact ⟨(fixedEquiv w (fun x => (hw x).symm)).trans (fixedEquiv v he)⟩

private theorem center_finrank_eq {L H : Type*}
    [LieRing L] [LieAlgebra ℂ L] [LieRing H] [LieAlgebra ℂ H] (e : L ≃ₗ⁅ℂ⁆ H) :
    Module.finrank ℂ (LieAlgebra.center ℂ L) = Module.finrank ℂ (LieAlgebra.center ℂ H) := by
  apply LinearEquiv.finrank_eq (e.toLinearEquiv.ofSubmodules _ _ ?_)
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hz'⟩
    have he : z = x := e.injective hz'
    subst z
    change e x ∈ LieAlgebra.center ℂ H
    have hL := (LieModule.mem_maxTrivSubmodule ℂ L L x).mp hz
    refine (LieModule.mem_maxTrivSubmodule ℂ H H (e x)).mpr ?_
    intro y
    obtain ⟨w, rfl⟩ := e.surjective y
    change ⁅e w, e x⁆ = 0
    rw [← e.map_lie, hL w, map_zero]
  · intro hx
    change e x ∈ LieAlgebra.center ℂ H at hx
    refine ⟨x, (LieModule.mem_maxTrivSubmodule ℂ L L x).mpr ?_, rfl⟩
    intro z
    apply e.injective
    change e ⁅z, x⁆ = e 0
    rw [e.map_lie, (LieModule.mem_maxTrivSubmodule ℂ H H (e x)).mp hx (e z), map_zero]

private theorem twice_triangle (m : ℕ) :
    2 * ((m * (m - 1) / 2 : ℕ) : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.triangle_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    linear_combination ih

private theorem twice_signed_dimension (p q : ℕ) :
    2 * ((p * (p - 1) / 2 + q * (q - 1) / 2 : ℕ) : ℤ) =
      (p : ℤ) * ((p : ℤ) - 1) + (q : ℤ) * ((q : ℤ) - 1) := by
  rw [Nat.cast_add, mul_add, twice_triangle, twice_triangle]

private theorem unordered_parameters_of_signed_dimension {p q r s : ℕ}
    (hsum : p + q = r + s)
    (hdim : p * (p - 1) / 2 + q * (q - 1) / 2 = r * (r - 1) / 2 + s * (s - 1) / 2) :
    (p = r ∧ q = s) ∨ (p = s ∧ q = r) := by
  have hsumZ : (p : ℤ) + q = (r : ℤ) + s := by exact_mod_cast hsum
  have hdimZ := congrArg (fun d : ℕ => (2 : ℤ) * (d : ℤ)) hdim
  rw [twice_signed_dimension, twice_signed_dimension] at hdimZ
  have hsq := congrArg (fun z : ℤ => z ^ 2) hsumZ
  have hprod : (p : ℤ) * q = (r : ℤ) * s := by nlinarith only [hdimZ, hsumZ, hsq]
  have hzero : ((p : ℤ) - r) * ((p : ℤ) - s) = 0 := by
    calc
      _ = (p : ℤ) ^ 2 - p * ((r : ℤ) + s) + (r : ℤ) * s := by ring
      _ = _ := by rw [← hsumZ, ← hprod]; ring
  rcases mul_eq_zero.mp hzero with h | h
  · have hpr : p = r := by exact_mod_cast sub_eq_zero.mp h
    exact Or.inl ⟨hpr, by omega⟩
  · have hps : p = s := by exact_mod_cast sub_eq_zero.mp h
    exact Or.inr ⟨hps, by omega⟩

theorem signature_isomorphism : signature_isomorphism_type := by
  intro p q r s hsum hsize
  constructor
  · rintro ⟨f⟩
    let e : Fin p ⊕ Fin q ≃ Fin r ⊕ Fin s := Fintype.equivOfCardEq (by simpa using hsum)
    have hc : IsCompact (coefficientConjugation (Fin p ⊕ Fin q)) :=
      coefficient_compact_of_card (by simpa using hsize)
    obtain ⟨f₁⟩ := signature_model p q
    obtain ⟨f₂⟩ := signature_model r s
    obtain ⟨g⟩ := matrix_compact_fixed_equiv e hc (signature_orthogonal p q)
      (signature_orthogonal r s) (Or.inl (signature_square p q)) (Or.inl (signature_square r s))
      (f₁.symm.trans (f.trans f₂))
    obtain ⟨g₁⟩ := signature_compact p q
    obtain ⟨g₂⟩ := signature_compact r s
    have hd := (g₁.symm.trans (g.trans g₂)).toLinearEquiv.finrank_eq
    rw [(OrthogonalCompactGeometry.signed_dimensions p q).1,
      (OrthogonalCompactGeometry.signed_dimensions r s).1] at hd
    exact unordered_parameters_of_signed_dimension hsum hd
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨LieEquiv.refl⟩
    · exact signature_swap p q

private theorem dimension_with_two {a n : ℕ} (hn : 3 ≤ n) (hsum : a + 2 = n + n)
    (hdim : a * (a - 1) / 2 + 2 * (2 - 1) / 2 = n ^ 2) : n = 4 ∧ a = 6 := by
  have ha : (a : ℤ) = 2 * (n : ℤ) - 2 := by
    have h : (a : ℤ) + 2 = (n : ℤ) + (n : ℤ) := by exact_mod_cast hsum
    linarith
  have hd := congrArg (fun d : ℕ => (2 : ℤ) * (d : ℤ)) hdim
  rw [twice_signed_dimension] at hd
  push_cast at hd
  rw [ha] at hd
  have hz : ((n : ℤ) - 1) * ((n : ℤ) - 4) = 0 := by nlinarith only [hd]
  rcases mul_eq_zero.mp hz with h | h
  · have h' : n = 1 := by exact_mod_cast sub_eq_zero.mp h
    omega
  · have h' : n = 4 := by exact_mod_cast sub_eq_zero.mp h
    exact ⟨h', by omega⟩

theorem possible_quaternionic_repetition : possible_quaternionic_repetition_type := by
  intro p q n hsum hsize ⟨f⟩
  have hs : p + q = 3 ∨ 5 ≤ p + q := hsize
  have hn : 3 ≤ n := by omega
  let e : Fin p ⊕ Fin q ≃ Fin n ⊕ Fin n := Fintype.equivOfCardEq (by simpa using hsum)
  have hc : IsCompact (coefficientConjugation (Fin p ⊕ Fin q)) :=
    coefficient_compact_of_card (by simpa using hsize)
  obtain ⟨f₁⟩ := signature_model p q
  obtain ⟨g⟩ := matrix_compact_fixed_equiv e hc (signature_orthogonal p q)
    (quaternionic_orthogonal n) (Or.inl (signature_square p q)) (Or.inr (quaternionic_square n))
    (f₁.symm.trans f)
  obtain ⟨g₁⟩ := signature_compact p q
  obtain ⟨g₂⟩ := quaternionic_compact n
  let G := g₁.symm.trans (g.trans g₂)
  obtain ⟨hd, hz⟩ := OrthogonalCompactGeometry.signed_dimensions p q
  obtain ⟨hd', hz'⟩ := OrthogonalCompactGeometry.general_linear_dimensions ℂ n
  have hdim := G.toLinearEquiv.finrank_eq
  rw [hd, hd'] at hdim
  have hcenter := center_finrank_eq G
  rw [hz, hz' (by omega)] at hcenter
  have htwo : p = 2 ∨ q = 2 := by
    by_contra! h
    simp [h.1, h.2] at hcenter
  rcases htwo with h | h
  · subst p
    have hsum' : q + 2 = n + n := by omega
    obtain ⟨hn', hq⟩ := dimension_with_two hn hsum' (by simpa [Nat.add_comm] using hdim)
    exact ⟨hn', Or.inr ⟨rfl, hq⟩⟩
  · subst q
    obtain ⟨hn', hp⟩ := dimension_with_two hn hsum hdim
    exact ⟨hn', Or.inl ⟨hp, rfl⟩⟩

end Separation

section MaximalCompact

private theorem killing_nonpos_of_compactlyEmbedded {L : Type*}
    [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    {K : LieSubalgebra ℝ L} (hK : IsCompactlyEmbedded K) {x : L} (hx : x ∈ K) :
    _root_.killingForm ℝ L x x ≤ 0 := by
  obtain ⟨B, hsym, hpos, hskew⟩ := hK
  let core : InnerProductSpace.Core ℝ L :=
    { inner := fun y z => B y z
      conj_inner_symm := fun y z => hsym.eq z y
      re_inner_nonneg := fun y => by
        change 0 ≤ B y y
        by_cases hy : y = 0
        · simp [hy]
        · exact (hpos y hy).le
      add_left := fun y z w => B.map_add₂ y z w
      smul_left := fun y z r => by
        change B (r • y) z = r * B y z
        simp
      definite := fun y hy => by
        by_contra h
        exact (hpos y h).ne' hy }
  let : NormedAddCommGroup L := core.toNormedAddCommGroup
  let : InnerProductSpace ℝ L := InnerProductSpace.ofCore core.toCore
  let b := stdOrthonormalBasis ℝ L
  let A := LinearMap.toMatrix b.toBasis b.toBasis (LieAlgebra.ad ℝ L x)
  have ht (i j : Fin (Module.finrank ℝ L)) : A j i = -A i j := by
    simp only [A, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      b.coe_toBasis_repr_apply, b.repr_apply_apply, LieAlgebra.ad_apply]
    change B (b j) ⁅x, b i⁆ = -B (b i) ⁅x, b j⁆
    exact (hsym.eq (b j) _).trans (hskew x hx (b i) (b j))
  rw [killingForm_apply_apply, LinearMap.trace_eq_matrix_trace ℝ b.toBasis,
    ← Module.End.mul_eq_comp, LinearMap.toMatrix_mul]
  change Matrix.trace (A * A) ≤ 0
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_nonpos
  intro i _
  apply Finset.sum_nonpos
  intro j _
  rw [ht i j, mul_neg]
  exact neg_nonpos.mpr (mul_self_nonneg _)

open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (hermitian)
open private hermitianCore hermitian_positive from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
open private cartan_parts_complementary from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanDecompositionSignature

private theorem cartan_maximal_compact {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (ω : Conjugation L) (hc : IsCompact ω) (a : L ≃ₗ⁅ℂ⁆ L)
    (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a) :
    IsMaximalCompact (compactSubalgebra ω (involutionConjugation ω a hcomm hinv)) := by
  let σ := involutionConjugation ω a hcomm hinv
  let S := σ.fixed
  let K := compactSubalgebra ω σ
  let P := compactPart ω a hcomm hinv
  let V := noncompactPart ω a hcomm hinv
  let v : S →ₗ[ℝ] L := σ.fixed.toSubmodule.subtype
  let B : LinearMap.BilinForm ℝ S :=
    ((-(_root_.killingForm ℂ L).restrictScalars₁₂ ℝ ℝ).compl₁₂
      (ω.map.toLinearMap.comp v) v).compr₂ Complex.reCLM.toLinearMap
  have hB (x y : S) : B x y = (hermitian ω (x : L) (y : L)).re := rfl
  refine ⟨⟨B, ⟨fun x y => ?_⟩, fun x hx => ?_, fun x hx y z => ?_⟩, ?_⟩
  · have h := (hermitianCore ω hc).conj_inner_symm (x : L) (y : L)
    change star (hermitian ω (y : L) (x : L)) = hermitian ω (x : L) (y : L) at h
    have h' := congrArg Complex.re h
    change B y x = B x y at h'
    exact h'.symm
  · rw [hB]
    exact hermitian_positive ω hc (fun h => hx (Subtype.ext h))
  · have hfix : ω.map (x : L) = (x : L) := hx
    simp only [hB, hermitian, LieSubalgebra.coe_bracket, ω.map.map_lie, hfix]
    rw [LieModule.traceForm_apply_lie_apply']
    simp
  · intro U hKU hU
    let : FiniteDimensional ℝ L := FiniteDimensional.trans ℝ ℂ L
    let : FiniteDimensional ℝ S :=
      FiniteDimensional.of_injective σ.fixed.toSubmodule.subtype Subtype.val_injective
    apply le_antisymm (fun x hx => ?_) hKU
    have hcompl : IsCompl P V := cartan_parts_complementary ω a hcomm hinv
    have hmem : x ∈ P ⊔ V := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨p, hp, n, hn, he⟩ := Submodule.mem_sup.mp hmem
    have hpK : p ∈ K := hp.1
    have hnU : n ∈ U := by simpa [← he, add_comm p n] using U.sub_mem hx (hKU hpK)
    have hzero : n = 0 := by
      by_contra hz
      exact (not_lt_of_ge (killing_nonpos_of_compactlyEmbedded hU hnU))
        ((CartanDecompositionSignature.cartan_killing ω a hcomm hinv hc).2.1 ⟨n, hn⟩ hz)
    simpa [← he, hzero] using hpK

private def compactSubalgebraEquiv {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a) :
    compactSubalgebra ω (involutionConjugation ω a hcomm hinv) ≃ₗ⁅ℝ⁆
      (fixedConjugation ω a hcomm).fixed where
  toFun x :=
    let y := x.val.val
    have hx : ω.map y = y := x.property
    have hs : a (ω.map y) = y := x.val.property
    ⟨⟨y, by rwa [hx] at hs⟩, Subtype.ext hx⟩
  invFun x :=
    let y := x.val.val
    have hx : ω.map y = y := congrArg Subtype.val x.property
    have ha : a y = y := x.val.property
    ⟨⟨y, show a (ω.map y) = y by rw [hx, ha]⟩, hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

private theorem compactlyEmbedded_map {L H : Type*}
    [LieRing L] [LieAlgebra ℝ L] [LieRing H] [LieAlgebra ℝ H]
    (e : L ≃ₗ⁅ℝ⁆ H) {K : LieSubalgebra ℝ L} (hK : IsCompactlyEmbedded K) :
    IsCompactlyEmbedded (K.map e.toLieHom) := by
  obtain ⟨B, hsym, hpos, hskew⟩ := hK
  let f := e.symm.toLinearEquiv.toLinearMap
  refine ⟨B.compl₁₂ f f, ⟨fun x y => hsym.eq (f x) (f y)⟩, fun x hx => ?_, ?_⟩
  · exact hpos (e.symm x) (fun h => hx (e.symm.injective (by simpa using h)))
  · rintro _ ⟨x, hx, rfl⟩ y z
    change B (e.symm ⁅e x, y⁆) (e.symm z) = -B (e.symm y) (e.symm ⁅e x, z⁆)
    rw [e.symm.map_lie, e.symm.map_lie, e.symm_apply_apply]
    exact hskew x hx (e.symm y) (e.symm z)

private theorem maximalCompact_map {L H : Type*}
    [LieRing L] [LieAlgebra ℝ L] [LieRing H] [LieAlgebra ℝ H]
    (e : L ≃ₗ⁅ℝ⁆ H) {K : LieSubalgebra ℝ L} (hK : IsMaximalCompact K) :
    IsMaximalCompact (K.map e.toLieHom) := by
  refine ⟨compactlyEmbedded_map e hK.1, fun U hKU hU => le_antisymm (fun x hx => ?_) hKU⟩
  have hle : K ≤ U.map e.symm.toLieHom := fun y hy =>
    ⟨e y, hKU ⟨y, hy, rfl⟩, e.symm_apply_apply y⟩
  have h := hK.2 (U.map e.symm.toLieHom) hle (compactlyEmbedded_map e.symm hU)
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem signature_maximal_compact : signature_maximal_compact_type := by
  intro p q hsize
  let ω := coefficientConjugation (Fin p ⊕ Fin q)
  let h := signature_orthogonal p q
  let hs : signatureMatrix p q * signatureMatrix p q = 1 ∨
      signatureMatrix p q * signatureMatrix p q = -1 := Or.inl (signature_square p q)
  let a := orthogonalAction (signatureMatrix p q) h
  let K := compactSubalgebra ω (signatureConjugation p q)
  have hc : IsCompact ω := coefficient_compact_of_card (by simpa using hsize)
  have hK : IsMaximalCompact K :=
    cartan_maximal_compact ω hc a (orthogonalAction_commutes h) (orthogonalAction_involutive h hs)
  obtain ⟨f⟩ := signature_model p q
  let K' := K.map f.symm.toLieHom
  let e : K ≃ₗ⁅ℝ⁆ K' := LieEquiv.ofSubalgebras K K' f.symm rfl
  let g := compactSubalgebraEquiv ω a (orthogonalAction_commutes h) (orthogonalAction_involutive h hs)
  obtain ⟨k, _⟩ := fixed_complexification (fixedConjugation ω a (orthogonalAction_commutes h))
  obtain ⟨j⟩ := signature_compact p q
  exact ⟨K', maximalCompact_map f.symm hK, ⟨(complexifyEquiv (e.symm.trans g)).trans (k.trans j)⟩⟩

theorem quaternionic_maximal_compact : quaternionic_maximal_compact_type := by
  intro n hsize
  let ω := coefficientConjugation (Fin n ⊕ Fin n)
  let h := quaternionic_orthogonal n
  let hs : quaternionicMatrix n * quaternionicMatrix n = 1 ∨
      quaternionicMatrix n * quaternionicMatrix n = -1 := Or.inr (quaternionic_square n)
  let a := orthogonalAction (quaternionicMatrix n) h
  have hc : IsCompact ω := coefficient_compact_of_card (by simpa using hsize)
  let g := compactSubalgebraEquiv ω a (orthogonalAction_commutes h) (orthogonalAction_involutive h hs)
  obtain ⟨k, _⟩ := fixed_complexification (fixedConjugation ω a (orthogonalAction_commutes h))
  obtain ⟨j⟩ := quaternionic_compact n
  obtain ⟨r⟩ := OrthogonalCompactGeometry.quaternionic_real_fixed n a (orthogonalAction_commutes h)
    (fun X => by rw [orthogonalAction_val, complexMatrix_quaternionic])
  exact ⟨cartan_maximal_compact ω hc a (orthogonalAction_commutes h) (orthogonalAction_involutive h hs),
    ⟨(complexifyEquiv g).trans (k.trans j)⟩, ⟨g.trans r⟩⟩

end MaximalCompact

theorem abstract_exhaustion : abstract_exhaustion_type := by
  intro N hN S _ _ ⟨e⟩
  let τ := RealForms.coefficientConjugation S
  let σ := τ.transport e
  have h : Intertwines τ σ e := by
    intro x
    change e (τ.map (e.symm (e x))) = _
    rw [e.symm_apply_apply]
  obtain ⟨f, _⟩ := restrict_complex_isomorphism τ σ e h
  obtain ⟨g, _⟩ := RealForms.coefficient_fixed_equiv S
  rcases exhaustion N hN σ.fixed (fixed_isRealForm σ) with ⟨p, q, hpq, ⟨j⟩⟩ | ⟨n, hn, ⟨j⟩⟩
  · exact Or.inl ⟨p, q, hpq, ⟨g.trans (f.trans j)⟩⟩
  · exact Or.inr ⟨n, hn, ⟨g.trans (f.trans j)⟩⟩

end LieAlgebrasAndRepresentations.RealFormsOrthogonal
