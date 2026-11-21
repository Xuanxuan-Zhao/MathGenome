import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormsSymplectic
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsC
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanDecompositionSignature
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SymplecticCompactKilling
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SymplecticAdjointSurjectivity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SymplecticSignedCentralizer
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SymplecticUnitaryNormalForms
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Module

/-! Matrix real structures for the symplectic row of LA-J07. -/

noncomputable section

namespace LieAlgebrasAndRepresentations.RealFormsSymplectic

open Matrix
attribute [local instance] LieRing.ofAssociativeRing
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
open Specs.LieAlgebrasAndRepresentations.RealFormsSymplectic

def coefficientConjugation := coefficientConjugation_value

theorem coefficientFormula : coefficientFormulaType := by
  intro n X
  rfl

private theorem symplecticEquation {R : Type*} [CommRing R] {n : ℕ}
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    X ∈ LieAlgebra.Symplectic.sp (Fin n) R ↔
      Xᵀ * J (Fin n) R = -(J (Fin n) R * X) := by
  simp only [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
    Matrix.mul_neg]

theorem splitIdentification : splitIdentificationType := by
  intro n
  let ofReal (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) : Mat n :=
    X.map Complex.ofRealHom
  have map_eq (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
      ofReal (Xᵀ * J (Fin n) ℝ) = (ofReal X)ᵀ * J (Fin n) ℂ := by
    simp only [ofReal, Matrix.map_mul, Matrix.transpose_map, Matrix.map_J]
  have map_eq' (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
      ofReal (-(J (Fin n) ℝ * X)) = -(J (Fin n) ℂ * ofReal X) := by
    simp only [ofReal, Matrix.map_neg _ (map_neg Complex.ofRealHom), Matrix.map_mul,
      Matrix.map_J]
  have hi : Function.Injective ofReal := by
    intro X Y h
    ext i j
    exact Complex.ofReal_injective (congrArg (fun M : Mat n => M i j) h)
  have hm (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
      ofReal X ∈ sp n ↔ X ∈ LieAlgebra.Symplectic.sp (Fin n) ℝ := by
    rw [symplecticEquation, symplecticEquation, ← map_eq, ← map_eq']
    exact hi.eq_iff
  let f : LieAlgebra.Symplectic.sp (Fin n) ℝ →ₗ⁅ℝ⁆ (coefficientConjugation_value n).fixed :=
    { toFun := fun X => ⟨⟨ofReal X.val, (hm X.val).mpr X.property⟩, by
        apply Subtype.ext
        ext i j
        exact Complex.conj_ofReal _⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        apply Subtype.ext
        exact Matrix.map_add _ (map_add Complex.ofRealHom) _ _
      map_smul' := by
        intro r X
        apply Subtype.ext
        apply Subtype.ext
        ext i j
        exact Complex.ofReal_mul _ _
      map_lie' := by
        intro X Y
        apply Subtype.ext
        apply Subtype.ext
        change (_ - _ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ).map Complex.ofRealHom
          = _ - _
        rw [Matrix.map_sub _ (map_sub Complex.ofRealHom), Matrix.map_mul, Matrix.map_mul] }
  refine ⟨(LieEquiv.ofBijective f ⟨?_, ?_⟩).symm⟩
  · intro X Y h
    exact Subtype.ext (hi (congrArg (fun z : (coefficientConjugation_value n).fixed =>
      (z.val : Mat n)) h))
  · intro X
    let Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
      fun i j => (X.val.val i j).re
    have hY : ofReal Y = X.val.val := by
      ext i j
      have h := congrArg (fun z : sp n => z.val i j) X.property
      change (starRingEnd ℂ) (X.val.val i j) = X.val.val i j at h
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp h
      change (↑((X.val.val i j).re) : ℂ) = X.val.val i j
      rw [hr, Complex.ofReal_re]
    have hmem := (hm Y).mp (hY.symm ▸ X.val.property)
    exact ⟨⟨Y, hmem⟩, Subtype.ext (Subtype.ext hY)⟩

def matrixAdjoint := matrixAdjoint_value

theorem matrixAdjointFormula : matrixAdjointFormulaType := by
  intro n A X
  change (A : Mat n).lieConj _ X.val = _
  rw [Matrix.lieConj_apply, SymplecticGroup.coe_inv']

open LieAlgebrasAndRepresentations.RealForms

def twistedConjugation := twistedConjugation_value

private theorem twistedFormula (n : ℕ) (A : Sp n)
    (hreal : (A : Mat n).map (starRingEnd ℂ) = (A : Mat n))
    (hsquare : (A : Mat n) * (A : Mat n) = -1)
    (X : sp n) :
    ((twistedConjugation_value n A hreal hsquare).map X : Mat n) =
      (A : Mat n) * X.val.map (starRingEnd ℂ) * (-(A : Mat n)) := by
  change (A : Mat n).lieConj _ (X.val.map (starRingEnd ℂ)) = _
  rw [Matrix.lieConj_apply]
  congr 1
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_neg, hsquare, neg_neg]

def compactConjugation := compactConjugation_value

theorem compactFormula : compactFormulaType := by
  intro n X
  unfold compactConjugation_value
  erw [twistedFormula]
  let Y : sp n := (coefficientConjugation_value n).map X
  change J (Fin n) ℂ * Y.val * (-J (Fin n) ℂ) = -X.valᴴ
  have h := congrArg (· * J (Fin n) ℂ) ((symplecticEquation Y.val).mp Y.property)
  rw [Matrix.mul_assoc Y.valᵀ, Matrix.J_squared, Matrix.mul_neg, Matrix.mul_one,
    Matrix.neg_mul, neg_inj] at h
  rw [Matrix.mul_neg, ← h]
  rfl

def signatureConjugation := signatureConjugation_value

private theorem signatureSquare (n p : ℕ) : signatureMatrix n p * signatureMatrix n p = 1 := by
  have h : signatureDiagonal n p * signatureDiagonal n p = 1 := by
    rw [signatureDiagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    by_cases hi : i.val < p <;> simp [hi]
  simp [signatureMatrix, Matrix.fromBlocks_multiply, h]

private theorem signatureMulJ (n p : ℕ) :
    signatureMatrix n p * J (Fin n) ℂ = quaternionicMatrix n p := by
  simp [signatureMatrix, quaternionicMatrix, Matrix.J, Matrix.fromBlocks_multiply]

private theorem jMulSignature (n p : ℕ) :
    J (Fin n) ℂ * signatureMatrix n p = quaternionicMatrix n p := by
  simp [signatureMatrix, quaternionicMatrix, Matrix.J, Matrix.fromBlocks_multiply]

theorem signatureFormula : signatureFormulaType := by
  intro n p X
  have h := compactFormula n X
  unfold compactConjugation_value at h
  erw [twistedFormula] at h
  change J (Fin n) ℂ * X.val.map (starRingEnd ℂ) * (-J (Fin n) ℂ) = -X.valᴴ at h
  rw [Matrix.mul_neg, neg_inj] at h
  unfold signatureConjugation_value
  erw [twistedFormula]
  change quaternionicMatrix n p * X.val.map (starRingEnd ℂ) * (-quaternionicMatrix n p) =
    -(signatureMatrix n p * X.valᴴ * signatureMatrix n p)
  rw [Matrix.mul_neg, neg_inj]
  calc
    quaternionicMatrix n p * X.val.map (starRingEnd ℂ) * quaternionicMatrix n p =
      (signatureMatrix n p * J (Fin n) ℂ) * X.val.map (starRingEnd ℂ) *
        (J (Fin n) ℂ * signatureMatrix n p) := by
          conv_lhs =>
            arg 1
            arg 1
            rw [← signatureMulJ n p]
          rw [← jMulSignature n p]
    _ = signatureMatrix n p *
        (J (Fin n) ℂ * X.val.map (starRingEnd ℂ) * J (Fin n) ℂ) * signatureMatrix n p := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [h]

theorem signatureFixedEquation : signatureFixedEquationType := by
  intro n p X
  change (signatureConjugation_value n p).map X = X ↔ _
  rw [← Subtype.coe_inj, signatureFormula]
  constructor
  · intro h
    have he := congrArg (signatureMatrix n p * ·) h
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, signatureSquare,
      Matrix.one_mul] at he
    exact neg_eq_iff_eq_neg.mp he
  · intro h
    rw [Matrix.mul_assoc, h, Matrix.mul_neg, neg_neg, ← Matrix.mul_assoc, signatureSquare,
      Matrix.one_mul]

open private LieAlgebrasAndRepresentations.ClassicalRootsC.centralizer_isDiag
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsC

theorem matrixCentralizer : matrixCentralizerType := by
  intro n hn M
  constructor
  · intro h
    have hd : M.IsDiag := LieAlgebrasAndRepresentations.ClassicalRootsC.centralizer_isDiag M fun t => by
      have h' := h ⟨_, ClassicalRootsC.diagonal_mem n t⟩
      exact sub_eq_zero.mpr h'.symm
    have entry (X : sp n) (i j : Fin n ⊕ Fin n) (hij : X.val i j ≠ 0) :
        M i i = M j j := by
      have he := congrArg (fun Y : Mat n => Y i j) (h X)
      conv at he =>
        lhs
        rw [← hd.diagonal_diag, Matrix.diagonal_mul]
      conv at he =>
        rhs
        rw [← hd.diagonal_diag, Matrix.mul_diagonal]
      change M i i * X.val i j = X.val i j * M j j at he
      rw [mul_comm (X.val i j)] at he
      exact mul_right_cancel₀ hij he
    have hpair (i : Fin n) : M (.inl i) (.inl i) = M (.inr i) (.inr i) := by
      have hmem : bLong i ∈ Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.rootSpace
          ((2 : ℂ) • eps i) := by
        rw [ClassicalRootsC.b_long_space n i]
        exact Submodule.subset_span (Set.mem_singleton _)
      exact entry ⟨bLong i, hmem.1⟩ (.inl i) (.inr i) (by simp [bLong])
    have hleft (i j : Fin n) : M (.inl i) (.inl i) = M (.inl j) (.inl j) := by
      by_cases hij : i = j
      · subst j
        rfl
      · have hmem : aRoot i j ∈ Specs.LieAlgebrasAndRepresentations.ClassicalRootsC.rootSpace
            (eps i - eps j) := by
          rw [ClassicalRootsC.a_space n i j hij]
          exact Submodule.subset_span (Set.mem_singleton _)
        exact entry ⟨aRoot i j, hmem.1⟩ (.inl i) (.inl j) (by simp [aRoot])
    let z : Fin n := ⟨0, hn⟩
    refine ⟨M (.inl z) (.inl z), ?_⟩
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      cases i with
      | inl i => exact hleft i z
      | inr i => exact (hpair i).symm.trans (hleft i z)
    · simp [hd hij, Matrix.one_apply_ne hij]
  · rintro ⟨c, rfl⟩ X
    simp

theorem matrixAdjointKernel : matrixAdjointKernelType := by
  intro n hn A
  have hAB : (A : Mat n) * ((A⁻¹ : Sp n) : Mat n) = 1 :=
    congrArg Subtype.val (mul_inv_cancel A)
  have hBA : ((A⁻¹ : Sp n) : Mat n) * (A : Mat n) = 1 :=
    congrArg Subtype.val (inv_mul_cancel A)
  constructor
  · intro h
    have hcomm (X : sp n) : (A : Mat n) * X.val = X.val * (A : Mat n) := by
      have he := congrArg Subtype.val (h X)
      rw [matrixAdjointFormula] at he
      have he' := congrArg (· * (A : Mat n)) he
      simpa only [Matrix.mul_assoc ((A : Mat n) * X.val), hBA, Matrix.mul_one] using he'
    obtain ⟨c, hc⟩ := (matrixCentralizer n hn A).mp hcomm
    have hs := SymplecticGroup.mem_iff.mp A.property
    change (A : Mat n) * J (Fin n) ℂ * (A : Mat n)ᵀ = J (Fin n) ℂ at hs
    rw [hc] at hs
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.one_mul, Matrix.mul_one, smul_smul] at hs
    let i : Fin n := ⟨0, hn⟩
    have hc' : c * c = 1 := by
      have he := congrArg (fun Y : Mat n => Y (.inr i) (.inl i)) hs
      simpa [Matrix.J] using he
    rcases (mul_self_eq_one_iff.mp hc') with he | he
    · exact Or.inl (by simp [hc, he])
    · exact Or.inr (by simp [hc, he])
  · intro h X
    apply Subtype.ext
    rw [matrixAdjointFormula]
    have he : (A : Mat n) * X.val = X.val * (A : Mat n) := by
      rcases h with h | h <;> simp [h]
    rw [he, Matrix.mul_assoc, hAB, Matrix.mul_one]

private theorem adjointJ (n : ℕ) (X : sp n) :
    (splitInvolution_value n X : Mat n) = J (Fin n) ℂ * X.val * (-J (Fin n) ℂ) := by
  rw [splitInvolution_value, matrixAdjointFormula, SymplecticGroup.coe_inv', SymplecticGroup.coe_J,
    Matrix.J_inv]

def splitInvolution := splitInvolution_value

theorem splitInvolutionProperties : splitInvolutionPropertiesType := by
  intro n
  have twice : Function.Involutive (splitInvolution_value n) := by
    intro X
    apply Subtype.ext
    rw [adjointJ, adjointJ]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc]
    rw [J_squared, Matrix.mul_assoc ((-1 : Mat n) * X.val), J_squared]
    simp
  have step (X : sp n) : splitInvolution_value n ((coefficientConjugation_value n).map X) =
      (compactConjugation_value n).map X := rfl
  have conjComm (X : sp n) :
      (coefficientConjugation_value n).map (splitInvolution_value n X) =
        splitInvolution_value n ((coefficientConjugation_value n).map X) := by
    apply Subtype.ext
    rw [coefficientFormula, adjointJ, adjointJ, coefficientFormula,
      Matrix.map_mul, Matrix.map_mul, Matrix.map_J, Matrix.map_neg _ (map_neg (starRingEnd ℂ)),
      Matrix.map_J]
  refine ⟨twice, ?_, ?_⟩
  · intro X
    rw [← step, conjComm, step]
  · intro X
    rw [← step, twice]

open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature (complexFixed)

private theorem splitFixed_iff_commute (n : ℕ) (X : sp n) :
    X ∈ complexFixed (splitInvolution_value n) ↔ J (Fin n) ℂ * X.val = X.val * J (Fin n) ℂ := by
  change splitInvolution_value n X = X ↔ _
  rw [← Subtype.coe_inj, adjointJ]
  have hJ : -(J (Fin n) ℂ) * J (Fin n) ℂ = 1 := by
    rw [Matrix.neg_mul, J_squared, neg_neg]
  constructor
  · intro h
    have h' := congrArg (· * J (Fin n) ℂ) h
    simpa only [Matrix.mul_assoc (J (Fin n) ℂ * X.val), hJ, Matrix.mul_one] using h'
  · intro h
    rw [h, Matrix.mul_assoc, Matrix.mul_neg, J_squared, neg_neg, Matrix.mul_one]

private theorem splitFixed_blocks (n : ℕ) (X : complexFixed (splitInvolution_value n)) :
    X.val.val.toBlocks₂₁ = -X.val.val.toBlocks₁₂ ∧
    X.val.val.toBlocks₂₂ = X.val.val.toBlocks₁₁ := by
  have h := (splitFixed_iff_commute n X.val).mp X.property
  conv at h in X.val.val => rw [← Matrix.fromBlocks_toBlocks X.val.val]
  conv at h in X.val.val * J (Fin n) ℂ =>
    rw [← Matrix.fromBlocks_toBlocks X.val.val]
  simp only [Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj, Matrix.zero_mul,
    Matrix.mul_zero, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg,
    add_zero, zero_add, neg_inj] at h
  exact ⟨neg_eq_iff_eq_neg.mp h.1, h.2.1⟩

private theorem splitFixed_fromBlocks (n : ℕ) (X : complexFixed (splitInvolution_value n)) :
    fromBlocks X.val.val.toBlocks₁₁ X.val.val.toBlocks₁₂
      (-X.val.val.toBlocks₁₂) X.val.val.toBlocks₁₁ = X.val.val := by
  obtain ⟨hC, hD⟩ := splitFixed_blocks n X
  simpa only [hC, hD] using Matrix.fromBlocks_toBlocks X.val.val

theorem splitComplexFixed : splitComplexFixedType := by
  intro n
  let f : complexFixed (splitInvolution_value n) →ₗ⁅ℂ⁆ Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun X => X.val.val.toBlocks₁₁ + Complex.I • X.val.val.toBlocks₁₂
      map_add' := by
        intro X Y
        change (X.val.val.toBlocks₁₁ + Y.val.val.toBlocks₁₁) +
          Complex.I • (X.val.val.toBlocks₁₂ + Y.val.val.toBlocks₁₂) =
          (X.val.val.toBlocks₁₁ + Complex.I • X.val.val.toBlocks₁₂) +
            (Y.val.val.toBlocks₁₁ + Complex.I • Y.val.val.toBlocks₁₂)
        module
      map_smul' := by
        intro c X
        change c • X.val.val.toBlocks₁₁ + Complex.I • (c • X.val.val.toBlocks₁₂) =
          c • (X.val.val.toBlocks₁₁ + Complex.I • X.val.val.toBlocks₁₂)
        module
      map_lie' := by
        intro X Y
        change
          (X.val.val * Y.val.val - Y.val.val * X.val.val).toBlocks₁₁ +
            Complex.I • (X.val.val * Y.val.val - Y.val.val * X.val.val).toBlocks₁₂ =
          (_ + _) * (_ + _) - (_ + _) * (_ + _)
        let A := X.val.val.toBlocks₁₁
        let B := X.val.val.toBlocks₁₂
        let C := Y.val.val.toBlocks₁₁
        let D := Y.val.val.toBlocks₁₂
        change (X.val.val * Y.val.val - Y.val.val * X.val.val).toBlocks₁₁ +
          Complex.I • (X.val.val * Y.val.val - Y.val.val * X.val.val).toBlocks₁₂ =
          (A + Complex.I • B) * (C + Complex.I • D) -
            (C + Complex.I • D) * (A + Complex.I • B)
        have hprod (U V : complexFixed (splitInvolution_value n)) :
            U.val.val * V.val.val =
              fromBlocks (U.val.val.toBlocks₁₁ * V.val.val.toBlocks₁₁ -
                U.val.val.toBlocks₁₂ * V.val.val.toBlocks₁₂)
                (U.val.val.toBlocks₁₁ * V.val.val.toBlocks₁₂ +
                  U.val.val.toBlocks₁₂ * V.val.val.toBlocks₁₁)
                ((-U.val.val.toBlocks₁₂) * V.val.val.toBlocks₁₁ +
                  U.val.val.toBlocks₁₁ * (-V.val.val.toBlocks₁₂))
                ((-U.val.val.toBlocks₁₂) * V.val.val.toBlocks₁₂ +
                  U.val.val.toBlocks₁₁ * V.val.val.toBlocks₁₁) := by
          conv_lhs =>
            arg 1
            rw [← splitFixed_fromBlocks n U]
          conv_lhs =>
            arg 2
            rw [← splitFixed_fromBlocks n V]
          rw [Matrix.fromBlocks_multiply, Matrix.mul_neg, ← sub_eq_add_neg]
        rw [hprod X Y, hprod Y X]
        change (A * C - B * D - (C * A - D * B)) +
          Complex.I • (A * D + B * C - (C * B + D * A)) = _
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul]
        simp only [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
        module }
  have hskew (X : complexFixed (splitInvolution_value n)) :
      X.val.val.toBlocks₁₁ᵀ = -X.val.val.toBlocks₁₁ ∧
      X.val.val.toBlocks₁₂ᵀ = X.val.val.toBlocks₁₂ := by
    obtain ⟨_, hb, ha⟩ := ClassicalRootsC.block_relations X.val.val X.val.property
    rw [(splitFixed_blocks n X).2] at ha
    exact ⟨(neg_eq_iff_eq_neg.mp ha.symm), hb⟩
  refine ⟨LieEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro X Y h
    change X.val.val.toBlocks₁₁ + Complex.I • X.val.val.toBlocks₁₂ =
      Y.val.val.toBlocks₁₁ + Complex.I • Y.val.val.toBlocks₁₂ at h
    have ht := congrArg Matrix.transpose h
    simp only [Matrix.transpose_add, Matrix.transpose_smul, (hskew X).1,
      (hskew X).2, (hskew Y).1, (hskew Y).2] at ht
    have hA : X.val.val.toBlocks₁₁ = Y.val.val.toBlocks₁₁ := by
      have he := congrArg₂ Sub.sub h ht
      have he' : (2 : ℂ) • X.val.val.toBlocks₁₁ = (2 : ℂ) • Y.val.val.toBlocks₁₁ := by
        calc
          _ = X.val.val.toBlocks₁₁ + Complex.I • X.val.val.toBlocks₁₂ -
              (-X.val.val.toBlocks₁₁ + Complex.I • X.val.val.toBlocks₁₂) := by module
          _ = Y.val.val.toBlocks₁₁ + Complex.I • Y.val.val.toBlocks₁₂ -
              (-Y.val.val.toBlocks₁₁ + Complex.I • Y.val.val.toBlocks₁₂) := he
          _ = _ := by module
      exact smul_right_injective (Matrix (Fin n) (Fin n) ℂ) (by norm_num : (2 : ℂ) ≠ 0) he'
    rw [hA, add_right_inj] at h
    have hB := smul_right_injective (Matrix (Fin n) (Fin n) ℂ) Complex.I_ne_zero h
    apply Subtype.ext
    apply Subtype.ext
    calc
      X.val.val = _ := (splitFixed_fromBlocks n X).symm
      _ = _ := by rw [hA, hB]
      _ = Y.val.val := splitFixed_fromBlocks n Y
  · intro M
    let A := (2 : ℂ)⁻¹ • (M - Mᵀ)
    let B := ((-Complex.I) / 2 : ℂ) • (M + Mᵀ)
    have hA : Aᵀ = -A := by
      simp only [A, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose]
      module
    have hB : Bᵀ = B := by
      simp [B, Matrix.transpose_smul, Matrix.transpose_add, add_comm]
    let X : sp n := ⟨fromBlocks A B (-B) A, (ClassicalRootsC.block_form n _ _ _ _).mpr
      ⟨by simp [hB], hB, by simp [hA]⟩⟩
    have hX : X ∈ complexFixed (splitInvolution_value n) := by
      rw [splitFixed_iff_commute]
      change Matrix.J (Fin n) ℂ * fromBlocks A B (-B) A =
        fromBlocks A B (-B) A * Matrix.J (Fin n) ℂ
      simp [Matrix.J, Matrix.fromBlocks_multiply]
    refine ⟨⟨X, hX⟩, ?_⟩
    change A + Complex.I • B = M
    have hI : Complex.I * (-Complex.I / 2) = (2 : ℂ)⁻¹ := by
      rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_div]
    unfold A B
    rw [smul_smul, hI, ← smul_add]
    module

def signatureInvolution := signatureInvolution_value

private theorem adjointSignature (n p : ℕ) (X : sp n) :
    (signatureInvolution_value n p X : Mat n) = signatureMatrix n p * X.val * signatureMatrix n p := by
  rw [signatureInvolution_value, matrixAdjointFormula, SymplecticGroup.coe_inv']
  change signatureMatrix n p * X.val * (signatureMatrix n p)⁻¹ = _
  rw [Matrix.inv_eq_right_inv (signatureSquare n p)]

private theorem signatureHermitian (n p : ℕ) : (signatureMatrix n p)ᴴ = signatureMatrix n p := by
  rw [signatureMatrix, Matrix.fromBlocks_conjTranspose]
  have hD : (signatureDiagonal n p)ᴴ = signatureDiagonal n p := by
    rw [signatureDiagonal, diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : i.val < p <;> simp [h]
  simp [hD]

theorem signatureInvolutionProperties : signatureInvolutionPropertiesType := by
  intro n p
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (signatureMatrix n p)ᴴ * signatureMatrix n p = 1
    rw [signatureHermitian, signatureSquare]
  · intro X
    apply Subtype.ext
    rw [adjointSignature, adjointSignature]
    simp only [← Matrix.mul_assoc]
    rw [signatureSquare, Matrix.one_mul, Matrix.mul_assoc, signatureSquare, Matrix.mul_one]
  · intro X
    apply Subtype.ext
    rw [compactFormula, adjointSignature, adjointSignature, compactFormula]
    simp only [Matrix.conjTranspose_mul, signatureHermitian, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc]
  · intro X
    apply Subtype.ext
    rw [adjointSignature, compactFormula, signatureFormula, Matrix.mul_neg, Matrix.neg_mul]

theorem signatureQuaternionicEquation : signatureQuaternionicEquationType := by
  intro n p X
  change (signatureConjugation_value n p).map X = X ↔ _
  rw [← Subtype.coe_inj]
  unfold signatureConjugation_value
  erw [twistedFormula]
  change quaternionicMatrix n p * X.val.map (starRingEnd ℂ) * (-(quaternionicMatrix n p)) =
    X.val ↔ _
  have hQ : quaternionicMatrix n p * quaternionicMatrix n p = -1 := by
    calc
      _ = (signatureMatrix n p * J (Fin n) ℂ) * (J (Fin n) ℂ * signatureMatrix n p) :=
        congrArg₂ (· * ·) (signatureMulJ n p).symm (jMulSignature n p).symm
      _ = signatureMatrix n p * (J (Fin n) ℂ * J (Fin n) ℂ) * signatureMatrix n p := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [J_squared]; simp [signatureSquare]
  constructor
  · intro h
    have he := congrArg (· * quaternionicMatrix n p) h
    rw [Matrix.mul_assoc (_ * _), Matrix.neg_mul, hQ, neg_neg, Matrix.mul_one] at he
    exact he.symm
  · intro h
    rw [← h, Matrix.mul_assoc, Matrix.mul_neg, hQ, neg_neg, Matrix.mul_one]

theorem representativeRealForms : representativeRealFormsType := by
  intro n
  exact ⟨fixed_isRealForm _, fun p => fixed_isRealForm _⟩

theorem compactEndpoint : compactEndpointType := by
  intro n
  have hpos : signatureMatrix n n = 1 := by
    simp [signatureMatrix, signatureDiagonal]
  have hneg : signatureMatrix n 0 = -1 := by
    have h : signatureDiagonal n 0 = -1 := by
      simp [signatureDiagonal, ← diagonal_neg]
    rw [signatureMatrix, h]
    calc
      _ = -(fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 1) := by
        rw [Matrix.fromBlocks_neg]
        simp
      _ = _ := by rw [Matrix.fromBlocks_one]
  constructor
  · apply Conjugation.ext_map
    ext X : 1
    apply Subtype.ext
    rw [signatureFormula, compactFormula, hpos, Matrix.one_mul, Matrix.mul_one]
  · apply Conjugation.ext_map
    ext X : 1
    apply Subtype.ext
    rw [signatureFormula, compactFormula, hneg]
    simp

theorem adjointInvolution : adjointInvolutionType := by
  intro n hn A
  change Function.Involutive (matrixAdjoint_value n A) ↔
    ((A * A : Sp n) : Mat n) = 1 ∨ ((A * A : Sp n) : Mat n) = -1
  rw [← matrixAdjointKernel n hn (A * A)]
  have hm (X : sp n) :
      matrixAdjoint_value n (A * A) X =
        matrixAdjoint_value n A (matrixAdjoint_value n A X) := by
    apply Subtype.ext
    rw [matrixAdjointFormula, matrixAdjointFormula, matrixAdjointFormula,
      _root_.mul_inv_rev, Submonoid.coe_mul, Submonoid.coe_mul]
    simp only [Matrix.mul_assoc]
  simp only [Function.Involutive, hm]

theorem compactAdjoint : compactAdjointType := by
  intro n hn A
  let B : Sp n := ⟨(A : Mat n)ᴴ, by
    change ((A : Mat n).map (starRingEnd ℂ))ᵀ ∈ symplecticGroup (Fin n) ℂ
    exact SymplecticGroup.transpose_mem (SymplecticGroup.map_mem A.property (starRingEnd ℂ))⟩
  have hBA : ((A⁻¹ : Sp n) : Mat n) * (A : Mat n) = 1 :=
    congrArg Subtype.val (inv_mul_cancel A)
  have hAB : (A : Mat n) * ((A⁻¹ : Sp n) : Mat n) = 1 :=
    congrArg Subtype.val (mul_inv_cancel A)
  have inverse_eq (h : (A : Mat n)ᴴ * (A : Mat n) = 1) :
      ((A⁻¹ : Sp n) : Mat n) = (A : Mat n)ᴴ := by
    have he := congrArg (· * ((A⁻¹ : Sp n) : Mat n)) h
    simpa only [Matrix.mul_assoc, hAB, Matrix.mul_one, Matrix.one_mul] using he.symm
  constructor
  · intro h
    have he (X : sp n) :
        ((A⁻¹ : Sp n) : Mat n)ᴴ * X.valᴴ * (A : Mat n)ᴴ =
          (A : Mat n) * X.valᴴ * ((A⁻¹ : Sp n) : Mat n) := by
      have hh := congrArg Subtype.val (h X)
      rw [compactFormula, matrixAdjointFormula, matrixAdjointFormula, compactFormula,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_neg, Matrix.neg_mul,
        neg_inj] at hh
      simpa only [Matrix.mul_assoc] using hh
    have hcomm (X : sp n) : ((B * A : Sp n) : Mat n) * X.val =
        X.val * ((B * A : Sp n) : Mat n) := by
      have hx := he ((compactConjugation_value n).map X)
      rw [compactFormula, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at hx
      have hh := congrArg (fun M : Mat n => (A : Mat n)ᴴ * (M * (A : Mat n))) hx
      have hI : (A : Mat n)ᴴ * ((A⁻¹ : Sp n) : Mat n)ᴴ = 1 := by
        simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one]
          using congrArg Matrix.conjTranspose hBA
      change ((A : Mat n)ᴴ * (A : Mat n)) * X.val = X.val * ((A : Mat n)ᴴ * (A : Mat n))
      calc
        _ = (A : Mat n)ᴴ * (((A : Mat n) * X.val * ((A⁻¹ : Sp n) : Mat n)) * (A : Mat n)) := by
          rw [Matrix.mul_assoc ((A : Mat n) * X.val), hBA, Matrix.mul_one, Matrix.mul_assoc]
        _ = (A : Mat n)ᴴ * ((((A⁻¹ : Sp n) : Mat n)ᴴ * X.val * (A : Mat n)ᴴ) * (A : Mat n)) :=
          hh.symm
        _ = _ := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hI, Matrix.one_mul,
            Matrix.mul_assoc]
    have htriv (X : sp n) : matrixAdjoint_value n (B * A) X = X := by
      apply Subtype.ext
      rw [matrixAdjointFormula, hcomm, Matrix.mul_assoc]
      have hinv : (((B * A : Sp n) : Mat n) * (((B * A)⁻¹ : Sp n) : Mat n)) = 1 :=
        congrArg Subtype.val (mul_inv_cancel (B * A))
      rw [hinv, Matrix.mul_one]
    rcases (matrixAdjointKernel n hn (B * A)).mp htriv with h | h
    · exact h
    · exfalso
      let i : Fin n ⊕ Fin n := .inl ⟨0, hn⟩
      have himpossible : (((A : Mat n)ᴴ * (A : Mat n)) i i).re = -1 := by
        have he := congrArg (fun M : Mat n => (M i i).re) h
        simpa only [Submonoid.coe_mul, B, Matrix.neg_apply, Matrix.one_apply_eq, Complex.neg_re,
          Complex.one_re] using he
      have hpos : 0 ≤ (((A : Mat n)ᴴ * (A : Mat n)) i i).re := by
        rw [Matrix.mul_apply, Complex.re_sum]
        apply Finset.sum_nonneg
        intro j hj
        rw [Matrix.conjTranspose_apply]
        change 0 ≤ (((starRingEnd ℂ) ((A : Mat n) j i)) * (A : Mat n) j i).re
        rw [mul_comm, Complex.mul_conj]
        exact Complex.normSq_nonneg _
      linarith
  · intro h X
    have hI := inverse_eq h
    apply Subtype.ext
    rw [compactFormula, matrixAdjointFormula, matrixAdjointFormula, compactFormula,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hI, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]


open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (involutionConjugation)

theorem compactKilling : compactKillingType :=
  fun n hn => SymplecticCompactKilling.compact_killing n hn _ (compactFormula n)

private theorem adjoint_mul {n : ℕ} (A B : Sp n) (X : sp n) :
    matrixAdjoint_value n (A * B) X =
      matrixAdjoint_value n A (matrixAdjoint_value n B X) := by
  apply Subtype.ext
  rw [matrixAdjointFormula, matrixAdjointFormula, matrixAdjointFormula,
    _root_.mul_inv_rev, Submonoid.coe_mul, Submonoid.coe_mul]
  simp only [Matrix.mul_assoc]

private theorem adjoint_one {n : ℕ} (X : sp n) :
    matrixAdjoint_value n 1 X = X := by
  apply Subtype.ext
  rw [matrixAdjointFormula]
  simp

private theorem adjoint_surjective {n : ℕ} (hn : 0 < n) (a : sp n ≃ₗ⁅ℂ⁆ sp n) :
    ∃ A : Sp n, a = matrixAdjoint_value n A := by
  obtain ⟨A, hA⟩ := SymplecticAdjointSurjectivity.adjointSurjectivity n hn
    (SymplecticCompactKilling.semisimple n hn) a
  refine ⟨A, ?_⟩
  ext X : 1
  exact Subtype.ext ((hA X).trans (matrixAdjointFormula n A X).symm)

theorem signatureComplexFixed : signatureComplexFixedType := by
  intro n p hp
  have h : complexFixed (signatureInvolution_value n p) =
      Specs.LieAlgebrasAndRepresentations.SymplecticSignedCentralizer.signedCentralizer n p := by
    ext X
    change signatureInvolution_value n p X = X ↔
      signatureMatrix n p * X.val = X.val * signatureMatrix n p
    rw [← Subtype.coe_inj, adjointSignature]
    constructor
    · intro h
      have h' := congrArg (· * signatureMatrix n p) h
      rwa [Matrix.mul_assoc (_ * _), signatureSquare, Matrix.mul_one] at h'
    · intro h
      rw [h, Matrix.mul_assoc, signatureSquare, Matrix.mul_one]
  rw [h]
  exact SymplecticSignedCentralizer.signedCentralizerEquiv n p hp

theorem compactInvolutionExhaustion : compactInvolutionExhaustionType := by
  intro n hn a ha ha2
  obtain ⟨A, rfl⟩ := adjoint_surjective hn a
  have hA := (compactAdjoint n hn A).mp ha
  refine ⟨A, rfl, hA, ?_⟩
  rcases (adjointInvolution n hn A).mp ha2 with h | h
  · obtain ⟨p, hp, B, hB, hBA⟩ := SymplecticUnitaryNormalForms.squareOne n hn A hA h
    exact ⟨B, hB, Or.inr ⟨h, p, hp, Subtype.ext hBA⟩⟩
  · obtain ⟨B, hB, hBA⟩ := SymplecticUnitaryNormalForms.squareNegOne n hn A hA h
    exact ⟨B, hB, Or.inl ⟨h, hBA⟩⟩

private theorem form_equiv_of_adjoint_intertwining
    {n : ℕ} (hn : 0 < n) {σ τ : Conjugation (sp n)} (B : Sp n)
    (hB : IsCompactMatrix B) (a b : sp n ≃ₗ⁅ℂ⁆ sp n)
    (ha : ∀ X, σ.map X = a ((compactConjugation_value n).map X))
    (hb : ∀ X, τ.map X = b ((compactConjugation_value n).map X))
    (h : ∀ X, b (matrixAdjoint_value n B X) = matrixAdjoint_value n B (a X)) :
    Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ τ.fixed) := by
  apply (forms_isomorphic_iff _ _).mpr
  refine ⟨matrixAdjoint_value n B, fun X => ?_⟩
  rw [hb, (compactAdjoint n hn B).mpr hB X, h, ← ha]

theorem realFormExhaustion : realFormExhaustionType := by
  intro n hn S hS
  obtain ⟨_, a, ha, ha2, _, _, ⟨e⟩⟩ :=
    PolarRealStructures.real_form_reduction (compactConjugation_value n) (compactKilling n hn) S hS
  obtain ⟨A, rfl, _, B, hB, h | h⟩ := compactInvolutionExhaustion n hn a ha ha2
  · have hb : ∀ X, splitInvolution_value n (matrixAdjoint_value n B X) =
        matrixAdjoint_value n B (matrixAdjoint_value n A X) := by
      intro X
      rw [splitInvolution_value, ← adjoint_mul, ← adjoint_mul, ← h.2]
      simp [mul_assoc]
    obtain ⟨f⟩ := form_equiv_of_adjoint_intertwining
      (σ := involutionConjugation (compactConjugation_value n) _ ha ha2)
      (τ := coefficientConjugation_value n) hn B hB _ _
      (fun _ => rfl) (fun X => ((splitInvolutionProperties n).2.2 X).symm) hb
    exact Or.inl ⟨e.trans f⟩
  · obtain ⟨_, p, hp, he⟩ := h
    have hb : ∀ X, signatureInvolution_value n p (matrixAdjoint_value n B X) =
        matrixAdjoint_value n B (matrixAdjoint_value n A X) := by
      intro X
      rw [signatureInvolution_value, ← adjoint_mul, ← adjoint_mul, ← he]
      simp [mul_assoc]
    obtain ⟨f⟩ := form_equiv_of_adjoint_intertwining
      (σ := involutionConjugation (compactConjugation_value n) _ ha ha2)
      (τ := signatureConjugation_value n p) hn B hB _ _
      (fun _ => rfl) (fun X => ((signatureInvolutionProperties n p).2.2.2 X).symm) hb
    exact Or.inr ⟨p, hp, ⟨e.trans f⟩⟩

private theorem adjoint_eq_up_to_sign {n : ℕ} (hn : 0 < n) (A B : Sp n)
    (h : ∀ X, matrixAdjoint_value n A X = matrixAdjoint_value n B X) :
    (A : Mat n) = (B : Mat n) ∨ (A : Mat n) = -(B : Mat n) := by
  have hker : ∀ X, matrixAdjoint_value n (B⁻¹ * A) X = X := fun X => by
    rw [adjoint_mul, h, ← adjoint_mul, inv_mul_cancel, adjoint_one]
  rcases (matrixAdjointKernel n hn _).mp hker with hpos | hneg
  · left
    have h' := congrArg (fun M : Mat n => (B : Mat n) * M) hpos
    rwa [← Submonoid.coe_mul, ← mul_assoc, mul_inv_cancel, one_mul, Matrix.mul_one] at h'
  · right
    have h' := congrArg (fun M : Mat n => (B : Mat n) * M) hneg
    rwa [← Submonoid.coe_mul, ← mul_assoc, mul_inv_cancel, one_mul, Matrix.mul_neg,
      Matrix.mul_one] at h'

open private compact_intertwiner from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

private theorem real_form_matrix_similarity {n : ℕ} (hn : 0 < n) (A C : Sp n)
    (hA : Intertwines (compactConjugation_value n) (compactConjugation_value n)
      (matrixAdjoint_value n A))
    (hC : Intertwines (compactConjugation_value n) (compactConjugation_value n)
      (matrixAdjoint_value n C))
    (hA2 : Function.Involutive (matrixAdjoint_value n A))
    (hC2 : Function.Involutive (matrixAdjoint_value n C))
    (h : Nonempty ((involutionConjugation (compactConjugation_value n) _ hA hA2).fixed
      ≃ₗ⁅ℝ⁆ (involutionConjugation (compactConjugation_value n) _ hC hC2).fixed)) :
    ∃ B : Sp n, ((B * A * B⁻¹ : Sp n) : Mat n) = (C : Mat n) ∨
      ((B * A * B⁻¹ : Sp n) : Mat n) = -(C : Mat n) := by
  obtain ⟨x, hx⟩ := (forms_isomorphic_iff _ _).mp h
  obtain ⟨v, _, hv⟩ := compact_intertwiner _ (compactKilling n hn) _ _ hA hC hA2 hC2 x hx
  obtain ⟨B, rfl⟩ := adjoint_surjective hn v
  refine ⟨B, adjoint_eq_up_to_sign hn _ _ (fun X => ?_)⟩
  rw [adjoint_mul (B * A) B⁻¹, adjoint_mul B A, ← hv, ← adjoint_mul B B⁻¹,
    mul_inv_cancel, adjoint_one]

private theorem involutionConjugation_split (n : ℕ) :
    involutionConjugation (compactConjugation_value n) _ (splitInvolutionProperties n).2.1
      (splitInvolutionProperties n).1 = coefficientConjugation_value n := by
  apply Conjugation.ext_map
  ext X : 1
  exact (splitInvolutionProperties n).2.2 X

private theorem involutionConjugation_signature (n p : ℕ) :
    involutionConjugation (compactConjugation_value n) _ (signatureInvolutionProperties n p).2.2.1
      (signatureInvolutionProperties n p).2.1 = signatureConjugation_value n p := by
  apply Conjugation.ext_map
  ext X : 1
  exact (signatureInvolutionProperties n p).2.2.2 X

theorem compactRealInvolutionExhaustion : compactRealInvolutionExhaustionType := by
  intro n hn θ hθ
  obtain ⟨a, ⟨ha, hcomm, hinv⟩, _⟩ :=
    PolarRealStructures.compact_involution_extension (compactConjugation_value n) θ hθ
  obtain ⟨A, rfl, hu, B, hv, hnormal⟩ := compactInvolutionExhaustion n hn a hcomm hinv
  exact ⟨A, ha, hu, B, hv, hnormal⟩

open scoped BigOperators

private theorem signature_trace {n p : ℕ} (hp : p ≤ n) :
    (signatureMatrix n p).trace = 2 * ((p : ℂ) - ((n - p : ℕ) : ℂ)) := by
  classical
  have hsum : (∑ i : Fin n, if i.val < p then (1 : ℂ) else -1) =
      (p : ℂ) - ((n - p : ℕ) : ℂ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < p then (1 : ℂ) else -1) n]
    conv_lhs =>
      rw [← Nat.add_sub_of_le hp, Finset.sum_range_add]
    have hpos : (∑ x ∈ Finset.range p, if x < p then (1 : ℂ) else -1) = p := by
      trans ∑ _x ∈ Finset.range p, (1 : ℂ)
      · exact Finset.sum_congr rfl (fun i hi => ite_eq_left (Finset.mem_range.mp hi))
      · simp
    rw [hpos]
    simp [Nat.not_lt.mpr (Nat.le_add_right _ _), sub_eq_add_neg]
  simp only [signatureMatrix, Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, signatureDiagonal,
    Matrix.diagonal_apply_eq, hsum, two_mul]

private theorem matrix_similarity_trace {n : ℕ} (A B : Sp n) :
    (((B * A * B⁻¹ : Sp n) : Mat n)).trace = (A : Mat n).trace := by
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrix.trace_mul_cycle,
    ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]

private def reversalMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (Fin.revPerm : Equiv.Perm (Fin n)).permMatrix ℂ

private theorem reversalMatrix_inv_eq (n : ℕ) :
    (Fin.revPerm : Equiv.Perm (Fin n))⁻¹ = Fin.revPerm :=
  (Equiv.Perm.inv_def _).trans Fin.revPerm_symm

private theorem reversalMatrix_square (n : ℕ) :
    reversalMatrix n * reversalMatrix n = 1 := by
  unfold reversalMatrix
  conv_lhs => lhs; rw [← reversalMatrix_inv_eq n]
  rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

private def reversalRepresentative (n : ℕ) : Sp n :=
  ⟨fromBlocks (reversalMatrix n) 0 0 (reversalMatrix n), by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    have ht : (reversalMatrix n)ᵀ = reversalMatrix n := by
      simp [reversalMatrix, reversalMatrix_inv_eq]
    simp [ht, reversalMatrix_square]⟩

private theorem reversalRepresentative_sq (n : ℕ) :
    (reversalRepresentative n : Mat n) * (reversalRepresentative n : Mat n) = 1 := by
  change (fromBlocks _ _ _ _ : Mat n) * _ = _
  simp [reversalRepresentative, Matrix.fromBlocks_multiply, reversalMatrix_square,
    ← Matrix.fromBlocks_one]

private theorem reversalRepresentative_compact (n : ℕ) :
    IsCompactMatrix (reversalRepresentative n) := by
  change (_ : Mat n)ᴴ * _ = _
  have ht : (reversalMatrix n)ᴴ = reversalMatrix n := by
    simp [reversalMatrix, reversalMatrix_inv_eq]
  simpa [reversalRepresentative, Matrix.fromBlocks_conjTranspose, ht]
    using reversalRepresentative_sq n

private theorem reversal_intertwines_signature {n p q : ℕ} (h : p + q = n) :
    (reversalRepresentative n : Mat n) * signatureMatrix n p =
      -(signatureMatrix n q * (reversalRepresentative n : Mat n)) := by
  have hD : reversalMatrix n * signatureDiagonal n p =
      -(signatureDiagonal n q * reversalMatrix n) := by
    ext i j
    rw [Matrix.neg_apply, signatureDiagonal, signatureDiagonal,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    have hij : (reversalMatrix n) i j = if j = i.rev then 1 else 0 := by
      simp [reversalMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm (a := j)]
    rw [hij]
    by_cases heq : j = i.rev
    · subst j
      have hi : i.rev.val < p ↔ ¬ i.val < q := by
        have := i.isLt
        rw [Fin.val_rev]
        omega
      by_cases hq : i.val < q
      · simp only [ite_true, ite_eq_left hq, ite_eq_right (fun he => (hi.mp he) hq), one_mul]
      · simp only [ite_true, ite_eq_right hq, ite_eq_left (hi.mpr hq), mul_one, neg_neg]
    · simp [heq]
  change fromBlocks (reversalMatrix n) 0 0 (reversalMatrix n) * signatureMatrix n p =
    -(signatureMatrix n q * fromBlocks (reversalMatrix n) 0 0 (reversalMatrix n))
  simp [signatureMatrix, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg, hD]

private theorem signature_exchange {n p q : ℕ} (hn : 0 < n) (h : p + q = n) :
    Nonempty ((signatureConjugation_value n p).fixed ≃ₗ⁅ℝ⁆
      (signatureConjugation_value n q).fixed) := by
  let B := reversalRepresentative n
  have hBinv : ((B⁻¹ : Sp n) : Mat n) = (B : Mat n) := by
    rw [SymplecticGroup.coe_inv']
    exact Matrix.inv_eq_right_inv (reversalRepresentative_sq n)
  refine form_equiv_of_adjoint_intertwining hn B (reversalRepresentative_compact n)
    (signatureInvolution_value n p) (signatureInvolution_value n q)
    (fun X => ((signatureInvolutionProperties n p).2.2.2 X).symm)
    (fun X => ((signatureInvolutionProperties n q).2.2.2 X).symm) ?_
  intro X
  apply Subtype.ext
  rw [adjointSignature, matrixAdjointFormula, matrixAdjointFormula, adjointSignature, hBinv]
  have hpq : signatureMatrix n q * (B : Mat n) = -((B : Mat n) * signatureMatrix n p) := by
    rw [reversal_intertwines_signature h, neg_neg]
  have hqp : (B : Mat n) * signatureMatrix n q = -(signatureMatrix n p * (B : Mat n)) :=
    reversal_intertwines_signature (Nat.add_comm q p ▸ h)
  calc
    signatureMatrix n q * ((B : Mat n) * X.val * (B : Mat n)) * signatureMatrix n q =
        (signatureMatrix n q * (B : Mat n)) * X.val * ((B : Mat n) * signatureMatrix n q) := by
          simp only [Matrix.mul_assoc]
    _ = (B : Mat n) * (signatureMatrix n p * X.val * signatureMatrix n p) * (B : Mat n) := by
          simp only [hpq, hqp, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]

theorem realFormUniqueness : realFormUniquenessType := by
  intro n hn
  constructor
  · intro p q hp hq
    constructor
    · intro h
      have hs := (signatureInvolutionProperties n p)
      have ht := (signatureInvolutionProperties n q)
      obtain ⟨B, hB⟩ := real_form_matrix_similarity hn (signatureRepresentative_value n p)
        (signatureRepresentative_value n q) hs.2.2.1 ht.2.2.1 hs.2.1 ht.2.1
        (by
          rw [← involutionConjugation_signature n p, ← involutionConjugation_signature n q] at h
          exact h)
      have htrace := matrix_similarity_trace (signatureRepresentative_value n p) B
      rcases hB with hB | hB
      · left
        rw [hB] at htrace
        change (signatureMatrix n q).trace = (signatureMatrix n p).trace at htrace
        rw [signature_trace hq, signature_trace hp] at htrace
        have hreal := congrArg Complex.re htrace
        simp [Complex.mul_re] at hreal
        have hnat : q + (n - p) = p + (n - q) := by
          have hcast : (q : ℝ) + ((n-p : ℕ) : ℝ) = (p : ℝ) + ((n-q : ℕ) : ℝ) := by
            linarith
          exact_mod_cast hcast
        omega
      · right
        rw [hB, Matrix.trace_neg] at htrace
        change -(signatureMatrix n q).trace = (signatureMatrix n p).trace at htrace
        rw [signature_trace hq, signature_trace hp] at htrace
        have hreal := congrArg Complex.re htrace
        simp [Complex.mul_re] at hreal
        have hnat : p + q = (n - p) + (n - q) := by
          have hcast : (p : ℝ) + (q : ℝ) = ((n-p : ℕ) : ℝ) + ((n-q : ℕ) : ℝ) := by
            linarith
          exact_mod_cast hcast
        omega
    · rintro (rfl | h)
      · exact ⟨LieEquiv.refl ..⟩
      · exact signature_exchange hn h
  · intro p _ h
    have hs := (signatureInvolutionProperties n p)
    have ht := (splitInvolutionProperties n)
    let A := signatureRepresentative_value n p
    obtain ⟨B, hB⟩ := real_form_matrix_similarity hn A (SymplecticGroup.symJ (Fin n) ℂ)
      hs.2.2.1 ht.2.1 hs.2.1 ht.1
      (by
        rw [← involutionConjugation_signature n p, ← involutionConjugation_split n] at h
        exact h)
    have hsq : A * A = 1 := Subtype.ext (signatureSquare n p)
    have hsq' : (B * A * B⁻¹) * (B * A * B⁻¹) = 1 := by
      calc
        _ = B * (A * A) * B⁻¹ := by simp only [mul_assoc, inv_mul_cancel_left]
        _ = 1 := by simp [hsq]
    have hmat : (((B * A * B⁻¹ : Sp n) : Mat n)) * ((B * A * B⁻¹ : Sp n) : Mat n) = 1 :=
      congrArg (fun C : Sp n => (C : Mat n)) hsq'
    have hne : (-1 : Mat n) ≠ 1 := by
      intro he
      let i : Fin n ⊕ Fin n := .inl ⟨0, hn⟩
      have he' := congrArg (fun M : Mat n => M i i) he
      norm_num [Matrix.one_apply] at he'
    apply hne
    rcases hB with hB | hB
    · simpa only [hB, SymplecticGroup.coe_J, Matrix.J_squared] using hmat
    · simpa only [hB, SymplecticGroup.coe_J, neg_mul_neg, Matrix.J_squared] using hmat

open scoped TensorProduct InnerProductSpace

open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (hermitian IsCompact)
open private hermitianCore hermitian_positive from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
open private cartan_parts_complementary from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanDecompositionSignature

def compactRealSubalgebra := @compactRealSubalgebra_value

@[instance_reducible] private def realFormInnerCore {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] (ω σ : Conjugation L) (hc : IsCompact ω) :
    InnerProductSpace.Core ℝ σ.fixed := by
  let c := hermitianCore ω hc
  refine
    { inner := fun x y => (hermitian ω (x : L) (y : L)).re
      conj_inner_symm := fun x y => ?_
      re_inner_nonneg := fun x => c.re_inner_nonneg (x : L)
      add_left := fun x y z => ?_
      smul_left := fun x y r => ?_
      definite := fun x hx => ?_ }
  · have h := c.conj_inner_symm (x : L) (y : L)
    change star (hermitian ω (y : L) (x : L)) = hermitian ω (x : L) (y : L) at h
    simpa using congrArg Complex.re h
  · have h := c.add_left (x : L) (y : L) (z : L)
    change hermitian ω ((x : L) + (y : L)) (z : L) =
      hermitian ω (x : L) (z : L) + hermitian ω (y : L) (z : L) at h
    simpa using congrArg Complex.re h
  · have h := c.smul_left (x : L) (y : L) (r : ℂ)
    change hermitian ω ((r : ℂ) • (x : L)) (y : L) =
      star (r : ℂ) * hermitian ω (x : L) (y : L) at h
    simpa [Complex.mul_re] using congrArg Complex.re h
  · by_contra hn
    exact (ne_of_gt (hermitian_positive ω hc (fun h => hn (Subtype.ext h)))) hx

private theorem compactRealSubalgebra_embedded {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] (ω σ : Conjugation L) (hc : IsCompact ω) :
    IsCompactlyEmbedded (compactRealSubalgebra ω σ) := by
  refine ⟨realFormInnerCore ω σ hc, ?_⟩
  intro x hx y z
  have hωx : ω.map (x : L) = (x : L) := hx
  change (hermitian ω ⁅(x : L), (y : L)⁆ (z : L)).re =
    -(hermitian ω (y : L) ⁅(x : L), (z : L)⁆).re
  unfold hermitian
  rw [ω.map.map_lie, hωx]
  simp only [LieModule.traceForm_apply_lie_apply', Complex.neg_re]

private theorem killing_nonpos_of_compactlyEmbedded
    {A : Type*} [LieRing A] [LieAlgebra ℝ A] [FiniteDimensional ℝ A]
    {T : LieSubalgebra ℝ A} (hT : IsCompactlyEmbedded T) {x : A} (hx : x ∈ T) :
    _root_.killingForm ℝ A x x ≤ 0 := by
  obtain ⟨c, hskew⟩ := hT
  let : NormedAddCommGroup A := c.toNormedAddCommGroup
  let : InnerProductSpace ℝ A := InnerProductSpace.ofCore c.toCore
  let b := stdOrthonormalBasis ℝ A
  let f := LieAlgebra.ad ℝ A x
  have hdiag (y : A) : ⟪y, f (f y)⟫_ℝ = -⟪f y, f y⟫_ℝ := by
    have h := hskew x hx y (f y)
    change ⟪f y, f y⟫_ℝ = -⟪y, f (f y)⟫_ℝ at h
    exact neg_eq_iff_eq_neg.mp h.symm
  rw [killingForm_apply_apply, LinearMap.trace_eq_sum_inner _ b]
  calc
    _ = ∑ i, -⟪f (b i), f (b i)⟫_ℝ := Finset.sum_congr rfl fun i _ => hdiag (b i)
    _ ≤ 0 := Finset.sum_nonpos fun i _ => neg_nonpos.mpr real_inner_self_nonneg

private theorem cartanMaximalCompact {L M : Type*} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] [LieRing M] [LieAlgebra ℂ M]
    (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
    (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a) (hc : IsCompact ω)
    {σ : Conjugation L} (hσ : involutionConjugation ω a hcomm hinv = σ)
    (he : Nonempty (complexFixed a ≃ₗ⁅ℂ⁆ M)) :
    let K := compactRealSubalgebra ω σ
    IsMaximalCompactlyEmbedded K ∧ Nonempty ((ℂ ⊗[ℝ] K) ≃ₗ⁅ℂ⁆ M) := by
  subst σ
  let σ := involutionConjugation ω a hcomm hinv
  let : FiniteDimensional ℝ L := FiniteDimensional.trans ℝ ℂ L
  let : FiniteDimensional ℝ σ.fixed :=
    FiniteDimensional.of_injective σ.fixed.toSubmodule.subtype Subtype.val_injective
  let K := compactRealSubalgebra ω σ
  let P := CartanDecompositionSignature.compactPart ω a hcomm hinv
  let N := CartanDecompositionSignature.noncompactPart ω a hcomm hinv
  let κ := CartanDecompositionSignature.fixedConjugation ω a hcomm
  have hfix (x : σ.fixed) : a (ω.map (x : L)) = (x : L) := x.property
  have hmem (x : σ.fixed) : x ∈ K ↔ x ∈ P := by
    change (ω.map (x : L) = (x : L)) ↔
      (ω.map (x : L) = (x : L) ∧ a (x : L) = (1 : ℂ) • (x : L))
    exact ⟨fun h => ⟨h, by simpa only [h, one_smul] using hfix x⟩, And.left⟩
  have hθ (x : κ.fixed) : a ((x : complexFixed a) : L) = ((x : complexFixed a) : L) :=
    (x : complexFixed a).property
  have hω (x : κ.fixed) : ω.map ((x : complexFixed a) : L) = ((x : complexFixed a) : L) :=
    congrArg (fun y : complexFixed a => (y : L)) x.property
  let e : K ≃ₗ⁅ℝ⁆ κ.fixed :=
    { toFun := fun x => ⟨⟨((x : σ.fixed) : L), by
        change a ((x : σ.fixed) : L) = ((x : σ.fixed) : L)
        have hx : ω.map ((x : σ.fixed) : L) = ((x : σ.fixed) : L) := x.property
        simpa only [hx] using hfix (x : σ.fixed)⟩, Subtype.ext x.property⟩
      invFun := fun x => ⟨⟨((x : complexFixed a) : L), by
        change a (ω.map ((x : complexFixed a) : L)) = _
        rw [hω, hθ]⟩, hω x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_lie' := fun {_ _} => rfl }
  obtain ⟨eC, _⟩ := fixed_complexification κ
  obtain ⟨f⟩ := he
  refine ⟨⟨compactRealSubalgebra_embedded ω σ hc, ?_⟩,
    ⟨((complexifyEquiv e).trans eC).trans f⟩⟩
  intro T hKT hT x hx
  have huniv : P ⊔ N = ⊤ :=
    (cartan_parts_complementary ω a hcomm hinv).sup_eq_top
  have hx' : x ∈ P ⊔ N := huniv.symm ▸ Submodule.mem_top
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hx'
  have hpT : p ∈ T := hKT ((hmem p).mpr hp)
  have hqT : q ∈ T := by
    rw [show q = x - p by rw [← hpq, add_sub_cancel_left]]
    exact T.sub_mem hx hpT
  have hqnonpos : _root_.killingForm ℝ σ.fixed q q ≤ 0 :=
    killing_nonpos_of_compactlyEmbedded hT hqT
  have hqzero : q = 0 := by
    by_contra hqn
    exact (not_lt_of_ge hqnonpos)
      ((CartanDecompositionSignature.cartan_killing ω a hcomm hinv hc).2.1 ⟨q, hq⟩ hqn)
  apply (hmem x).mpr
  simpa [← hpq, hqzero] using hp

theorem splitMaximalCompact : splitMaximalCompactType := by
  intro n hn
  obtain ⟨hinv, hcomm, he⟩ := splitInvolutionProperties n
  have hσ : involutionConjugation (compactConjugation_value n)
      (splitInvolution_value n) hcomm hinv = coefficientConjugation_value n := by
    apply Conjugation.ext_map
    exact LieHom.ext he
  exact cartanMaximalCompact (compactConjugation_value n) (splitInvolution_value n)
    hcomm hinv (compactKilling n hn) hσ (splitComplexFixed n)

theorem signatureMaximalCompact : signatureMaximalCompactType := by
  intro n p hn hp
  obtain ⟨_, hinv, hcomm, he⟩ := signatureInvolutionProperties n p
  have hσ : involutionConjugation (compactConjugation_value n)
      (signatureInvolution_value n p) hcomm hinv = signatureConjugation_value n p := by
    apply Conjugation.ext_map
    exact LieHom.ext he
  exact cartanMaximalCompact (compactConjugation_value n) (signatureInvolution_value n p)
    hcomm hinv (compactKilling n hn) hσ (signatureComplexFixed n p hp)

open scoped Quaternion

def quaternionicSkewLie := quaternionicSkewLie_value

private def quaternionFirst : ℍ[ℝ] →ₗ[ℝ] ℂ where
  toFun q := ⟨q.re, q.imI⟩
  map_add' q r := by simp [Complex.ext_iff]
  map_smul' r q := by simp [Complex.ext_iff]

private def quaternionSecond : ℍ[ℝ] →ₗ[ℝ] ℂ where
  toFun q := ⟨q.imJ, q.imK⟩
  map_add' q r := by simp [Complex.ext_iff]
  map_smul' r q := by simp [Complex.ext_iff]

private theorem quaternionFirst_mul (q r : ℍ[ℝ]) :
    quaternionFirst (q * r) = quaternionFirst q * quaternionFirst r -
      quaternionSecond q * star (quaternionSecond r) := by
  apply Complex.ext <;> simp [quaternionFirst, quaternionSecond, Complex.mul_re,
    Complex.mul_im] <;> ring

private theorem quaternionSecond_mul (q r : ℍ[ℝ]) :
    quaternionSecond (q * r) = quaternionFirst q * quaternionSecond r +
      quaternionSecond q * star (quaternionFirst r) := by
  apply Complex.ext <;> simp [quaternionFirst, quaternionSecond, Complex.mul_re,
    Complex.mul_im] <;> ring

/-- The complex representation of a quaternionic matrix with quaternion entries
written as `a + b j`, for complex `a` and `b`. -/
private def quaternionMatrix (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℍ[ℝ]) : Mat n :=
  fromBlocks (Q.map quaternionFirst) (Q.map quaternionSecond)
    (-(Q.map quaternionSecond).map (starRingEnd ℂ)) ((Q.map quaternionFirst).map (starRingEnd ℂ))

private theorem quaternionMatrix_add (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    quaternionMatrix n (X + Y) = quaternionMatrix n X + quaternionMatrix n Y := by
  simp [quaternionMatrix, Matrix.fromBlocks_add, Matrix.map_add _ (map_add quaternionFirst),
    Matrix.map_add _ (map_add quaternionSecond), Matrix.map_add _ (map_add (starRingEnd ℂ)), add_comm]

private theorem quaternionMatrix_smul (n : ℕ) (r : ℝ) (X : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    quaternionMatrix n (r • X) = r • quaternionMatrix n X := by
  ext (i | i) (j | j) <;> simp [quaternionMatrix, Matrix.smul_apply, Matrix.map_apply, map_smul]

private theorem quaternionMatrix_star (n : ℕ) (X : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    quaternionMatrix n Xᴴ = (quaternionMatrix n X)ᴴ := by
  ext (i | i) (j | j) <;> apply Complex.ext <;>
    simp [quaternionMatrix, quaternionFirst, quaternionSecond, Matrix.conjTranspose_apply,
      Matrix.map_apply]

private theorem quaternionMatrix_injective (n : ℕ) : Function.Injective (quaternionMatrix n) := by
  intro Q R h
  have hA := congrArg Matrix.toBlocks₁₁ h
  have hB := congrArg Matrix.toBlocks₁₂ h
  apply Matrix.ext
  intro i j
  apply Quaternion.ext
  · exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i j).re) hA
  · exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i j).im) hA
  · exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i j).re) hB
  · exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i j).im) hB

private theorem quaternionMatrix_mul (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    quaternionMatrix n (X * Y) = quaternionMatrix n X * quaternionMatrix n Y := by
  have hA : (X * Y).map quaternionFirst =
      X.map quaternionFirst * Y.map quaternionFirst -
        X.map quaternionSecond * (Y.map quaternionSecond).map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.mul_apply, map_sum, quaternionFirst_mul, Finset.sum_sub_distrib]
  have hB : (X * Y).map quaternionSecond =
      X.map quaternionFirst * Y.map quaternionSecond +
        X.map quaternionSecond * (Y.map quaternionFirst).map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.mul_apply, map_sum, quaternionSecond_mul, Finset.sum_add_distrib]
  have hstar (Z : Matrix (Fin n) (Fin n) ℂ) :
      (Z.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Z := by
    ext i j
    exact star_star _
  simp only [quaternionMatrix, Matrix.fromBlocks_multiply, hA, hB,
    Matrix.map_add _ (map_add (starRingEnd ℂ)), Matrix.map_neg _ (map_neg (starRingEnd ℂ)), Matrix.map_mul, hstar,
    Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg, neg_add_rev, add_comm]

private theorem quaternionMatrix_sign (n p : ℕ) :
    quaternionMatrix n (diagonal (fun i : Fin n => if i.val < p then 1 else -1)) =
      signatureMatrix n p := by
  ext (i | i) (j | j) <;> by_cases hij : i = j <;> by_cases hj : j.val < p <;>
    simp [quaternionMatrix, quaternionFirst, quaternionSecond, signatureMatrix,
      signatureDiagonal, hij, hj, Complex.ext_iff]

private theorem quaternionMatrix_range (n : ℕ) (Z : Mat n) :
    (∃ X, quaternionMatrix n X = Z) ↔
      Z * J (Fin n) ℂ = J (Fin n) ℂ * Z.map (starRingEnd ℂ) := by
  let A := Z.toBlocks₁₁
  let B := Z.toBlocks₁₂
  let C := Z.toBlocks₂₁
  let D := Z.toBlocks₂₂
  have hz : Z = fromBlocks A B C D := (Matrix.fromBlocks_toBlocks Z).symm
  have hs (Y : Matrix (Fin n) (Fin n) ℂ) :
      (Y.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Y := by
    ext i j
    exact star_star _
  constructor
  · rintro ⟨X, rfl⟩
    simp only [quaternionMatrix, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
      Matrix.map_neg _ (map_neg (starRingEnd ℂ)), hs, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add,
      neg_neg, neg_zero]
  · intro h
    conv at h =>
      lhs
      rw [hz]
    conv at h =>
      rhs
      arg 2
      rw [hz]
    simp only [Matrix.J, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
      Matrix.neg_mul, add_zero, zero_add] at h
    have hc : C = -(B.map (starRingEnd ℂ)) := by
      have z := congrArg Matrix.toBlocks₂₂ h
      simpa using congrArg Neg.neg z
    have hd : D = A.map (starRingEnd ℂ) := by
      simpa using congrArg Matrix.toBlocks₂₁ h
    let X : Matrix (Fin n) (Fin n) ℍ[ℝ] :=
      fun i j => ⟨(A i j).re, (A i j).im, (B i j).re, (B i j).im⟩
    refine ⟨X, ?_⟩
    have ha : X.map quaternionFirst = A := by
      ext i j
      exact Complex.eta _
    have hb : X.map quaternionSecond = B := by
      ext i j
      exact Complex.eta _
    rw [hz, hc, hd, quaternionMatrix, ha, hb]

private theorem quaternionMatrix_neg (n : ℕ) (X : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    quaternionMatrix n (-X) = -(quaternionMatrix n X) := by
  simp only [quaternionMatrix, Matrix.fromBlocks_neg, Matrix.map_neg _ (map_neg quaternionFirst),
    Matrix.map_neg _ (map_neg quaternionSecond), Matrix.map_neg _ (map_neg (starRingEnd ℂ))]

private def signaturePhaseDiagonal (n p : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => if i.val < p then 1 else Complex.I

/-- Multiplying both complex coordinates in each negative pair by `i`
changes standard quaternionic conjugation to the signed one. -/
private def signaturePhase (n p : ℕ) : Mat n :=
  fromBlocks (signaturePhaseDiagonal n p) 0 0 (signaturePhaseDiagonal n p)

private theorem signaturePhase_conj (n p : ℕ) :
    (signaturePhase n p).map (starRingEnd ℂ) = (signaturePhase n p)ᴴ := by
  rw [signaturePhase, Matrix.fromBlocks_map, Matrix.fromBlocks_conjTranspose]
  simp [signaturePhaseDiagonal, Matrix.diagonal_map, Matrix.diagonal_conjTranspose]

private theorem signaturePhase_unitary (n p : ℕ) :
    (signaturePhase n p)ᴴ * signaturePhase n p = 1 ∧
      signaturePhase n p * (signaturePhase n p)ᴴ = 1 := by
  have h (f : ℂ → ℂ → ℂ) (H : ∀ z : ℂ, f z (star z) = z * star z) :
      (Matrix.diagonal fun i : Fin n => f (if i.val < p then 1 else Complex.I)
        (star (if i.val < p then 1 else Complex.I))) = 1 := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    rw [H]
    by_cases hi : i.val < p <;> simp [hi, Complex.I_mul_I]
  have ha : (signaturePhaseDiagonal n p)ᴴ * signaturePhaseDiagonal n p = 1 := by
    rw [signaturePhaseDiagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    exact h (fun z w => w * z) (fun z => mul_comm _ _)
  have hb : signaturePhaseDiagonal n p * (signaturePhaseDiagonal n p)ᴴ = 1 := by
    rw [signaturePhaseDiagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    exact h (· * ·) (fun _ => rfl)
  simp [signaturePhase, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ha, hb]

private theorem signaturePhase_sign (n p : ℕ) :
    signatureMatrix n p * signaturePhase n p = (signaturePhase n p)ᴴ ∧
      signaturePhase n p * signatureMatrix n p = (signaturePhase n p)ᴴ := by
  have h : signatureDiagonal n p * signaturePhaseDiagonal n p =
      (signaturePhaseDiagonal n p)ᴴ := by
    rw [signatureDiagonal, signaturePhaseDiagonal, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i.val < p <;> simp [hi]
  have h' : signaturePhaseDiagonal n p * signatureDiagonal n p =
      (signaturePhaseDiagonal n p)ᴴ := by
    rw [signatureDiagonal, signaturePhaseDiagonal, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    have he := congrArg Matrix.diag h
    rw [signatureDiagonal, signaturePhaseDiagonal, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.diag_diagonal, Matrix.diag_diagonal] at he
    congr 1
    funext i
    exact (mul_comm _ _).trans (congrFun he i)
  simp [signatureMatrix, signaturePhase, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_conjTranspose, h, h']

private theorem signaturePhase_commute (n p : ℕ) :
    signaturePhase n p * J (Fin n) ℂ = J (Fin n) ℂ * signaturePhase n p := by
  simp [signaturePhase, Matrix.J, Matrix.fromBlocks_multiply]

private theorem quaternionic_equations_mem (n p : ℕ) (Z : Mat n)
    (hh : Zᴴ * signatureMatrix n p = -(signatureMatrix n p * Z))
    (hq : Z * quaternionicMatrix n p = quaternionicMatrix n p * Z.map (starRingEnd ℂ))
    (hs : signatureMatrix n p * signatureMatrix n p = 1)
    (hsj : signatureMatrix n p * J (Fin n) ℂ = quaternionicMatrix n p) :
    Z ∈ sp n := by
  have hsreal : (signatureMatrix n p).map (starRingEnd ℂ) = signatureMatrix n p := by
    ext (i | i) (j | j) <;> by_cases hij : i = j <;> by_cases hj : j.val < p <;>
      simp [signatureMatrix, signatureDiagonal, hij, hj]
  have hqreal : (quaternionicMatrix n p).map (starRingEnd ℂ) = quaternionicMatrix n p := by
    rw [← hsj, Matrix.map_mul, hsreal, Matrix.map_J]
  have hconj : (Z.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Z := by
    ext i j
    exact star_star _
  have htr : Zᴴ.map (starRingEnd ℂ) = Zᵀ := by
    ext i j
    exact star_star _
  have hqt := congrArg (fun M : Mat n => M.map (starRingEnd ℂ)) hq
  rw [Matrix.map_mul, Matrix.map_mul, hqreal, hconj] at hqt
  have hht := congrArg (fun M : Mat n => M.map (starRingEnd ℂ)) hh
  rw [Matrix.map_mul, Matrix.map_neg _ (map_neg (starRingEnd ℂ)), Matrix.map_mul, hsreal, htr] at hht
  have hq' : signatureMatrix n p * quaternionicMatrix n p = J (Fin n) ℂ := by
    rw [← hsj, ← mul_assoc, hs, one_mul]
  have ht := congrArg (fun M : Mat n => M * signatureMatrix n p) hht
  rw [mul_assoc, hs, mul_one, neg_mul] at ht
  have hm : Zᵀ * J (Fin n) ℂ = -(J (Fin n) ℂ * Z) := by
    rw [ht, neg_mul, mul_assoc, mul_assoc (signatureMatrix n p), hsj, hqt,
      ← mul_assoc (signatureMatrix n p), hq']
  change Z ∈ LieAlgebra.Symplectic.sp (Fin n) ℂ
  simpa only [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
    Matrix.mul_neg] using hm

private theorem signaturePhase_transport (n p : ℕ) (Y : Mat n)
    (hs : signatureMatrix n p * signatureMatrix n p = 1)
    (hsj : signatureMatrix n p * J (Fin n) ℂ = quaternionicMatrix n p)
    (hjs : J (Fin n) ℂ * signatureMatrix n p = quaternionicMatrix n p) :
    let P := signaturePhase n p
    let Z := P * Y * Pᴴ
    (Zᴴ * signatureMatrix n p = -(signatureMatrix n p * Z) ↔
      Yᴴ * signatureMatrix n p = -(signatureMatrix n p * Y)) ∧
    (Z * quaternionicMatrix n p = quaternionicMatrix n p * Z.map (starRingEnd ℂ) ↔
      Y * J (Fin n) ℂ = J (Fin n) ℂ * Y.map (starRingEnd ℂ)) := by
  dsimp
  let P := signaturePhase n p
  let S := signatureMatrix n p
  let Q := quaternionicMatrix n p
  let J₀ := J (Fin n) ℂ
  let Z := P * Y * Pᴴ
  have hcomm : P * J₀ = J₀ * P := signaturePhase_commute n p
  have hSP : S * P = Pᴴ := (signaturePhase_sign n p).1
  have hPS : P * S = Pᴴ := (signaturePhase_sign n p).2
  have hstarS : Pᴴ * S = P := by rw [← hPS, mul_assoc, hs, mul_one]
  have hSstar : S * Pᴴ = P := by rw [← hSP, ← mul_assoc, hs, one_mul]
  have hstarQ : Pᴴ * Q = J₀ * P := by
    rw [← show S * J₀ = Q from hsj, ← mul_assoc, hstarS, hcomm]
  have hQstar : Q * Pᴴ = P * J₀ := by
    rw [← show J₀ * S = Q from hjs, mul_assoc, hSstar, hcomm]
  have hP : P.map (starRingEnd ℂ) = Pᴴ := signaturePhase_conj n p
  have hP' : Pᴴ.map (starRingEnd ℂ) = P := by
    rw [← hP]
    ext i j
    exact star_star _
  have hZ : Zᴴ = P * Yᴴ * Pᴴ := by
    simp only [Z, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]
  have hleft : Pᴴ * P = 1 := (signaturePhase_unitary n p).1
  have hright : P * Pᴴ = 1 := (signaturePhase_unitary n p).2
  change (Zᴴ * S = -(S * Z) ↔ Yᴴ * S = -(S * Y)) ∧
    (Z * Q = Q * Z.map (starRingEnd ℂ) ↔ Y * J₀ = J₀ * Y.map (starRingEnd ℂ))
  constructor
  · have hinj : Function.Injective (fun M : Mat n => P * M * Pᴴ) := by
      intro a b h
      have he := congrArg (fun M : Mat n => Pᴴ * M * P) h
      simpa only [← mul_assoc Pᴴ P, mul_assoc, hleft, one_mul, mul_one] using
        (show Pᴴ * (P * a * Pᴴ) * P = Pᴴ * (P * b * Pᴴ) * P from he)
    have hl : Zᴴ * S = P * (Yᴴ * S) * Pᴴ := by
      rw [hZ]
      simp only [mul_assoc, hstarS, hSstar]
    have hr : -(S * Z) = P * (-(S * Y)) * Pᴴ := by
      simp only [Z, mul_neg, neg_mul, ← mul_assoc, hSP, hPS]
    rw [hl, hr]
    exact hinj.eq_iff
  · have hinj : Function.Injective (fun M : Mat n => P * M * P) := by
      intro a b h
      have he := congrArg (fun M : Mat n => Pᴴ * M * Pᴴ) h
      change Pᴴ * (P * a * P) * Pᴴ = Pᴴ * (P * b * P) * Pᴴ at he
      simp only [← mul_assoc Pᴴ, hleft, one_mul, mul_assoc, hright, mul_one] at he
      exact he
    have hl : Z * Q = P * (Y * J₀) * P := by
      simp only [Z, mul_assoc, hstarQ]
    have hr : Q * Z.map (starRingEnd ℂ) = P * (J₀ * Y.map (starRingEnd ℂ)) * P := by
      unfold Z
      rw [Matrix.map_mul, Matrix.map_mul, hP, hP']
      simp only [← mul_assoc, hQstar]
    rw [hl, hr]
    exact hinj.eq_iff

private theorem quaternionMatrix_skew (n p : ℕ) (X : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    X ∈ quaternionicSkewLie n p ↔
      (quaternionMatrix n X)ᴴ * signatureMatrix n p =
        -(signatureMatrix n p * quaternionMatrix n X) := by
  let D : Matrix (Fin n) (Fin n) ℍ[ℝ] :=
    Matrix.diagonal fun i => if i.val < p then 1 else -1
  change Xᴴ * D = -(D * X) ↔ _
  rw [← (quaternionMatrix_injective n).eq_iff, quaternionMatrix_mul, quaternionMatrix_neg,
    quaternionMatrix_mul, quaternionMatrix_star, quaternionMatrix_sign]


theorem signatureQuaternionicIdentification : signatureQuaternionicIdentificationType := by
  intro n p _
  let P := signaturePhase n p
  let encode (X : Matrix (Fin n) (Fin n) ℍ[ℝ]) : Mat n := P * quaternionMatrix n X * Pᴴ
  have hleft : Pᴴ * P = 1 := (signaturePhase_unitary n p).1
  have hright : P * Pᴴ = 1 := (signaturePhase_unitary n p).2
  have hrecover (M : Mat n) : P * (Pᴴ * M * P) * Pᴴ = M := by
    simp only [← mul_assoc P, one_mul, mul_assoc, hright, mul_one]
  have hencode_inj : Function.Injective encode := by
    intro X Y h
    apply quaternionMatrix_injective n
    have he := congrArg (fun M : Mat n => Pᴴ * M * P) h
    change Pᴴ * (P * quaternionMatrix n X * Pᴴ) * P =
      Pᴴ * (P * quaternionMatrix n Y * Pᴴ) * P at he
    simpa only [← mul_assoc Pᴴ, hleft, one_mul, mul_assoc, hleft, mul_one] using he
  have transport (Y : Mat n) :=
    signaturePhase_transport n p Y (signatureSquare n p) (signatureMulJ n p) (jMulSignature n p)
  have hmem (X : quaternionicSkewLie n p) :
      encode X.val ∈ sp n := by
    have h := transport (quaternionMatrix n X.val)
    exact quaternionic_equations_mem n p (encode X.val)
      (h.1.mpr ((quaternionMatrix_skew n p X.val).mp X.property))
      (h.2.mpr ((quaternionMatrix_range n _).mp ⟨X.val, rfl⟩))
      (signatureSquare n p) (signatureMulJ n p)
  let f : quaternionicSkewLie n p →ₗ⁅ℝ⁆ (signatureConjugation_value n p).fixed :=
    { toFun := fun X => ⟨⟨encode X.val, hmem X⟩,
        (signatureFixedEquation n p ⟨encode X.val, hmem X⟩).mpr
          ((transport (quaternionMatrix n X.val)).1.mpr
            ((quaternionMatrix_skew n p X.val).mp X.property))⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        apply Subtype.ext
        change encode (X.val + Y.val) = encode X.val + encode Y.val
        simp [encode, quaternionMatrix_add, mul_add, add_mul]
      map_smul' := by
        intro r X
        apply Subtype.ext
        apply Subtype.ext
        change encode (r • X.val) = r • encode X.val
        simp [encode, quaternionMatrix_smul]
      map_lie' := by
        intro X Y
        apply Subtype.ext
        apply Subtype.ext
        change encode (X.val * Y.val - Y.val * X.val) =
          encode X.val * encode Y.val - encode Y.val * encode X.val
        have hmul (Q R : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
            encode (Q * R) = encode Q * encode R := by
          simp only [encode, quaternionMatrix_mul, mul_assoc, ← mul_assoc Pᴴ P, hleft,
            one_mul]
        rw [sub_eq_add_neg, sub_eq_add_neg, show encode (X.val * Y.val + -(Y.val * X.val)) =
          encode (X.val * Y.val) + -encode (Y.val * X.val) by
            simp [encode, quaternionMatrix_add, quaternionMatrix_neg, mul_add, add_mul],
          hmul, hmul] }
  refine ⟨(LieEquiv.ofBijective f ⟨?_, ?_⟩).symm⟩
  · intro X Y h
    exact Subtype.ext (hencode_inj (congrArg (fun T : (signatureConjugation_value n p).fixed =>
      T.val.val) h))
  · intro X
    let Z := X.val.val
    let Y := Pᴴ * Z * P
    have hY : P * Y * Pᴴ = Z := hrecover Z
    have hh := (signatureFixedEquation n p X.val).mp X.property
    have hq := (signatureQuaternionicEquation n p X.val).mp X.property
    have h := transport Y
    have hh' : Yᴴ * signatureMatrix n p = -(signatureMatrix n p * Y) := by
      apply h.1.mp
      change (P * Y * Pᴴ)ᴴ * signatureMatrix n p = -(signatureMatrix n p * (P * Y * Pᴴ))
      rw [hY]
      exact hh
    have hq' : Y * J (Fin n) ℂ = J (Fin n) ℂ * Y.map (starRingEnd ℂ) := by
      apply h.2.mp
      change (P * Y * Pᴴ) * quaternionicMatrix n p =
        quaternionicMatrix n p * (P * Y * Pᴴ).map (starRingEnd ℂ)
      rw [hY]
      exact hq
    obtain ⟨Q, hQ⟩ := (quaternionMatrix_range n Y).mpr hq'
    have hm : Q ∈ quaternionicSkewLie n p := (quaternionMatrix_skew n p Q).mpr (hQ.symm ▸ hh')
    refine ⟨⟨Q, hm⟩, Subtype.ext (Subtype.ext ?_)⟩
    change encode Q = Z
    unfold encode
    rw [hQ, hY]

theorem abstractRealFormClassification : abstractRealFormClassificationType := by
  intro n hn A _ _
  obtain ⟨split⟩ := splitIdentification n
  constructor
  · rintro ⟨c⟩
    obtain ⟨ρ, _, e, _⟩ := coefficient_converse A
    let σ := ρ.transport c
    have hc : Intertwines ρ σ c := fun x => by
      change c (ρ.map (c.symm (c x))) = c (ρ.map x)
      rw [c.symm_apply_apply]
    obtain ⟨f, _⟩ := restrict_complex_isomorphism ρ σ c hc
    rcases realFormExhaustion n hn σ.fixed (fixed_isRealForm σ) with hg | ⟨p, hp, ⟨g⟩⟩
    · obtain ⟨g⟩ := hg
      exact Or.inl ⟨((e.trans f).trans g).trans split⟩
    · obtain ⟨q⟩ := signatureQuaternionicIdentification n p hp
      exact Or.inr ⟨p, hp, ⟨((e.trans f).trans g).trans q⟩⟩
  · have of_fixed (σ : Conjugation (sp n)) (e : A ≃ₗ⁅ℝ⁆ σ.fixed) :
        Nonempty ((ℂ ⊗[ℝ] A) ≃ₗ⁅ℂ⁆ sp n) := by
      obtain ⟨f, _⟩ := fixed_complexification σ
      exact ⟨(complexifyEquiv e).trans f⟩
    rintro (he | ⟨p, hp, ⟨e⟩⟩)
    · obtain ⟨e⟩ := he
      exact of_fixed (coefficientConjugation_value n) (e.trans split.symm)
    · obtain ⟨q⟩ := signatureQuaternionicIdentification n p hp
      exact of_fixed (signatureConjugation_value n p) (e.trans q.symm)

private theorem rankOne_symplectic_iff_trace {R : Type*} [CommRing R]
    (X : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    X ∈ LieAlgebra.Symplectic.sp (Fin 1) R ↔ X.trace = 0 := by
  have htrace : X.trace = X (.inl 0) (.inl 0) + X (.inr 0) (.inr 0) := by
    simp [Matrix.trace, Fintype.sum_sum_type]
  rw [htrace]
  change X ∈ skewAdjointMatricesLieSubalgebra (Matrix.J _ _) ↔ _
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule,
    Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_neg]
  constructor
  · intro h
    have h' := congrArg (fun M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R =>
      M (.inl 0) (.inr 0)) h
    simp [Matrix.J, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type] at h'
    exact eq_neg_iff_add_eq_zero.mp (neg_eq_iff_eq_neg.mp h')
  · intro h
    ext (i | i) (j | j)
    all_goals
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i
      subst j
      simp [Matrix.J, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
        neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero, h, add_comm]

private theorem rankOne_reindex_trace {R : Type*} [AddCommMonoid R]
    (X : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    (X.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Fintype.sum_equiv finSumFinEquiv.symm _ _ (fun _ => rfl)

theorem rankOneSymplectic : rankOneSymplecticType := by
  intro R _
  let e : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R ≃ₗ⁅R⁆ Matrix (Fin 2) (Fin 2) R :=
    Matrix.reindexLieEquiv finSumFinEquiv
  refine ⟨e.ofSubalgebras _ _ ?_⟩
  ext Y
  have he (X : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) : (e X).trace = X.trace := by
    exact rankOne_reindex_trace X
  change (∃ X, X ∈ LieAlgebra.Symplectic.sp (Fin 1) R ∧ e X = Y) ↔ Y.trace = 0
  constructor
  · rintro ⟨X, hX, rfl⟩
    rw [he, ← rankOne_symplectic_iff_trace]
    exact hX
  · intro hY
    refine ⟨e.symm Y, (rankOne_symplectic_iff_trace _).mpr ?_, e.apply_symm_apply _⟩
    rwa [← he, e.apply_symm_apply]

theorem rankOneCompact : rankOneCompactType := by
  let e : Mat 1 ≃ₗ⁅ℝ⁆ Matrix (Fin 2) (Fin 2) ℂ :=
    (Matrix.reindexAlgEquiv ℝ ℂ finSumFinEquiv).toLieEquiv
  let f : (compactConjugation_value 1).fixed →ₗ⁅ℝ⁆ Matrix (Fin 2) (Fin 2) ℂ := {
    toFun X := e X.val.val
    map_add' X Y := map_add e X.val.val Y.val.val
    map_smul' r X := map_smul e r X.val.val
    map_lie' {X Y} := e.map_lie X.val.val Y.val.val }
  refine ⟨f, fun X Y h => Subtype.ext (Subtype.ext (e.injective h)), ?_⟩
  have he (X : Mat 1) : (e X).trace = X.trace := by
    exact rankOne_reindex_trace X
  have hs (X : Mat 1) : (e X)ᴴ = e Xᴴ := rfl
  have hmem (X : sp 1) :
      X ∈ (compactConjugation_value 1).fixed ↔ X.valᴴ = -X.val := by
    change (compactConjugation_value 1).map X = X ↔ X.valᴴ = -X.val
    rw [← Subtype.coe_inj, compactFormula, neg_eq_iff_eq_neg]
  intro M
  constructor
  · rintro ⟨X, rfl⟩
    change (e X.val.val).trace = 0 ∧ (e X.val.val)ᴴ = -(e X.val.val)
    rw [he, hs, ← map_neg]
    exact ⟨(rankOne_symplectic_iff_trace _).mp X.val.property,
      congrArg e ((hmem X.val).mp X.property)⟩
  · rintro ⟨ht, hM⟩
    let X : sp 1 := ⟨e.symm M, (rankOne_symplectic_iff_trace _).mpr (by
      rw [← he, e.apply_symm_apply, ht])⟩
    have hX : X ∈ (compactConjugation_value 1).fixed := (hmem X).mpr (e.injective (by
      change e (e.symm M)ᴴ = e (-(e.symm M))
      rw [← hs, map_neg, e.apply_symm_apply, hM]))
    exact ⟨⟨X, hX⟩, e.apply_symm_apply _⟩

end LieAlgebrasAndRepresentations.RealFormsSymplectic
