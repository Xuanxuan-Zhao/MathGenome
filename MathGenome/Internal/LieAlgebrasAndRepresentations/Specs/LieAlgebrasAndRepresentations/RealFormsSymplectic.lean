import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SymplecticSignedCentralizer
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.InnerProductSpace.Defs

/-! Matrix models for the symplectic row of LA-J07 (source lines 4973–4978
and 5057–5088). The symplectic form uses Mathlib's sign convention for J. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.RealFormsSymplectic

open Matrix
attribute [local instance] LieRing.ofAssociativeRing
open ClassicalRootsC
open LieAlgebrasAndRepresentations.RealForms

abbrev Sp (n : ℕ) := symplecticGroup (Fin n) ℂ

/-- The compact quaternionic unitary group in its complex realization.
The quaternionic structure is J followed by coefficient conjugation. -/
def IsCompactMatrix {n : ℕ} (A : Sp n) : Prop :=
  (A : Mat n)ᴴ * (A : Mat n) = 1

export SymplecticSignedCentralizer (signatureDiagonal signatureMatrix)

/-- Coefficient conjugation on matrices in the original symplectic coordinates. -/
abbrev coefficientConjugationType :=
  ∀ n : ℕ, Conjugation (sp n)

def coefficientConjugation_value : coefficientConjugationType := by
  intro n
  have mem_map (x : sp n) : (x : Mat n).map (starRingEnd ℂ) ∈ sp n := by
    have h : (x : Mat n)ᵀ * Matrix.J (Fin n) ℂ = -(Matrix.J (Fin n) ℂ * (x : Mat n)) := by
      simpa only [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra,
        mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
        Matrix.mul_neg, Matrix.neg_mul] using x.property
    change _ ∈ skewAdjointMatricesLieSubalgebra (Matrix.J (Fin n) ℂ)
    rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule,
      Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
    simpa only [Matrix.map_mul, Matrix.map_neg _ (map_neg (starRingEnd ℂ)), Matrix.transpose_map, Matrix.map_J,
      Matrix.mul_neg, Matrix.neg_mul] using congrArg (fun X : Mat n => X.map (starRingEnd ℂ)) h
  let f : sp n →ₗ⁅ℝ⁆ sp n :=
    { toFun := fun x => ⟨(x : Mat n).map (starRingEnd ℂ), mem_map x⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact Matrix.map_add _ (map_add (starRingEnd ℂ)) _ _
      map_smul' := by
        intro r x
        apply Subtype.ext
        ext i j
        change star ((r : ℂ) * (x : Mat n) i j) = (r : ℂ) * star ((x : Mat n) i j)
        rw [star_mul']
        exact congrArg (· * star ((x : Mat n) i j)) (Complex.conj_ofReal r)
      map_lie' := by
        intro x y
        apply Subtype.ext
        change (_ - _ : Mat n).map (starRingEnd ℂ) = _ - _
        rw [Matrix.map_sub _ (map_sub (starRingEnd ℂ)), Matrix.map_mul, Matrix.map_mul] }
  exact
    { map := f
      antilinear := by
        intro a x
        apply Subtype.ext
        ext i j
        exact star_mul' _ _
      involutive := by
        intro x
        apply Subtype.ext
        ext i j
        exact star_star _ }

def coefficientFormulaType : Prop :=
  ∀ n (x : sp n),
    ((coefficientConjugation_value n).map x : Mat n) = (x : Mat n).map (starRingEnd ℂ)

def splitIdentificationType : Prop :=
  ∀ n : ℕ, Nonempty ((coefficientConjugation_value n).fixed ≃ₗ⁅ℝ⁆
    LieAlgebra.Symplectic.sp (Fin n) ℝ)

abbrev matrixAdjointType :=
  ∀ n : ℕ, Sp n → (sp n ≃ₗ⁅ℂ⁆ sp n)

def matrixAdjoint_value : matrixAdjointType := by
  intro n A
  let P : Mat n := A
  let hP : Invertible P := Matrix.invertibleOfIsUnitDet P (SymplecticGroup.symplectic_det A.property)
  refine LieEquiv.ofSubalgebras (sp n) (sp n) (P.lieConj hP) ?_
  ext X
  have key (Y : Mat n) : Y ∈ sp n ↔ P.lieConj hP Y ∈ sp n := by
    simp only [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.lieConj_apply]
    have hJ : Pᵀ * Matrix.J (Fin n) ℂ * P = Matrix.J (Fin n) ℂ :=
      SymplecticGroup.mem_iff'.mp A.property
    have h := (Matrix.J (Fin n) ℂ).isAdjointPair_equiv Y (-Y) P (isUnit_of_invertible P)
    simpa only [hJ, Matrix.mul_neg, Matrix.neg_mul] using h
  constructor
  · rintro ⟨Y, hY, rfl⟩
    exact (key Y).mp hY
  · intro hX
    refine ⟨(P.lieConj hP).symm X, (key _).mpr ?_, (P.lieConj hP).apply_symm_apply X⟩
    simpa only [LieEquiv.apply_symm_apply] using hX

def matrixAdjointFormulaType : Prop :=
  ∀ n (A : Sp n) (X : sp n),
    (matrixAdjoint_value n A X : Mat n) =
      (A : Mat n) * (X : Mat n) * ((A⁻¹ : Sp n) : Mat n)

/-- The matrix for the antiunitary structure of the signature (p,n-p) form. -/
def quaternionicMatrix (n p : ℕ) : Mat n :=
  fromBlocks 0 (-signatureDiagonal n p) (signatureDiagonal n p) 0

/-- A structure obtained by composing coefficient conjugation with an adjoint
action. The parameters below include both the compact and signed cases. -/
abbrev twistedConjugationType :=
  ∀ (n : ℕ) (A : Sp n),
    (A : Mat n).map (starRingEnd ℂ) = (A : Mat n) →
    ((A : Mat n) * (A : Mat n) = -1) → Conjugation (sp n)

def twistedConjugation_value : twistedConjugationType := by
  intro n A hreal hsquare
  let a := matrixAdjoint_value n A
  let σ := coefficientConjugation_value n
  have formula (X : sp n) : (a X : Mat n) =
      (A : Mat n) * (X : Mat n) * (-(A : Mat n)) := by
    change (A : Mat n).lieConj _ X.val = _
    rw [Matrix.lieConj_apply]
    congr 1
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_neg, hsquare, neg_neg]
  refine
    { map := LieHom.comp
        { (a.toLinearEquiv.restrictScalars ℝ).toLinearMap with map_lie' := a.map_lie _ _ }
        σ.map
      antilinear := ?_
      involutive := ?_ }
  · intro c X
    change a (σ.map (c • X)) = star c • a (σ.map X)
    rw [σ.antilinear, map_smul]
  · intro X
    apply Subtype.ext
    change (a (σ.map (a (σ.map X))) : Mat n) = X.val
    rw [formula]
    change (A : Mat n) * (a (σ.map X) : Mat n).map (starRingEnd ℂ) * (-(A : Mat n)) = _
    rw [formula, Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (map_neg (starRingEnd ℂ)), hreal]
    have hstar : ((σ.map X : Mat n).map (starRingEnd ℂ)) = X.val :=
      congrArg Subtype.val (σ.involutive X)
    rw [hstar]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc]
    calc
      A.val * A.val * X.val * A.val * A.val = (-1 : Mat n) * X.val * (A.val * A.val) := by
        rw [hsquare, Matrix.mul_assoc ((-1 : Mat n) * X.val), hsquare]
      _ = X.val := by simp [hsquare]

def compactConjugation_value (n : ℕ) : Conjugation (sp n) :=
  twistedConjugation_value n (SymplecticGroup.symJ (Fin n) ℂ)
    (Matrix.map_J _ _) (Matrix.J_squared _ _)

def compactFormulaType : Prop :=
  ∀ n (X : sp n), ((compactConjugation_value n).map X : Mat n) = -(X.val)ᴴ

abbrev signatureConjugationType := ∀ (n : ℕ) (_p : ℕ), Conjugation (sp n)

private theorem signatureDiagonal_transpose (n p : ℕ) :
    (signatureDiagonal n p)ᵀ = signatureDiagonal n p := by
  simp [signatureDiagonal]

private theorem signatureDiagonal_squared (n p : ℕ) :
    signatureDiagonal n p * signatureDiagonal n p = 1 := by
  rw [signatureDiagonal, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  by_cases h : i.val < p <;> simp [h]

def signatureRepresentative_value (n p : ℕ) : Sp n :=
  ⟨signatureMatrix n p, by
    rw [signatureMatrix, SymplecticGroup.fromBlocks_mem_iff]
    simp [signatureDiagonal_transpose, signatureDiagonal_squared]⟩

def quaternionicRepresentative_value (n p : ℕ) : Sp n :=
  ⟨quaternionicMatrix n p, by
    rw [quaternionicMatrix, SymplecticGroup.fromBlocks_mem_iff]
    simp [signatureDiagonal_transpose, signatureDiagonal_squared]⟩

def signatureConjugation_value : signatureConjugationType := by
  intro n p
  refine twistedConjugation_value n (quaternionicRepresentative_value n p) ?_ ?_
  · have hD : (signatureDiagonal n p).map (starRingEnd ℂ) = signatureDiagonal n p := by
      rw [signatureDiagonal, Matrix.diagonal_map (map_zero (starRingEnd ℂ))]
      congr 1
      funext i
      by_cases h : i.val < p <;> simp [h]
    change (quaternionicMatrix n p).map (starRingEnd ℂ) = quaternionicMatrix n p
    simp [quaternionicMatrix, Matrix.fromBlocks_map, Matrix.map_neg _ (map_neg (starRingEnd ℂ)),
      Matrix.map_zero _ (map_zero (starRingEnd ℂ)), hD]
  · change quaternionicMatrix n p * quaternionicMatrix n p = -1
    simp [quaternionicMatrix, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg,
      signatureDiagonal_squared, ← Matrix.fromBlocks_one]

def signatureFormulaType : Prop :=
  ∀ n p (X : sp n),
    ((signatureConjugation_value n p).map X : Mat n) =
      -(signatureMatrix n p * (X.val)ᴴ * signatureMatrix n p)

def signatureFixedEquationType : Prop :=
  ∀ n p (X : sp n), X ∈ (signatureConjugation_value n p).fixed ↔
    (X.val)ᴴ * signatureMatrix n p = -(signatureMatrix n p * X.val)

def matrixCentralizerType : Prop :=
  ∀ n : ℕ, 0 < n → ∀ M : Mat n,
    (∀ X : sp n, M * X.val = X.val * M) ↔ ∃ c : ℂ, M = c • (1 : Mat n)

def matrixAdjointKernelType : Prop :=
  ∀ n : ℕ, 0 < n → ∀ A : Sp n,
    (∀ X : sp n, matrixAdjoint_value n A X = X) ↔
      (A : Mat n) = 1 ∨ (A : Mat n) = -1

open CartanDecompositionSignature

def splitInvolution_value (n : ℕ) : sp n ≃ₗ⁅ℂ⁆ sp n :=
  matrixAdjoint_value n (SymplecticGroup.symJ (Fin n) ℂ)

def splitInvolutionType := ∀ n : ℕ, sp n ≃ₗ⁅ℂ⁆ sp n

def splitInvolutionPropertiesType : Prop :=
  ∀ n : ℕ, Function.Involutive (splitInvolution_value n) ∧
    Intertwines (compactConjugation_value n) (compactConjugation_value n)
      (splitInvolution_value n) ∧
    ∀ X : sp n, splitInvolution_value n ((compactConjugation_value n).map X) =
      (coefficientConjugation_value n).map X

def splitComplexFixedType : Prop :=
  ∀ n : ℕ, Nonempty (complexFixed (splitInvolution_value n) ≃ₗ⁅ℂ⁆
    Matrix (Fin n) (Fin n) ℂ)

/-- The diagonal symmetry of the compact group with quaternionic multiplicities p and n-p. -/
def signatureInvolution_value (n p : ℕ) : sp n ≃ₗ⁅ℂ⁆ sp n :=
  matrixAdjoint_value n (signatureRepresentative_value n p)

def signatureInvolutionType := ∀ (n : ℕ) (_p : ℕ), sp n ≃ₗ⁅ℂ⁆ sp n

def signatureInvolutionPropertiesType : Prop :=
  ∀ n p : ℕ, IsCompactMatrix (signatureRepresentative_value n p) ∧
    Function.Involutive (signatureInvolution_value n p) ∧
    Intertwines (compactConjugation_value n) (compactConjugation_value n)
      (signatureInvolution_value n p) ∧
    ∀ X : sp n, signatureInvolution_value n p ((compactConjugation_value n).map X) =
      (signatureConjugation_value n p).map X

/-- Commutation with the anti-linear quaternionic structure J D followed by
conjugating coefficients. Together with skew-adjointness for D this is the
usual complex-matrix realization of quaternionic sp(p,n-p). -/
def signatureQuaternionicEquationType : Prop :=
  ∀ n p (X : sp n), X ∈ (signatureConjugation_value n p).fixed ↔
    X.val * quaternionicMatrix n p = quaternionicMatrix n p * X.val.map (starRingEnd ℂ)

def representativeRealFormsType : Prop :=
  ∀ n : ℕ, IsRealForm (coefficientConjugation_value n).fixed ∧
    ∀ p : ℕ, IsRealForm (signatureConjugation_value n p).fixed

def compactEndpointType : Prop :=
  ∀ n : ℕ, signatureConjugation_value n n = compactConjugation_value n ∧
    signatureConjugation_value n 0 = compactConjugation_value n

def adjointInvolutionType : Prop :=
  ∀ n : ℕ, 0 < n → ∀ A : Sp n,
    Function.Involutive (matrixAdjoint_value n A) ↔
      (A : Mat n) * (A : Mat n) = 1 ∨ (A : Mat n) * (A : Mat n) = -1

def compactAdjointType : Prop :=
  ∀ n : ℕ, 0 < n → ∀ A : Sp n,
    Intertwines (compactConjugation_value n) (compactConjugation_value n)
      (matrixAdjoint_value n A) ↔ IsCompactMatrix A

/-! Classification of the real forms and of the compact involutions. -/

def compactKillingType : Prop :=
  ∀ n : ℕ, 0 < n → PolarRealStructures.IsCompact (compactConjugation_value n)

def signatureComplexFixedType : Prop :=
  ∀ n p : ℕ, p ≤ n →
    Nonempty (complexFixed (signatureInvolution_value n p) ≃ₗ⁅ℂ⁆
      (sp p × sp (n - p)))

/-- Exhaustion on the compact side. The Lie equivalence is conjugation by
a unitary symplectic matrix and intertwines the two involutions. -/
def compactInvolutionExhaustionType : Prop :=
  ∀ n : ℕ, 0 < n → ∀ θ : sp n ≃ₗ⁅ℂ⁆ sp n,
    Intertwines (compactConjugation_value n) (compactConjugation_value n) θ →
    Function.Involutive θ →
    ∃ A : Sp n, θ = matrixAdjoint_value n A ∧ IsCompactMatrix A ∧
      ∃ B : Sp n, IsCompactMatrix B ∧
        (((A : Mat n) * (A : Mat n) = -1 ∧
            B * A * B⁻¹ = SymplecticGroup.symJ (Fin n) ℂ) ∨
          ((A : Mat n) * (A : Mat n) = 1 ∧
            ∃ p : ℕ, p ≤ n ∧ B * A * B⁻¹ = signatureRepresentative_value n p))

/-- Every embedded real form of the complex symplectic algebra is covered. -/
def realFormExhaustionType : Prop :=
  ∀ n : ℕ, 0 < n → ∀ S : LieSubalgebra ℝ (sp n), IsRealForm S →
    Nonempty (S ≃ₗ⁅ℝ⁆ (coefficientConjugation_value n).fixed) ∨
      ∃ p : ℕ, p ≤ n ∧ Nonempty (S ≃ₗ⁅ℝ⁆ (signatureConjugation_value n p).fixed)

/-- The signed parameters are classified up to exchange, and the split
form is distinct even in rank one. -/
def realFormUniquenessType : Prop :=
  ∀ n : ℕ, 0 < n →
    (∀ p q : ℕ, p ≤ n → q ≤ n →
      (Nonempty ((signatureConjugation_value n p).fixed ≃ₗ⁅ℝ⁆
        (signatureConjugation_value n q).fixed) ↔ p = q ∨ p + q = n)) ∧
    (∀ p : ℕ, p ≤ n →
      ¬ Nonempty ((signatureConjugation_value n p).fixed ≃ₗ⁅ℝ⁆
        (coefficientConjugation_value n).fixed))

/-- The matrix normal forms, applied to any involution of the compact real algebra. -/
def compactRealInvolutionExhaustionType : Prop :=
  ∀ n : ℕ, 0 < n →
    ∀ θ : (compactConjugation_value n).fixed ≃ₗ⁅ℝ⁆ (compactConjugation_value n).fixed,
    Function.Involutive θ →
    ∃ A : Sp n,
      (∀ X : (compactConjugation_value n).fixed,
        matrixAdjoint_value n A (X : sp n) = (θ X : sp n)) ∧ IsCompactMatrix A ∧
      ∃ B : Sp n, IsCompactMatrix B ∧
        (((A : Mat n) * (A : Mat n) = -1 ∧
            B * A * B⁻¹ = SymplecticGroup.symJ (Fin n) ℂ) ∨
          ((A : Mat n) * (A : Mat n) = 1 ∧
            ∃ p : ℕ, p ≤ n ∧ B * A * B⁻¹ = signatureRepresentative_value n p))

/-- The Lie algebra form of compact embedding: there is a common positive definite
real inner product for which the ambient adjoint operators are skew-adjoint. -/
def IsCompactlyEmbedded {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    (K : LieSubalgebra ℝ A) : Prop :=
  ∃ c : InnerProductSpace.Core ℝ A,
    ∀ x ∈ K, ∀ y z : A, c.inner ⁅x, y⁆ z = -c.inner y ⁅x, z⁆

/-- Maximality is among compactly embedded Lie subalgebras of the real form. -/
def IsMaximalCompactlyEmbedded {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    (K : LieSubalgebra ℝ A) : Prop :=
  IsCompactlyEmbedded K ∧
    ∀ T : LieSubalgebra ℝ A, K ≤ T → IsCompactlyEmbedded T → T ≤ K

def compactRealSubalgebraType :=
  ∀ {L : Type*} [LieRing L] [LieAlgebra ℂ L] (_ω σ : Conjugation L),
    LieSubalgebra ℝ σ.fixed

/-- The compact real algebra inside the real form defined by σ. -/
def compactRealSubalgebra_value : compactRealSubalgebraType :=
  fun ω σ => ω.fixed.comap σ.fixed.incl

open scoped TensorProduct in
def splitMaximalCompactType : Prop :=
  ∀ n : ℕ, 0 < n →
    let K := compactRealSubalgebra_value (compactConjugation_value n)
      (coefficientConjugation_value n)
    IsMaximalCompactlyEmbedded K ∧
      Nonempty ((ℂ ⊗[ℝ] K) ≃ₗ⁅ℂ⁆ Matrix (Fin n) (Fin n) ℂ)

open scoped TensorProduct in
def signatureMaximalCompactType : Prop :=
  ∀ n p : ℕ, 0 < n → p ≤ n →
    let K := compactRealSubalgebra_value (compactConjugation_value n)
      (signatureConjugation_value n p)
    IsMaximalCompactlyEmbedded K ∧
      Nonempty ((ℂ ⊗[ℝ] K) ≃ₗ⁅ℂ⁆ (sp p × sp (n - p)))

open scoped Quaternion TensorProduct

universe u

def quaternionicSkewLieType :=
  ∀ (n : ℕ) (_p : ℕ), LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℍ[ℝ])

/-- Infinitesimal isometries of the quaternionic Hermitian matrix
with `p` positive and `n - p` negative diagonal entries. -/
def quaternionicSkewLie_value : quaternionicSkewLieType := by
  intro n p
  let D : Matrix (Fin n) (Fin n) ℍ[ℝ] := diagonal fun i => if i.val < p then 1 else -1
  refine
    { carrier := {X | Xᴴ * D = -(D * X)}
      zero_mem' := by simp
      add_mem' := ?_
      smul_mem' := ?_
      lie_mem' := ?_ }
  · intro X Y hX hY
    change Xᴴ * D = -(D * X) at hX
    change Yᴴ * D = -(D * Y) at hY
    change (X + Y)ᴴ * D = -(D * (X + Y))
    rw [Matrix.conjTranspose_add, add_mul, mul_add, hX, hY, neg_add]
  · intro r X hX
    change Xᴴ * D = -(D * X) at hX
    change (r • X)ᴴ * D = -(D * (r • X))
    have hs : (r • X)ᴴ = r • Xᴴ := by
      apply Matrix.ext
      intro i j
      exact Quaternion.star_smul r (X j i)
    rw [hs, Matrix.smul_mul, Matrix.mul_smul, hX, smul_neg]
  · intro X Y hX hY
    change Xᴴ * D = -(D * X) at hX
    change Yᴴ * D = -(D * Y) at hY
    change (X * Y - Y * X)ᴴ * D = -(D * (X * Y - Y * X))
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      sub_mul, mul_sub, mul_assoc, hX, mul_assoc, hY]
    simp only [mul_neg, ← mul_assoc]
    rw [hY, hX]
    simp only [neg_mul, neg_neg, mul_assoc, neg_sub]

def signatureQuaternionicIdentificationType : Prop :=
  ∀ n p : ℕ, p ≤ n →
    Nonempty ((signatureConjugation_value n p).fixed ≃ₗ⁅ℝ⁆ quaternionicSkewLie_value n p)

/-- Classification for an abstract real Lie algebra via its tensor complexification. -/
def abstractRealFormClassificationType : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (A : Type u) [LieRing A] [LieAlgebra ℝ A],
    Nonempty ((ℂ ⊗[ℝ] A) ≃ₗ⁅ℂ⁆ sp n) ↔
      Nonempty (A ≃ₗ⁅ℝ⁆ LieAlgebra.Symplectic.sp (Fin n) ℝ) ∨
        ∃ p : ℕ, p ≤ n ∧ Nonempty (A ≃ₗ⁅ℝ⁆ quaternionicSkewLie_value n p)

/-- The rank-one coincidence between the two standard matrix models. -/
def rankOneSymplecticType : Prop :=
  ∀ (R : Type u) [CommRing R],
    Nonempty (LieAlgebra.Symplectic.sp (Fin 1) R ≃ₗ⁅R⁆
      LieAlgebra.SpecialLinear.sl (Fin 2) R)

/-- The rank-one compact symplectic form is the trace-zero skew-Hermitian 2-by-2 model. -/
def rankOneCompactType : Prop :=
  ∃ f : (compactConjugation_value 1).fixed →ₗ⁅ℝ⁆ Matrix (Fin 2) (Fin 2) ℂ,
    Function.Injective f ∧
      ∀ M : Matrix (Fin 2) (Fin 2) ℂ, M ∈ Set.range f ↔ M.trace = 0 ∧ Mᴴ = -M

end Specs.LieAlgebrasAndRepresentations.RealFormsSymplectic
