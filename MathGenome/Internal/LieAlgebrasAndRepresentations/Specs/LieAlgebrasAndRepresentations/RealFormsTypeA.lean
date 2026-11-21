import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! Type A real forms in LA-J07, in the traceless-matrix realization. -/

namespace Specs.LieAlgebrasAndRepresentations.RealFormsTypeA

open LieAlgebrasAndRepresentations.RealForms
open PolarRealStructures (IsCompact involutionConjugation)
open CartanDecompositionSignature (complexFixed)
open Matrix
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev SL (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  LieAlgebra.SpecialLinear.sl ι ℂ

abbrev Blocks (p q : ℕ) := Fin p ⊕ Fin q

/-- The form of signature `(p,q)` on a sum of coordinate spaces. -/
abbrev signatureMatrix (p q : ℕ) : Matrix (Blocks p q) (Blocks p q) ℂ :=
  LieAlgebra.Orthogonal.indefiniteDiagonal (Fin p) (Fin q) ℂ

/-- Entrywise conjugation, as opposed to conjugate transpose. -/
def bar {ι : Type*} (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  X.map (starRingEnd ℂ)

/-- The standard compact conjugation of the complex special linear algebra. -/
def compactMatrixType : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∃ ω : Conjugation (SL ι), (∀ X, (ω.map X).val = -X.valᴴ) ∧ IsCompact ω

/-- `s(gl_p ⊕ gl_q)` as block diagonal matrices of total trace zero. -/
def isBlockDiagonal {p q : ℕ} (X : Matrix (Blocks p q) (Blocks p q) ℂ) : Prop :=
  (∀ i : Fin p, ∀ j : Fin q, X (Sum.inl i) (Sum.inr j) = 0) ∧
  (∀ i : Fin q, ∀ j : Fin p, X (Sum.inr i) (Sum.inl j) = 0)

/-- Pairs of blocks having total trace zero, with the componentwise bracket. -/
def blockTraceZero (p q : ℕ) :
    LieSubalgebra ℂ (Matrix (Fin p) (Fin p) ℂ × Matrix (Fin q) (Fin q) ℂ) where
  carrier := {X | X.1.trace + X.2.trace = 0}
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    change X.1.trace + X.2.trace = 0 at hX
    change Y.1.trace + Y.2.trace = 0 at hY
    change (X.1 + Y.1).trace + (X.2 + Y.2).trace = 0
    rw [trace_add, trace_add, add_add_add_comm, hX, hY, add_zero]
  smul_mem' c X hX := by
    change X.1.trace + X.2.trace = 0 at hX
    change (c • X.1).trace + (c • X.2).trace = 0
    rw [trace_smul, trace_smul, ← smul_add, hX, smul_zero]
  lie_mem' {X Y} _ _ := by
    change (X.1 * Y.1 - Y.1 * X.1).trace + (X.2 * Y.2 - Y.2 * X.2).trace = 0
    simp only [trace_sub, trace_mul_comm X.1 Y.1, trace_mul_comm X.2 Y.2,
      sub_self, add_zero]

def unitaryCompactBlockType : Prop :=
  ∀ (p q : ℕ) (a : SL (Blocks p q) ≃ₗ⁅ℂ⁆ SL (Blocks p q)),
    (∀ X : SL (Blocks p q), X ∈ complexFixed a ↔ isBlockDiagonal X.val) →
    ∃ e : complexFixed a ≃ₗ⁅ℂ⁆ blockTraceZero p q,
      ∀ X, (e X).val = (X.val.val.toBlocks₁₁, X.val.val.toBlocks₂₂)

/-- The Lie algebra of the positive Cartan summand, in the corresponding real form. -/
def modelCompactPart {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ω : Conjugation (SL ι)) (a : SL ι ≃ₗ⁅ℂ⁆ SL ι)
    (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a) :
    LieSubalgebra ℝ (involutionConjugation ω a hcomm hinv).fixed where
  carrier := {X | ω.map X.val = X.val}
  zero_mem' := map_zero ω.map
  add_mem' {_ _} hX hY := by
    change ω.map (_ + _) = _
    rw [map_add, hX, hY]
    rfl
  smul_mem' r _ hX := by
    change ω.map (r • _) = _
    rw [map_smul, hX]
    rfl
  lie_mem' {_ _} hX hY := by
    change ω.map ⁅_, _⁆ = _
    rw [LieHom.map_lie, hX, hY]
    rfl

/-- The adjoint action on the ambient real Lie algebra preserves a positive
definite inner product. This expresses compactness of the embedding. -/
def IsCompactlyEmbedded {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    (K : LieSubalgebra ℝ A) : Prop :=
  ∃ B : LinearMap.BilinForm ℝ A, B.IsSymm ∧ (∀ v ≠ 0, 0 < B v v) ∧
    ∀ (x : K) (v w : A), B ⁅x.val, v⁆ w = -B v ⁅x.val, w⁆

/-- Complexification of the compact part is evaluation onto the fixed complex
algebra. The compact part is maximal compactly embedded, and is even maximal
among subalgebras with nonpositive restriction of the ambient Killing form. -/
def modelCompactPartType : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (ω : Conjugation (SL ι)) (a : SL ι ≃ₗ⁅ℂ⁆ SL ι)
    (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a), IsCompact ω →
    let S := (involutionConjugation ω a hcomm hinv).fixed
    let C := modelCompactPart ω a hcomm hinv
    (∃ e : (ℂ ⊗[ℝ] C) ≃ₗ⁅ℂ⁆ complexFixed a,
      ∀ c x, (e (c ⊗ₜ[ℝ] x)).val = c • x.val.val) ∧
    (∀ x : C, x.val ≠ 0 → killingForm ℝ S x.val x.val < 0) ∧
    (∀ K : LieSubalgebra ℝ S, C ≤ K →
      (∀ x : K, killingForm ℝ S x.val x.val ≤ 0) → K = C) ∧
    IsCompactlyEmbedded C ∧
    (∀ K : LieSubalgebra ℝ S, C ≤ K → IsCompactlyEmbedded K → K = C)

/-- The compact-part identification is expressed through the actual fixed
complex Lie subalgebra of the extended compact involution. -/
def unitaryModelType : Prop :=
  ∀ p q : ℕ,
    ∃ (ω : Conjugation (SL (Blocks p q))) (a : SL (Blocks p q) ≃ₗ⁅ℂ⁆ SL (Blocks p q))
      (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a),
      let D := signatureMatrix p q
      (∀ X, (ω.map X).val = -X.valᴴ) ∧
      (∀ X, (a X).val = D * X.val * D) ∧
      (∀ X, ((involutionConjugation ω a hcomm hinv).map X).val = -(D * X.valᴴ * D)) ∧
      (∀ X : SL (Blocks p q), X ∈ (involutionConjugation ω a hcomm hinv).fixed ↔
        X.valᴴ * D + D * X.val = 0) ∧
      (∀ X : SL (Blocks p q), X ∈ complexFixed a ↔ isBlockDiagonal X.val)

def splitModelType : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∃ (ω : Conjugation (SL ι)) (a : SL ι ≃ₗ⁅ℂ⁆ SL ι)
      (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a),
      (∀ X, (ω.map X).val = -X.valᴴ) ∧
      (∀ X, (a X).val = -X.valᵀ) ∧
      (∀ X, ((involutionConjugation ω a hcomm hinv).map X).val = bar X.val) ∧
      (∃ e : LieAlgebra.SpecialLinear.sl ι ℝ ≃ₗ⁅ℝ⁆
          (involutionConjugation ω a hcomm hinv).fixed,
        ∀ X, ((e X).val).val = X.val.map Complex.ofReal) ∧
      (∃ e : complexFixed a ≃ₗ⁅ℂ⁆ LieAlgebra.Orthogonal.so ι ℂ,
        ∀ X, (e X).val = X.val.val)

/-- The real part of the quaternionic trace is the sum of diagonal real
parts. This condition is stable under commutators over the quaternions. -/
def quaternionicSL (ι : Type*) [Fintype ι] [DecidableEq ι] :
    LieSubalgebra ℝ (Matrix ι ι (Quaternion ℝ)) where
  carrier := {X | ∑ i, (X i i).re = 0}
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    change ∑ i, (X i i).re = 0 at hX
    change ∑ i, (Y i i).re = 0 at hY
    change ∑ i, (X i i + Y i i).re = 0
    simp [Finset.sum_add_distrib, hX, hY]
  smul_mem' r X hX := by
    change ∑ i, (X i i).re = 0 at hX
    change ∑ i, (r • X i i).re = 0
    simp [smul_eq_mul, ← Finset.mul_sum, hX]
  lie_mem' {X Y} _ _ := by
    change ∑ i, ((X * Y) i i - (Y * X) i i).re = 0
    have pull (f : ι → Quaternion ℝ) :
        (∑ j, f j).re = ∑ j, (f j).re := map_sum (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) f _
    simp only [Quaternion.re_sub, Matrix.mul_apply, pull,
      Finset.sum_sub_distrib, sub_eq_zero]
    rw [Finset.sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    simp only [Quaternion.re_mul]
    ring

/-- The standard complex representation of a quaternionic matrix, with
`a + b i + c j + d k` represented by the pair `(a+bi,c+di)`. -/
def quaternionicMatrix {ι : Type*} (X : Matrix ι ι (Quaternion ℝ)) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  let A : Matrix ι ι ℂ := fun i j => ⟨(X i j).re, (X i j).imI⟩
  let B : Matrix ι ι ℂ := fun i j => ⟨(X i j).imJ, (X i j).imK⟩
  Matrix.fromBlocks A B (-bar B) (bar A)

def quaternionicModelType : Prop :=
  ∀ m : ℕ,
    ∃ (ω : Conjugation (SL (Blocks m m))) (a : SL (Blocks m m) ≃ₗ⁅ℂ⁆ SL (Blocks m m))
      (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a),
      -- Switching the sign of the standard symplectic matrix leaves both actions unchanged.
      let J := Matrix.J (Fin m) ℂ
      (∀ X, (ω.map X).val = -X.valᴴ) ∧
      (∀ X, (a X).val = J * X.valᵀ * J) ∧
      (∀ X, ((involutionConjugation ω a hcomm hinv).map X).val = -(J * bar X.val * J)) ∧
      (∃ e : quaternionicSL (Fin m) ≃ₗ⁅ℝ⁆ (involutionConjugation ω a hcomm hinv).fixed,
        ∀ X, ((e X).val).val = quaternionicMatrix X.val) ∧
      (∃ e : complexFixed a ≃ₗ⁅ℂ⁆ LieAlgebra.Symplectic.sp (Fin m) ℂ,
        ∀ X, (e X).val = X.val.val)

/-- The two signature endpoints give negative conjugate transpose itself. -/
def compactEndpointsType : Prop :=
  ∀ p q : ℕ, p = 0 ∨ q = 0 →
    ∀ X : Matrix (Blocks p q) (Blocks p q) ℂ,
      -(signatureMatrix p q * Xᴴ * signatureMatrix p q) = -Xᴴ

/-- In size two the quaternionic real form is the compact real form. -/
def quaternionicRankOneType : Prop :=
  ∃ ω : Conjugation (SL (Blocks 1 1)),
    (∀ X, (ω.map X).val = -X.valᴴ) ∧
      ∃ e : quaternionicSL (Fin 1) ≃ₗ⁅ℝ⁆ ω.fixed,
        ∀ X, ((e X).val).val = quaternionicMatrix X.val

/-- A Hermitian involution is unitarily similar to a signature matrix,
with a reindexing of its positive and negative eigenvectors. -/
def signedHermitianNormalFormType : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    A.IsHermitian → A * A = 1 →
    ∃ (p q : ℕ) (e : ι ≃ Blocks p q) (U : (Matrix ι ι ℂ)ˣ),
      p + q = Fintype.card ι ∧ U.valᴴ = U.inv ∧
        Matrix.reindex e e (U.val * A * U.inv) = signatureMatrix p q

/-- The inner compact-involution branch of type A classification. -/
def innerCaseType : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ω : Conjugation (SL ι)) (a : SL ι ≃ₗ⁅ℂ⁆ SL ι)
    (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a),
    (∀ X, (ω.map X).val = -X.valᴴ) →
    (∃ U : (Matrix ι ι ℂ)ˣ, ∀ X, (a X).val = U.val * X.val * U.inv) →
    ∃ (p q : ℕ) (τ : Conjugation (SL (Blocks p q))) (b : SL ι ≃ₗ⁅ℂ⁆ SL (Blocks p q)),
      p + q = Fintype.card ι ∧
      (∀ X, (τ.map X).val = -(signatureMatrix p q * X.valᴴ * signatureMatrix p q)) ∧
      Intertwines (involutionConjugation ω a hcomm hinv) τ b

/-- The outer branch reduces to a unitary symmetric or skew-symmetric
matrix. The statement retains equality of the actions on the Lie algebra. -/
def outerRepresentativeType : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ω : Conjugation (SL ι)) (a : SL ι ≃ₗ⁅ℂ⁆ SL ι),
    Intertwines ω ω a → Function.Involutive a →
    (∀ X, (ω.map X).val = -X.valᴴ) →
    (∃ U : (Matrix ι ι ℂ)ˣ, ∀ X, (a X).val = U.val * (-X.valᵀ) * U.inv) →
    ∃ V : (Matrix ι ι ℂ)ˣ, V.valᴴ = V.inv ∧
      (V.valᵀ = V.val ∨ V.valᵀ = -V.val) ∧
      ∀ X, (a X).val = V.val * (-X.valᵀ) * V.inv

/-- The two matrix actions for complex automorphisms of the special linear algebra. -/
def matrixAutomorphismType : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ a : SL (Fin n) ≃ₗ⁅ℂ⁆ SL (Fin n),
    (∃ U : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ X, (a X).val = U.val * X.val * U.inv) ∨
    (∃ U : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ X, (a X).val = U.val * (-X.valᵀ) * U.inv)

/-- Unitary congruence for a symmetric matrix. -/
def symmetricCongruenceType : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    Aᴴ * A = 1 → Aᵀ = A →
    ∃ P : (Matrix ι ι ℂ)ˣ, P.valᴴ = P.inv ∧ A = P.val * P.valᵀ

/-- Unitary congruence for a skew-symmetric matrix, with its even size as an output. -/
def skewCongruenceType : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    Aᴴ * A = 1 → Aᵀ = -A →
    ∃ (m : ℕ) (e : ι ≃ Blocks m m) (P : (Matrix ι ι ℂ)ˣ),
      P.valᴴ = P.inv ∧
        A = P.val * Matrix.reindex e.symm e.symm (Matrix.J (Fin m) ℂ) * P.valᵀ

/-- Completeness of the symmetric and skew-symmetric outer normal forms. -/
def outerCaseType : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ω : Conjugation (SL ι)) (a : SL ι ≃ₗ⁅ℂ⁆ SL ι)
    (hcomm : Intertwines ω ω a) (hinv : Function.Involutive a),
    (∀ X, (ω.map X).val = -X.valᴴ) →
    (∃ U : (Matrix ι ι ℂ)ˣ, ∀ X, (a X).val = U.val * (-X.valᵀ) * U.inv) →
    Nonempty ((involutionConjugation ω a hcomm hinv).fixed ≃ₗ⁅ℝ⁆
      LieAlgebra.SpecialLinear.sl ι ℝ) ∨
    ∃ m : ℕ, Fintype.card ι = 2 * m ∧
      Nonempty ((involutionConjugation ω a hcomm hinv).fixed ≃ₗ⁅ℝ⁆ quaternionicSL (Fin m))

/-- The three type A families, up to real Lie algebra isomorphism. -/
def IsTypeARealFormModel (n : ℕ) (A : Type*) [LieRing A] [LieAlgebra ℝ A] : Prop :=
    (∃ p q : ℕ, p + q = n ∧
      ∃ (τ : Conjugation (SL (Blocks p q))) (_ : A ≃ₗ⁅ℝ⁆ τ.fixed),
        ∀ X, (τ.map X).val = -(signatureMatrix p q * X.valᴴ * signatureMatrix p q)) ∨
    Nonempty (A ≃ₗ⁅ℝ⁆ LieAlgebra.SpecialLinear.sl (Fin n) ℝ) ∨
    (∃ m : ℕ, 2 ≤ m ∧ n = 2 * m ∧ Nonempty (A ≃ₗ⁅ℝ⁆ quaternionicSL (Fin m)))

/-- Classification of embedded real forms. -/
def classificationType : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ S : LieSubalgebra ℝ (SL (Fin n)), IsRealForm S →
    IsTypeARealFormModel n S

/-- Classification of real Lie algebras with complexification of type A. -/
def abstractClassificationType : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (A : Type*) [LieRing A] [LieAlgebra ℝ A],
    Nonempty ((ℂ ⊗[ℝ] A) ≃ₗ⁅ℂ⁆ SL (Fin n)) → IsTypeARealFormModel n A

/-- In size two the indefinite unitary model is the split real form. -/
def splitRankOneType : Prop :=
  ∀ σ : Conjugation (SL (Blocks 1 1)),
    (∀ X, (σ.map X).val = -(signatureMatrix 1 1 * X.valᴴ * signatureMatrix 1 1)) →
    Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ LieAlgebra.SpecialLinear.sl (Fin 2) ℝ)

/-- Exchanging the two signature spaces preserves the real form. -/
def unitaryExchangeType : Prop :=
  ∀ p q : ℕ, ∀ (σ : Conjugation (SL (Blocks p q))) (τ : Conjugation (SL (Blocks q p))),
    (∀ X, (σ.map X).val = -(signatureMatrix p q * X.valᴴ * signatureMatrix p q)) →
    (∀ X, (τ.map X).val = -(signatureMatrix q p * X.valᴴ * signatureMatrix q p)) →
    Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ τ.fixed)

/-- Exchanging the two signature spaces is the only repetition within the
unitary row, including the compact endpoints. -/
def unitaryUniquenessType : Prop :=
  ∀ p q r s : ℕ, 2 ≤ p + q → p + q = r + s →
    ∀ (σ : Conjugation (SL (Blocks p q))) (τ : Conjugation (SL (Blocks r s))),
      (∀ X, (σ.map X).val = -(signatureMatrix p q * X.valᴴ * signatureMatrix p q)) →
      (∀ X, (τ.map X).val = -(signatureMatrix r s * X.valᴴ * signatureMatrix r s)) →
      (Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ τ.fixed) ↔ (p = r ∧ q = s) ∨ (p = s ∧ q = r))

/-- At size two the split form has exactly the indefinite unitary signature. -/
def splitRankOneUniquenessType : Prop :=
  ∀ p q : ℕ, p + q = 2 → ∀ σ : Conjugation (SL (Blocks p q)),
    (∀ X, (σ.map X).val = -(signatureMatrix p q * X.valᴴ * signatureMatrix p q)) →
    (Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ LieAlgebra.SpecialLinear.sl (Fin 2) ℝ) ↔ p = 1 ∧ q = 1)

/-- Above rank one the split, quaternionic, and unitary rows are disjoint. -/
def distinctRowsType : Prop :=
  (∀ p q : ℕ, 2 < p + q → ∀ σ : Conjugation (SL (Blocks p q)),
    (∀ X, (σ.map X).val = -(signatureMatrix p q * X.valᴴ * signatureMatrix p q)) →
    ¬Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ LieAlgebra.SpecialLinear.sl (Fin (p + q)) ℝ)) ∧
  (∀ p q m : ℕ, 2 ≤ m → p + q = 2 * m → ∀ σ : Conjugation (SL (Blocks p q)),
    (∀ X, (σ.map X).val = -(signatureMatrix p q * X.valᴴ * signatureMatrix p q)) →
    ¬Nonempty (σ.fixed ≃ₗ⁅ℝ⁆ quaternionicSL (Fin m))) ∧
  (∀ m : ℕ, 2 ≤ m →
    ¬Nonempty (LieAlgebra.SpecialLinear.sl (Fin (2 * m)) ℝ ≃ₗ⁅ℝ⁆ quaternionicSL (Fin m)))

end Specs.LieAlgebrasAndRepresentations.RealFormsTypeA
