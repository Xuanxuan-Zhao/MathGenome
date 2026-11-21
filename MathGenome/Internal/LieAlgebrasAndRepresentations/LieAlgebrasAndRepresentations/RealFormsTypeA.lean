import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormsTypeA
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsA
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.KillingCriterion
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanDecompositionSignature
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

namespace LieAlgebrasAndRepresentations.RealFormsTypeA

open Matrix
open RealForms
open Specs.LieAlgebrasAndRepresentations.RealFormsTypeA
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (involutionConjugation)
open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature (complexFixed)

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem trace_val (X : SL ι) : X.val.trace = 0 := X.property

/-- Negative conjugate transpose on the traceless complex matrices. -/
def compactConjugation : Conjugation (SL ι) where
  map :=
    { toFun := fun X => ⟨-X.valᴴ, by
        change (-X.valᴴ).trace = 0
        rw [trace_neg, trace_conjTranspose, trace_val, star_zero, neg_zero]⟩
      map_add' := fun X Y => Subtype.ext (by
        change (-(X.val + Y.val)ᴴ) = -X.valᴴ + -Y.valᴴ
        rw [conjTranspose_add, neg_add])
      map_smul' := fun r X => Subtype.ext (by
        change (-(r • X.val)ᴴ) = r • (-X.valᴴ)
        rw [conjTranspose_smul, star_trivial, smul_neg])
      map_lie' := fun {X Y} => Subtype.ext (by
        change (-(X.val * Y.val - Y.val * X.val)ᴴ) =
          (-X.valᴴ) * (-Y.valᴴ) - (-Y.valᴴ) * (-X.valᴴ)
        simp only [conjTranspose_sub, conjTranspose_mul, neg_mul_neg, neg_sub]) }
  antilinear c X := Subtype.ext (by
    change (-(c • X.val)ᴴ) = star c • (-X.valᴴ)
    rw [conjTranspose_smul, smul_neg])
  involutive X := Subtype.ext (by
    change (-(-X.valᴴ)ᴴ) = X.val
    simp)

private theorem compact_apply (X : SL ι) :
    (compactConjugation.map X).val = -X.valᴴ := rfl

/-- The complex Lie involution given by negative transpose. -/
def negativeTranspose : SL ι ≃ₗ⁅ℂ⁆ SL ι where
  toFun X := ⟨-X.valᵀ, by
    change (-X.valᵀ).trace = 0
    rw [trace_neg, trace_transpose, trace_val, neg_zero]⟩
  invFun X := ⟨-X.valᵀ, by
    change (-X.valᵀ).trace = 0
    rw [trace_neg, trace_transpose, trace_val, neg_zero]⟩
  left_inv X := Subtype.ext (by change (-(-X.valᵀ)ᵀ) = X.val; simp)
  right_inv X := Subtype.ext (by change (-(-X.valᵀ)ᵀ) = X.val; simp)
  map_add' X Y := Subtype.ext (by
    change (-(X.val + Y.val)ᵀ) = -X.valᵀ + -Y.valᵀ
    rw [transpose_add, neg_add])
  map_smul' c X := Subtype.ext (by
    change (-(c • X.val)ᵀ) = c • (-X.valᵀ)
    rw [transpose_smul, smul_neg])
  map_lie' {X Y} := Subtype.ext (by
    change (-(X.val * Y.val - Y.val * X.val)ᵀ) =
      (-X.valᵀ) * (-Y.valᵀ) - (-Y.valᵀ) * (-X.valᵀ)
    simp only [transpose_sub, transpose_mul, neg_mul_neg, neg_sub])

private theorem negativeTranspose_apply (X : SL ι) :
    (negativeTranspose X).val = -X.valᵀ := rfl

private theorem negativeTranspose_involutive :
    Function.Involutive (negativeTranspose : SL ι ≃ₗ⁅ℂ⁆ SL ι) := by
  intro X
  apply Subtype.ext
  simp [negativeTranspose_apply]

omit [Fintype ι] [DecidableEq ι] in
private theorem transpose_adjoint (X : Matrix ι ι ℂ) : Xᴴᵀ = bar X := rfl
omit [Fintype ι] [DecidableEq ι] in
private theorem adjoint_transpose (X : Matrix ι ι ℂ) : Xᵀᴴ = bar X := rfl

private theorem negativeTranspose_comm :
    Intertwines (compactConjugation : Conjugation (SL ι)) compactConjugation negativeTranspose := by
  intro X
  apply Subtype.ext
  simp only [compact_apply, negativeTranspose_apply, conjTranspose_neg, transpose_neg, neg_neg,
    transpose_adjoint, adjoint_transpose]

private theorem unit_conj_mul (U : (Matrix ι ι ℂ)ˣ) (A B : Matrix ι ι ℂ) :
    (U.val * A * U.inv) * (U.val * B * U.inv) = U.val * (A * B) * U.inv := by
  rw [← mul_assoc _ (U.val * B) U.inv, ← mul_assoc _ U.val B,
    mul_assoc (U.val * A) U.inv U.val, U.inv_val, mul_one, mul_assoc U.val A B]

/-- Inner conjugation on the traceless matrices. -/
def matrixConjugation (U : (Matrix ι ι ℂ)ˣ) : SL ι ≃ₗ⁅ℂ⁆ SL ι where
  toFun X := ⟨U.val * X.val * U.inv, by
    change (U.val * X.val * U.inv).trace = 0
    rw [trace_mul_comm (U.val * X.val) U.inv, ← mul_assoc, U.inv_val, one_mul, trace_val]⟩
  invFun X := ⟨U.inv * X.val * U.val, by
    change (U.inv * X.val * U.val).trace = 0
    rw [trace_mul_comm (U.inv * X.val) U.val, ← mul_assoc, U.val_inv, one_mul, trace_val]⟩
  left_inv X := Subtype.ext (by
    change U.inv * (U.val * X.val * U.inv) * U.val = X.val
    rw [← mul_assoc U.inv, ← mul_assoc U.inv, U.inv_val, one_mul, mul_assoc, U.inv_val, mul_one])
  right_inv X := Subtype.ext (by
    change U.val * (U.inv * X.val * U.val) * U.inv = X.val
    rw [← mul_assoc U.val, ← mul_assoc U.val, U.val_inv, one_mul, mul_assoc, U.val_inv, mul_one])
  map_add' X Y := Subtype.ext (by
    change U.val * (X.val + Y.val) * U.inv = U.val * X.val * U.inv + U.val * Y.val * U.inv
    simp only [mul_add, add_mul])
  map_smul' c X := Subtype.ext (by
    change U.val * (c • X.val) * U.inv = c • (U.val * X.val * U.inv)
    rw [Matrix.mul_smul, Matrix.smul_mul])
  map_lie' {X Y} := Subtype.ext (by
    change U.val * (X.val * Y.val - Y.val * X.val) * U.inv =
      (U.val * X.val * U.inv) * (U.val * Y.val * U.inv) -
      (U.val * Y.val * U.inv) * (U.val * X.val * U.inv)
    rw [unit_conj_mul, unit_conj_mul, mul_sub, sub_mul])

private theorem matrixConjugation_apply (U : (Matrix ι ι ℂ)ˣ) (X : SL ι) :
    (matrixConjugation U X).val = U.val * X.val * U.inv := rfl

private theorem matrixConjugation_comm (U : (Matrix ι ι ℂ)ˣ)
    (h : U.valᴴ = U.inv) (h' : U.invᴴ = U.val) :
    Intertwines (compactConjugation : Conjugation (SL ι)) compactConjugation
      (matrixConjugation U) := by
  intro X
  apply Subtype.ext
  simp only [matrixConjugation_apply, compact_apply, conjTranspose_mul, h, h',
    Matrix.mul_neg, Matrix.neg_mul, mul_assoc]

private theorem signature_squared (p q : ℕ) :
    signatureMatrix p q * signatureMatrix p q = 1 := by
  unfold signatureMatrix LieAlgebra.Orthogonal.indefiniteDiagonal
  rw [diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext i
  cases i <;> simp

private theorem signature_adjoint (p q : ℕ) :
    (signatureMatrix p q)ᴴ = signatureMatrix p q := by
  unfold signatureMatrix LieAlgebra.Orthogonal.indefiniteDiagonal
  rw [diagonal_conjTranspose]
  congr 1
  funext i
  cases i <;> simp

private def signatureUnit (p q : ℕ) : (Matrix (Blocks p q) (Blocks p q) ℂ)ˣ :=
  ⟨signatureMatrix p q, signatureMatrix p q, signature_squared p q, signature_squared p q⟩

theorem unitary_model : unitaryModelType := by
  intro p q
  let D := signatureMatrix p q
  let U := signatureUnit p q
  let a := matrixConjugation U
  have happly (X : SL (Blocks p q)) : (a X).val = D * X.val * D := rfl
  have hDD : D * D = 1 := signature_squared p q
  have hinv : Function.Involutive a := by
    intro X
    apply Subtype.ext
    rw [happly, happly, ← mul_assoc D (D * X.val), ← mul_assoc D D X.val,
      hDD, one_mul, mul_assoc X.val D D, hDD, mul_one]
  have hcomm : Intertwines compactConjugation compactConjugation a :=
    matrixConjugation_comm U (signature_adjoint p q) (signature_adjoint p q)
  have hσ (X : SL (Blocks p q)) :
      ((involutionConjugation compactConjugation a hcomm hinv).map X).val =
        -(D * X.valᴴ * D) := by
    change (a (compactConjugation.map X)).val = _
    rw [happly, compact_apply, Matrix.mul_neg, Matrix.neg_mul]
  refine ⟨compactConjugation, a, hcomm, hinv, compact_apply, happly, hσ, ?_, ?_⟩
  · intro X
    change ((involutionConjugation compactConjugation a hcomm hinv).map X = X) ↔ _
    rw [← Subtype.val_inj, hσ]
    constructor
    · intro h
      have h' := congrArg (D * ·) h
      rw [Matrix.mul_neg, ← mul_assoc D (D * X.valᴴ) D,
        ← mul_assoc D D X.valᴴ, hDD, one_mul] at h'
      rw [← h', add_neg_cancel]
    · intro h
      have h' : D * X.val = -(X.valᴴ * D) := eq_neg_of_add_eq_zero_right h
      have h'' := congrArg (D * ·) h'
      rwa [← mul_assoc, hDD, one_mul, Matrix.mul_neg, ← mul_assoc, eq_comm] at h''
  · intro X
    change (a X = X) ↔ _
    rw [← Subtype.val_inj, happly]
    have hentry (i j : Blocks p q) :
        (D * X.val * D) i j =
          (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i) * X.val i j *
          (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) j) := by
      simp [D, LieAlgebra.Orthogonal.indefiniteDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
    constructor
    · intro h
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have hc := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
        rw [hentry] at hc
        simp only [Sum.elim_inl, Sum.elim_inr, one_mul, mul_neg, mul_one] at hc
        linear_combination (-1 / 2 : ℂ) * hc
      · have hc := congrFun (congrFun h (Sum.inr i)) (Sum.inl j)
        rw [hentry] at hc
        simp only [Sum.elim_inl, Sum.elim_inr, mul_one, neg_mul, one_mul] at hc
        linear_combination (-1 / 2 : ℂ) * hc
    · rintro ⟨h₁, h₂⟩
      ext i j
      rw [hentry]
      cases i <;> cases j <;> simp [h₁, h₂]

private theorem split_apply (X : SL ι) :
    ((involutionConjugation compactConjugation negativeTranspose negativeTranspose_comm
        negativeTranspose_involutive).map X).val = bar X.val := by
  change (negativeTranspose (compactConjugation.map X)).val = _
  simp only [negativeTranspose_apply, compact_apply, transpose_neg, neg_neg,
    transpose_adjoint]

private def fixedMatrixEquiv (a : SL ι ≃ₗ⁅ℂ⁆ SL ι)
    (K : LieSubalgebra ℂ (Matrix ι ι ℂ)) (htrace : ∀ X ∈ K, X.trace = 0)
    (hfixed : ∀ X : SL ι, X ∈ complexFixed a ↔ X.val ∈ K) :
    complexFixed a ≃ₗ⁅ℂ⁆ K where
  toFun X := ⟨X.val.val, (hfixed X.val).mp X.property⟩
  invFun Y := ⟨⟨Y.val, htrace Y.val Y.property⟩, (hfixed _).mpr Y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

private theorem trace_of_similar_neg_transpose (X : Matrix ι ι ℂ)
    (U : (Matrix ι ι ℂ)ˣ) (h : U.val * (-Xᵀ) * U.inv = X) : X.trace = 0 := by
  have htr := congrArg Matrix.trace h
  rw [trace_mul_comm (U.val * (-Xᵀ)) U.inv, ← mul_assoc, U.inv_val, one_mul,
    trace_neg, trace_transpose] at htr
  linear_combination (-1 / 2 : ℂ) * htr

theorem split_model : splitModelType := by
  intro ι _ _
  let σ := involutionConjugation (compactConjugation : Conjugation (SL ι)) negativeTranspose
    negativeTranspose_comm negativeTranspose_involutive
  let f : LieAlgebra.SpecialLinear.sl ι ℝ →ₗ⁅ℝ⁆ σ.fixed :=
    { toFun := fun X => ⟨⟨X.val.map Complex.ofReal, by
          change (X.val.map Complex.ofRealHom).trace = 0
          rw [← AddMonoidHom.map_trace Complex.ofRealHom, show X.val.trace = 0 from X.property, map_zero]⟩,
        by
          apply Subtype.ext
          rw [split_apply]
          ext i j
          exact Complex.conj_ofReal _⟩
      map_add' := fun X Y => by
        apply Subtype.ext
        apply Subtype.ext
        ext i j
        exact Complex.ofReal_add _ _
      map_smul' := fun r X => by
        apply Subtype.ext
        apply Subtype.ext
        ext i j
        exact Complex.ofReal_mul _ _
      map_lie' := fun {X Y} => by
        apply Subtype.ext
        apply Subtype.ext
        change (X.val * Y.val - Y.val * X.val).map Complex.ofRealHom =
          X.val.map Complex.ofRealHom * Y.val.map Complex.ofRealHom -
            Y.val.map Complex.ofRealHom * X.val.map Complex.ofRealHom
        let g : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
        change g (X.val * Y.val - Y.val * X.val) = g X.val * g Y.val - g Y.val * g X.val
        simp only [map_sub, map_mul] }
  have hf (X : LieAlgebra.SpecialLinear.sl ι ℝ) : (f X).val.val = X.val.map Complex.ofReal := rfl
  have hbij : Function.Bijective f := by
    constructor
    · intro X Y h
      apply Subtype.ext
      ext i j
      exact Complex.ofReal_injective (congrFun (congrFun (congrArg (fun Z : σ.fixed =>
        Z.val.val) h) i) j)
    · intro X
      let Y : LieAlgebra.SpecialLinear.sl ι ℝ := ⟨X.val.val.map Complex.re, by
        change (X.val.val.map Complex.reLm).trace = 0
        rw [← AddMonoidHom.map_trace Complex.reLm, trace_val, map_zero]⟩
      refine ⟨Y, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rw [hf]
      ext i j
      have h : bar X.val.val = X.val.val := by
        rw [← split_apply]
        exact congrArg Subtype.val X.property
      exact Complex.conj_eq_iff_re.mp (congrFun (congrFun h i) j)
  refine ⟨compactConjugation, negativeTranspose, negativeTranspose_comm,
    negativeTranspose_involutive, compact_apply, negativeTranspose_apply,
    split_apply, ⟨LieEquiv.ofBijective f hbij, hf⟩, ?_⟩
  refine ⟨fixedMatrixEquiv negativeTranspose _ ?_ ?_, fun _ => rfl⟩
  · intro X h
    apply trace_of_similar_neg_transpose X 1
    simpa using (neg_eq_iff_eq_neg.mpr (LieAlgebra.Orthogonal.mem_so _ _ X |>.mp h))
  · intro X
    change (negativeTranspose X = X) ↔ _
    rw [← Subtype.val_inj, negativeTranspose_apply, LieAlgebra.Orthogonal.mem_so]
    exact neg_eq_iff_eq_neg

private def symplecticUnit (m : ℕ) : (Matrix (Blocks m m) (Blocks m m) ℂ)ˣ :=
  ⟨Matrix.J (Fin m) ℂ, -Matrix.J (Fin m) ℂ,
    by rw [Matrix.mul_neg, Matrix.J_squared, neg_neg],
    by rw [Matrix.neg_mul, Matrix.J_squared, neg_neg]⟩

private theorem symplectic_adjoint (m : ℕ) : (Matrix.J (Fin m) ℂ)ᴴ = -Matrix.J (Fin m) ℂ := by
  rw [show (Matrix.J (Fin m) ℂ)ᴴ = bar ((Matrix.J (Fin m) ℂ)ᵀ) from rfl]
  rw [Matrix.J_transpose]
  unfold bar
  rw [Matrix.map_neg _ (map_neg (starRingEnd ℂ)), Matrix.map_J]

private def symplecticInvolution (m : ℕ) : SL (Blocks m m) ≃ₗ⁅ℂ⁆ SL (Blocks m m) :=
  negativeTranspose.trans (matrixConjugation (symplecticUnit m))

private theorem symplecticInvolution_apply (m : ℕ) (X : SL (Blocks m m)) :
    (symplecticInvolution m X).val = Matrix.J (Fin m) ℂ * X.valᵀ * Matrix.J (Fin m) ℂ := by
  change Matrix.J (Fin m) ℂ * (-X.valᵀ) * (-Matrix.J (Fin m) ℂ) = _
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]

private theorem symplecticInvolution_involutive (m : ℕ) :
    Function.Involutive (symplecticInvolution m) := by
  intro X
  apply Subtype.ext
  let J := Matrix.J (Fin m) ℂ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  simp only [symplecticInvolution_apply, transpose_mul, Matrix.J_transpose,
    transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  change J * (J * (X.val * J)) * J = X.val
  rw [← mul_assoc J J (X.val * J), hJJ, neg_mul, one_mul, Matrix.neg_mul,
    mul_assoc, hJJ, Matrix.mul_neg, mul_one, neg_neg]

private theorem symplecticInvolution_comm (m : ℕ) :
    Intertwines compactConjugation compactConjugation (symplecticInvolution m) := by
  intro X
  have h := matrixConjugation_comm (symplecticUnit m) (symplectic_adjoint m)
    (by change (-Matrix.J (Fin m) ℂ)ᴴ = _; rw [conjTranspose_neg, symplectic_adjoint, neg_neg]; rfl)
  change compactConjugation.map (matrixConjugation (symplecticUnit m) (negativeTranspose X)) = _
  rw [h, negativeTranspose_comm]
  rfl

private def quaternionicConjugation (m : ℕ) : Conjugation (SL (Blocks m m)) :=
  involutionConjugation compactConjugation (symplecticInvolution m)
    (symplecticInvolution_comm m) (symplecticInvolution_involutive m)

private theorem quaternionicConjugation_apply (m : ℕ) (X : SL (Blocks m m)) :
    ((quaternionicConjugation m).map X).val = -(Matrix.J (Fin m) ℂ * bar X.val * Matrix.J (Fin m) ℂ) := by
  change (symplecticInvolution m (compactConjugation.map X)).val = _
  rw [symplecticInvolution_apply, compact_apply, transpose_neg, transpose_adjoint,
    Matrix.mul_neg, Matrix.neg_mul]

private theorem symplectic_fixed (m : ℕ) (X : SL (Blocks m m)) :
    X ∈ complexFixed (symplecticInvolution m) ↔
      X.val ∈ LieAlgebra.Symplectic.sp (Fin m) ℂ := by
  change (symplecticInvolution m X = X) ↔ _
  rw [← Subtype.val_inj, symplecticInvolution_apply, LieAlgebra.Symplectic.sp,
    mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  let J := Matrix.J (Fin m) ℂ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  change J * X.valᵀ * J = X.val ↔ X.valᵀ * J = J * (-X.val)
  constructor
  · intro h
    have h' := congrArg (J * ·) h
    rw [← mul_assoc J (J * X.valᵀ), ← mul_assoc J J, hJJ, neg_mul, one_mul,
      Matrix.neg_mul] at h'
    rw [Matrix.mul_neg, ← h', neg_neg]
  · intro h
    rw [mul_assoc, h, ← mul_assoc, hJJ, neg_mul, one_mul, neg_neg]

section Quaternionic

variable {m : ℕ}

private def qA (X : Matrix ι ι (Quaternion ℝ)) : Matrix ι ι ℂ :=
  fun i j => ⟨(X i j).re, (X i j).imI⟩

private def qB (X : Matrix ι ι (Quaternion ℝ)) : Matrix ι ι ℂ :=
  fun i j => ⟨(X i j).imJ, (X i j).imK⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem bar_add (X Y : Matrix ι ι ℂ) : bar (X + Y) = bar X + bar Y := by
  ext i j
  exact map_add (starRingEnd ℂ) _ _

omit [Fintype ι] [DecidableEq ι] in
private theorem bar_neg (X : Matrix ι ι ℂ) : bar (-X) = -bar X := by
  ext i j
  exact map_neg (starRingEnd ℂ) _

omit [Fintype ι] [DecidableEq ι] in
private theorem bar_bar (X : Matrix ι ι ℂ) : bar (bar X) = X := by
  ext i j
  exact star_star _

omit [DecidableEq ι] in
private theorem bar_mul (X Y : Matrix ι ι ℂ) : bar (X * Y) = bar X * bar Y :=
  Matrix.map_mul (f := starRingEnd ℂ)

omit [Fintype ι] [DecidableEq ι] in
private theorem bar_apply (X : Matrix ι ι ℂ) (i j : ι) :
    bar X i j = star (X i j) := rfl

private theorem quaternionic_transform (X : Matrix (Blocks m m) (Blocks m m) ℂ) :
    -(Matrix.J (Fin m) ℂ * bar X * Matrix.J (Fin m) ℂ) =
      fromBlocks (bar X.toBlocks₂₂) (-bar X.toBlocks₂₁)
        (-bar X.toBlocks₁₂) (bar X.toBlocks₁₁) := by
  rw [← fromBlocks_toBlocks X, bar, fromBlocks_map]
  simp only [Matrix.J, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    neg_one_mul, mul_neg_one, Matrix.one_mul, Matrix.mul_one,
    zero_add, add_zero, neg_neg, fromBlocks_neg, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂,
    toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  rfl

private theorem quaternionic_fixed_iff (X : SL (Blocks m m)) :
    X ∈ (quaternionicConjugation m).fixed ↔
      X.val.toBlocks₂₂ = bar X.val.toBlocks₁₁ ∧ X.val.toBlocks₂₁ = -bar X.val.toBlocks₁₂ := by
  change ((quaternionicConjugation m).map X = X) ↔ _
  rw [← Subtype.val_inj, quaternionicConjugation_apply, quaternionic_transform, ext_iff_blocks]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂]
  constructor
  · rintro ⟨_, _, h₂, h₁⟩
    exact ⟨h₁.symm, h₂.symm⟩
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂, bar_bar, bar_neg, bar_bar, neg_neg]
    exact ⟨rfl, rfl, rfl, rfl⟩

omit [DecidableEq ι] in
private theorem quaternionic_trace_re (X : Matrix ι ι (Quaternion ℝ)) :
    (quaternionicMatrix X).trace = ((2 * ∑ i, (X i i).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [Matrix.trace, Matrix.diag, quaternionicMatrix, Fintype.sum_sum_type,
      two_mul, bar, Matrix.map, Matrix.fromBlocks]
  · simp [Matrix.trace, Matrix.diag, quaternionicMatrix, Fintype.sum_sum_type,
      bar, Matrix.map, Matrix.fromBlocks, Finset.sum_neg_distrib]

omit [Fintype ι] [DecidableEq ι] in
private theorem quaternionic_add (X Y : Matrix ι ι (Quaternion ℝ)) :
    quaternionicMatrix (X + Y) = quaternionicMatrix X + quaternionicMatrix Y := by
  ext i j : 2
  cases i <;> cases j <;> apply Complex.ext <;>
    simp [quaternionicMatrix, bar, Matrix.map, Matrix.fromBlocks]
  all_goals abel

omit [Fintype ι] [DecidableEq ι] in
private theorem quaternionic_sub (X Y : Matrix ι ι (Quaternion ℝ)) :
    quaternionicMatrix (X - Y) = quaternionicMatrix X - quaternionicMatrix Y := by
  ext i j : 2
  cases i <;> cases j <;> apply Complex.ext <;>
    simp [quaternionicMatrix, bar, Matrix.map, Matrix.fromBlocks, neg_sub]
  all_goals abel

omit [Fintype ι] [DecidableEq ι] in
private theorem quaternionic_smul (r : ℝ) (X : Matrix ι ι (Quaternion ℝ)) :
    quaternionicMatrix (r • X) = r • quaternionicMatrix X := by
  ext i j : 2
  cases i <;> cases j <;> apply Complex.ext <;>
    simp [quaternionicMatrix, bar, Matrix.map, Matrix.fromBlocks, smul_eq_mul]

omit [DecidableEq ι] in
private theorem quaternionic_mul (X Y : Matrix ι ι (Quaternion ℝ)) :
    quaternionicMatrix (X * Y) = quaternionicMatrix X * quaternionicMatrix Y := by
  change fromBlocks (qA (X * Y)) (qB (X * Y)) (-bar (qB (X * Y))) (bar (qA (X * Y))) =
    fromBlocks (qA X) (qB X) (-bar (qB X)) (bar (qA X)) *
      fromBlocks (qA Y) (qB Y) (-bar (qB Y)) (bar (qA Y))
  rw [fromBlocks_multiply, fromBlocks_inj]
  have hA : qA (X * Y) = qA X * qA Y + qB X * -bar (qB Y) := by
    ext i j : 2
    apply Complex.ext
    all_goals
      simp only [qA, qB, mul_apply, Matrix.add_apply, Matrix.neg_apply, bar_apply,
        Complex.add_re, Complex.add_im, Complex.re_sum, Complex.im_sum]
      rw [← Finset.sum_add_distrib]
    · change (∑ k, X i k * Y k j).re = _
      rw [show (∑ k, X i k * Y k j).re = ∑ k, (X i k * Y k j).re from
        map_sum (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) _ _]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Quaternion.re_mul, Complex.mul_re, Complex.neg_re, Complex.neg_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    · change (∑ k, X i k * Y k j).imI = _
      rw [show (∑ k, X i k * Y k j).imI = ∑ k, (X i k * Y k j).imI from
        map_sum (QuaternionAlgebra.imIₗ (-1 : ℝ) 0 (-1)) _ _]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Quaternion.imI_mul, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
  have hB : qB (X * Y) = qA X * qB Y + qB X * bar (qA Y) := by
    ext i j : 2
    apply Complex.ext
    all_goals
      simp only [qA, qB, mul_apply, Matrix.add_apply, bar_apply,
        Complex.add_re, Complex.add_im, Complex.re_sum, Complex.im_sum]
      rw [← Finset.sum_add_distrib]
    · change (∑ k, X i k * Y k j).imJ = _
      rw [show (∑ k, X i k * Y k j).imJ = ∑ k, (X i k * Y k j).imJ from
        map_sum (QuaternionAlgebra.imJₗ (-1 : ℝ) 0 (-1)) _ _]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Quaternion.imJ_mul, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    · change (∑ k, X i k * Y k j).imK = _
      rw [show (∑ k, X i k * Y k j).imK = ∑ k, (X i k * Y k j).imK from
        map_sum (QuaternionAlgebra.imKₗ (-1 : ℝ) 0 (-1)) _ _]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Quaternion.imK_mul, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
  refine ⟨hA, hB, ?_, ?_⟩
  · rw [hB, bar_add, bar_mul, bar_mul, bar_bar]
    simp only [neg_add, Matrix.mul_neg, Matrix.neg_mul, add_comm]
  · rw [hA, bar_add, bar_mul, bar_mul, bar_neg, bar_bar, add_comm, Matrix.mul_neg, Matrix.neg_mul]

theorem quaternionic_model : quaternionicModelType := by
  intro m
  let σ := quaternionicConjugation m
  let f : quaternionicSL (Fin m) →ₗ⁅ℝ⁆ σ.fixed :=
    { toFun := fun X => ⟨⟨quaternionicMatrix X.val, by
          change (quaternionicMatrix X.val).trace = 0
          have h : ∑ i, (X.val i i).re = 0 := X.property
          simp [quaternionic_trace_re, h]⟩, by
          apply (quaternionic_fixed_iff _).2
          exact ⟨rfl, rfl⟩⟩
      map_add' := fun X Y => Subtype.ext (Subtype.ext (quaternionic_add X.val Y.val))
      map_smul' := fun r X => Subtype.ext (Subtype.ext (quaternionic_smul r X.val))
      map_lie' := fun {X Y} => Subtype.ext (Subtype.ext (by
        change quaternionicMatrix (X.val * Y.val - Y.val * X.val) =
          quaternionicMatrix X.val * quaternionicMatrix Y.val -
            quaternionicMatrix Y.val * quaternionicMatrix X.val
        rw [quaternionic_sub, quaternionic_mul, quaternionic_mul])) }
  have hf (X : quaternionicSL (Fin m)) : (f X).val.val = quaternionicMatrix X.val := rfl
  have hbij : Function.Bijective f := by
    constructor
    · intro X Y h
      have he : quaternionicMatrix X.val = quaternionicMatrix Y.val :=
        congrArg (fun Z : σ.fixed => Z.val.val) h
      have ha : qA X.val = qA Y.val := congrArg Matrix.toBlocks₁₁ he
      have hb : qB X.val = qB Y.val := congrArg Matrix.toBlocks₁₂ he
      apply Subtype.ext
      apply Matrix.ext
      intro i j
      have h₁ := congrFun (congrFun ha i) j
      have h₂ := congrFun (congrFun hb i) j
      exact QuaternionAlgebra.ext (congrArg Complex.re h₁) (congrArg Complex.im h₁)
        (congrArg Complex.re h₂) (congrArg Complex.im h₂)
    · intro X
      obtain ⟨h₂₂, h₂₁⟩ := (quaternionic_fixed_iff X.val).1 X.property
      let Y : Matrix (Fin m) (Fin m) (Quaternion ℝ) := fun i j =>
        ⟨(X.val.val.toBlocks₁₁ i j).re, (X.val.val.toBlocks₁₁ i j).im,
          (X.val.val.toBlocks₁₂ i j).re, (X.val.val.toBlocks₁₂ i j).im⟩
      have he : quaternionicMatrix Y = X.val.val := by
        apply ext_iff_blocks.mpr
        exact ⟨rfl, rfl, h₂₁.symm, h₂₂.symm⟩
      have ht := quaternionic_trace_re Y
      rw [he, trace_val] at ht
      have ht' := Complex.ofReal_eq_zero.mp ht.symm
      have hY : Y ∈ quaternionicSL (Fin m) := by
        change ∑ i, (Y i i).re = 0
        linarith
      exact ⟨⟨Y, hY⟩, Subtype.ext (Subtype.ext he)⟩
  refine ⟨compactConjugation, symplecticInvolution m, symplecticInvolution_comm m,
    symplecticInvolution_involutive m, compact_apply, symplecticInvolution_apply m,
    quaternionicConjugation_apply m, ⟨LieEquiv.ofBijective f hbij, hf⟩,
    ⟨fixedMatrixEquiv (symplecticInvolution m) _ ?_ (symplectic_fixed m), fun _ => rfl⟩⟩
  intro X hX
  apply trace_of_similar_neg_transpose X (symplecticUnit m)
  change Matrix.J (Fin m) ℂ * (-Xᵀ) * (-Matrix.J (Fin m) ℂ) = X
  simp only [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hX
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  rw [mul_assoc, hX, ← mul_assoc, Matrix.J_squared, neg_mul, one_mul, neg_neg]

end Quaternionic

section Compactness

open private killing_fixed from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (IsCompact)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
private theorem trace_reindex_matrix (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    (Matrix.reindex e e A).trace = A.trace := by
  change ∑ i : κ, A (e.symm i) (e.symm i) = ∑ i : ι, A i i
  exact e.symm.sum_comp (fun i => A i i)

/-- Changing coordinate names preserves the traceless Lie algebras. -/
def reindexSL (e : ι ≃ κ) : SL ι ≃ₗ⁅ℂ⁆ SL κ :=
  (Matrix.reindexLieEquiv e).ofSubalgebras (SL ι) (SL κ) <| by
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      change (Matrix.reindex e e Y).trace = 0
      exact (trace_reindex_matrix e Y).trans hY
    · intro hX
      let Y := Matrix.reindex e.symm e.symm X
      exact ⟨Y, (trace_reindex_matrix e.symm X).trans hX,
        (Matrix.reindex e e).apply_symm_apply X⟩

private theorem reindexSL_apply (e : ι ≃ κ) (X : SL ι) :
    (reindexSL e X).val = Matrix.reindex e e X.val := rfl

private theorem reindexSL_intertwines (e : ι ≃ κ) :
    Intertwines (compactConjugation : Conjugation (SL ι))
      (compactConjugation : Conjugation (SL κ)) (reindexSL e) := by
  intro X
  apply Subtype.ext
  rfl

private theorem compact_diagonalized {n : ℕ} (X : (compactConjugation :
    Conjugation (SL (Fin (n+1)))).fixed) :
    ∃ (U : (Matrix (Fin (n+1)) (Fin (n+1)) ℂ)ˣ),
      Intertwines compactConjugation compactConjugation (matrixConjugation U) ∧
        (matrixConjugation U X.val).val.IsDiag := by
  have hx : X.val.valᴴ = -X.val.val := by
    have h : -X.val.valᴴ = X.val.val := congrArg Subtype.val X.property
    exact neg_eq_iff_eq_neg.mp h
  have hh : (Complex.I • X.val.val).IsHermitian := by
    change (Complex.I • X.val.val)ᴴ = Complex.I • X.val.val
    rw [conjTranspose_smul, hx, Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg]
  let u := star hh.eigenvectorUnitary
  let U := Unitary.toUnits u
  have hU : (U.val)ᴴ = U.inv := rfl
  have hU' : (U.inv)ᴴ = U.val := star_star _
  refine ⟨U, matrixConjugation_comm U hU hU', ?_⟩
  have hdiag := hh.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply] at hdiag
  change U.val * (Complex.I • X.val.val) * U.inv = _ at hdiag
  rw [Matrix.mul_smul, Matrix.smul_mul, ← matrixConjugation_apply] at hdiag
  intro i j hij
  have hz := congrFun (congrFun hdiag i) j
  rw [Matrix.diagonal_apply_ne _ hij] at hz
  exact (mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero

private theorem compactFin (n : ℕ) : IsCompact (compactConjugation :
    Conjugation (SL (Fin (n+1)))) := by
  intro X hX
  obtain ⟨U, hcomm, hd⟩ := compact_diagonalized X
  let Z := matrixConjugation U X.val
  have hz : Z ≠ 0 := fun h => hX (Subtype.ext ((matrixConjugation U).injective
    (h.trans (map_zero (matrixConjugation U)).symm)))
  have hzfix : compactConjugation.map Z = Z := (hcomm X.val).trans
    (congrArg (matrixConjugation U) X.property)
  have hre (i : Fin (n+1)) : (Z.val i i).re = 0 := by
    have h := congrFun (congrFun (congrArg Subtype.val hzfix) i) i
    change -star (Z.val i i) = Z.val i i at h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hpos : 0 < ∑ i : Fin (n+1), (Z.val i i).im ^ 2 := by
    have hsome : ∃ i : Fin (n+1), (Z.val i i).im ≠ 0 := by
      by_contra! hh
      apply hz
      apply Subtype.ext
      apply Matrix.ext
      intro i j
      by_cases h : i = j
      · subst j
        exact Complex.ext (hre i) (hh i)
      · exact hd h
    obtain ⟨i, hi⟩ := hsome
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  let H : Specs.LieAlgebrasAndRepresentations.ClassicalRootsA.cartan n := ⟨Z, hd⟩
  have hb : _root_.killingForm ℂ (SL (Fin (n+1))) Z Z =
      (2 * (n + 1) : ℂ) * ∑ i, Z.val i i * Z.val i i :=
    LieAlgebrasAndRepresentations.ClassicalRootsA.killing_diagonal H H
  have hB := congrArg Complex.re (killing_fixed compactConjugation X X)
  rw [← LieAlgebra.killingForm_of_equiv_apply (matrixConjugation U) X.val X.val] at hB
  change (_root_.killingForm ℂ (SL (Fin (n+1))) Z Z).re = _ at hB
  rw [hb] at hB
  have hsum : (∑ i, Z.val i i * Z.val i i).re = -(∑ i, (Z.val i i).im ^ 2) := by
    rw [Complex.re_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [Complex.mul_re, hre i, pow_two]
  have hfactor : (2 * (n + 1) : ℂ) = ((2 * (n + 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [hfactor] at hB
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    hsum] at hB
  rw [← hB]
  exact mul_neg_of_pos_of_neg (by positivity) (neg_neg_of_pos hpos)

theorem compact_matrix : compactMatrixType := by
  intro ι _ _
  refine ⟨compactConjugation, compact_apply, ?_⟩
  intro X hX
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h
    exact False.elim (hX (Subtype.ext (Subtype.ext (Subsingleton.elim _ _))))
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    let e : ι ≃ Fin (n+1) := (Fintype.equivFin ι).trans (finCongr hn)
    let a := reindexSL e
    let Y : (compactConjugation : Conjugation (SL (Fin (n+1)))).fixed :=
      ⟨a X.val, (reindexSL_intertwines e X.val).trans (congrArg a X.property)⟩
    have hY : Y ≠ 0 := fun hy => hX (Subtype.ext (a.injective
      ((congrArg Subtype.val hy).trans (map_zero a).symm)))
    have heq : _root_.killingForm ℝ (compactConjugation : Conjugation (SL ι)).fixed X X =
        _root_.killingForm ℝ (compactConjugation : Conjugation (SL (Fin (n+1)))).fixed Y Y := by
      apply Complex.ofReal_injective
      rw [← killing_fixed compactConjugation X X, ← killing_fixed compactConjugation Y Y]
      exact (LieAlgebra.killingForm_of_equiv_apply a X.val X.val).symm
    rw [heq]
    exact compactFin n Y hY

theorem compactConjugation_isCompact (ι : Type) [Fintype ι] [DecidableEq ι] :
    IsCompact (compactConjugation : Conjugation (SL ι)) := by
  obtain ⟨ω, hω, hc⟩ := compact_matrix ι
  have h : ω = compactConjugation := by
    apply Conjugation.ext_map
    ext X : 1
    exact Subtype.ext ((hω X).trans (compact_apply X).symm)
  exact h ▸ hc

open private hermitian_positive from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

theorem special_linear_semisimple (ι : Type) [Fintype ι] [DecidableEq ι] :
    Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ (SL ι) := by
  obtain ⟨ω, _, hc⟩ := compact_matrix ι
  apply (semisimple_iff_killingForm_nondegenerate (k := ℂ) (L := SL ι)).2
  constructor
  · intro X hX
    by_contra h
    have hpos := hermitian_positive ω hc h
    have hz : Specs.LieAlgebrasAndRepresentations.PolarRealStructures.hermitian ω X X = 0 := by
      change -_root_.killingForm ℂ (SL ι) (ω.map X) X = 0
      rw [LieModule.traceForm_comm ℂ (SL ι) (SL ι)]
      exact neg_eq_zero.mpr (hX _)
    simp [hz] at hpos
  · intro X hX
    by_contra h
    have hpos := hermitian_positive ω hc h
    have hz : Specs.LieAlgebrasAndRepresentations.PolarRealStructures.hermitian ω X X = 0 := by
      change -_root_.killingForm ℂ (SL ι) (ω.map X) X = 0
      exact neg_eq_zero.mpr (hX _)
    simp [hz] at hpos

end Compactness

theorem compact_endpoints : compactEndpointsType := by
  intro p q h X
  rcases h with rfl | rfl
  · have hD : signatureMatrix 0 q = -1 := by
      unfold signatureMatrix LieAlgebra.Orthogonal.indefiniteDiagonal
      rw [← diagonal_one, diagonal_neg]
      congr 1
      funext i
      cases i with
      | inl i => exact Fin.elim0 i
      | inr i => rfl
    rw [hD, neg_one_mul, mul_neg_one, neg_neg]
  · have hD : signatureMatrix p 0 = 1 := by
      unfold signatureMatrix LieAlgebra.Orthogonal.indefiniteDiagonal
      rw [← diagonal_one]
      congr 1
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact Fin.elim0 i
    rw [hD, one_mul, mul_one]

private theorem symplecticInvolution_rank_one (X : SL (Blocks 1 1)) :
    symplecticInvolution 1 X = X := by
  apply Subtype.ext
  rw [symplecticInvolution_apply]
  have htr : X.val (Sum.inl 0) (Sum.inl 0) + X.val (Sum.inr 0) (Sum.inr 0) = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Fin.sum_univ_one] using trace_val X
  generalize hY : X.valᵀ = Y
  have ht (i j : Blocks 1 1) : Y i j = X.val j i := by rw [← hY]; rfl
  rw [← fromBlocks_toBlocks Y, Matrix.J, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, neg_one_mul, mul_neg_one, Matrix.one_mul,
    Matrix.mul_one, zero_add, add_zero, neg_neg]
  apply Matrix.ext
  intro i j
  cases i <;> cases j
  all_goals
    rename_i i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i j
    simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
      Matrix.toBlocks₂₂, ht]
  · exact neg_eq_of_add_eq_zero_left htr
  · exact neg_eq_of_add_eq_zero_right htr

theorem quaternionic_rank_one : quaternionicRankOneType := by
  obtain ⟨ω, a, hcomm, hinv, hω, ha, _, ⟨e, he⟩, _⟩ := quaternionic_model 1
  have ha' : ∀ X : SL (Blocks 1 1), a X = X := by
    intro X
    apply Subtype.ext
    rw [ha, ← symplecticInvolution_apply, symplecticInvolution_rank_one]
  have hσ : (involutionConjugation ω a hcomm hinv).fixed = ω.fixed := by
    ext X
    change (a (ω.map X) = X) ↔ (ω.map X = X)
    rw [ha']
  refine ⟨ω, hω, ?_⟩
  let f := (LieEquiv.refl : SL (Blocks 1 1) ≃ₗ⁅ℝ⁆ SL (Blocks 1 1)).ofSubalgebras
    (involutionConjugation ω a hcomm hinv).fixed ω.fixed (by
      change (involutionConjugation ω a hcomm hinv).fixed.map (LieHom.id) = ω.fixed
      rw [← hσ]
      ext X
      constructor
      · rintro ⟨Y, hY, rfl⟩
        exact hY
      · intro hX
        exact ⟨X, hX, rfl⟩)
  exact ⟨e.trans f, he⟩

section CompactMatrixRepresentatives

private theorem matrixConjugation_mul (U V : (Matrix ι ι ℂ)ˣ) (X : SL ι) :
    matrixConjugation (U * V) X = matrixConjugation U (matrixConjugation V X) := by
  apply Subtype.ext
  simp only [matrixConjugation_apply]
  change (U.val * V.val) * X.val * (V.inv * U.inv) =
    U.val * (V.val * X.val * V.inv) * U.inv
  simp only [← mul_assoc]

private theorem matrixConjugation_scalar_iff (U : (Matrix ι ι ℂ)ˣ) :
    (∀ X : SL ι, matrixConjugation U X = X) ↔ ∃ c : ℂ, U.val = Matrix.scalar ι c := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := U.val) (by
      intro i j hij
      let X := LieAlgebra.SpecialLinear.single i j hij (1 : ℂ)
      have hX : U.val * X.val * U.inv = X.val :=
        congrArg Subtype.val (h X)
      have hm := congrArg (· * U.val) hX
      rw [mul_assoc (U.val * X.val) U.inv U.val, U.inv_val, mul_one] at hm
      exact hm.symm)
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩ X
    apply Subtype.ext
    rw [matrixConjugation_apply]
    have hh : Commute U.val X.val := hc ▸ Matrix.scalar_comm c (Commute.all _) X.val
    rw [hh.eq, mul_assoc, U.val_inv, mul_one]

private theorem compact_conjugation_matrixConjugation
    (U : (Matrix ι ι ℂ)ˣ) (X : SL ι) :
    compactConjugation.map (matrixConjugation U (compactConjugation.map X)) =
      matrixConjugation (star U)⁻¹ X := by
  apply Subtype.ext
  change -(U.val * (-X.valᴴ) * U.inv)ᴴ = U.invᴴ * X.val * U.valᴴ
  simp only [conjTranspose_mul, conjTranspose_neg, conjTranspose_conjTranspose,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, mul_assoc]

/-- The Gram matrix of an inner compact automorphism is scalar. -/
theorem compact_inner_gram (U : (Matrix ι ι ℂ)ˣ)
    (h : Intertwines compactConjugation compactConjugation (matrixConjugation U)) :
    ∃ c : ℂ, U.valᴴ * U.val = Matrix.scalar ι c := by
  have hAd (X : SL ι) : matrixConjugation U X = matrixConjugation (star U)⁻¹ X := by
    rw [← compact_conjugation_matrixConjugation, h, compactConjugation.involutive]
  apply (matrixConjugation_scalar_iff (star U * U)).mp
  intro X
  rw [matrixConjugation_mul, hAd, ← matrixConjugation_mul, mul_inv_cancel]
  apply Subtype.ext
  simp [matrixConjugation_apply]

/-- An inner involution is represented by a matrix whose square is scalar. -/
theorem inner_involution_scalar_square (U : (Matrix ι ι ℂ)ˣ)
    (h : Function.Involutive (matrixConjugation U)) :
    ∃ c : ℂ, U.val * U.val = Matrix.scalar ι c := by
  apply (matrixConjugation_scalar_iff (U * U)).mp
  intro X
  rw [matrixConjugation_mul, h]

private def transposeUnit (U : (Matrix ι ι ℂ)ˣ) : (Matrix ι ι ℂ)ˣ :=
  ⟨U.valᵀ, U.invᵀ,
    by rw [← transpose_mul, U.inv_val, transpose_one],
    by rw [← transpose_mul, U.val_inv, transpose_one]⟩

private theorem transpose_matrixConjugation (U : (Matrix ι ι ℂ)ˣ) (X : SL ι) :
    negativeTranspose (matrixConjugation U (negativeTranspose X)) =
      matrixConjugation (transposeUnit U⁻¹) X := by
  apply Subtype.ext
  simp only [negativeTranspose_apply, matrixConjugation_apply]
  change -(U.val * (-X.valᵀ) * U.inv)ᵀ = U.invᵀ * X.val * U.valᵀ
  simp only [transpose_mul, transpose_neg, transpose_transpose, Matrix.mul_neg,
    Matrix.neg_mul, neg_neg, mul_assoc]

/-- A representative for an outer involution is symmetric or skew-symmetric. -/
theorem outer_involution_transpose_sign [Nonempty ι]
    (U : (Matrix ι ι ℂ)ˣ)
    (h : Function.Involutive (negativeTranspose.trans (matrixConjugation U))) :
    U.valᵀ = U.val ∨ U.valᵀ = -U.val := by
  let V := U * transposeUnit U⁻¹
  obtain ⟨c, hc⟩ := (matrixConjugation_scalar_iff V).mp (by
    intro X
    rw [matrixConjugation_mul, ← transpose_matrixConjugation]
    exact h X)
  change U.val * U.invᵀ = Matrix.scalar ι c at hc
  have hU := congrArg (· * U.valᵀ) hc
  rw [mul_assoc, ← transpose_mul, U.val_inv, transpose_one, mul_one,
    scalar_apply, ← smul_eq_diagonal_mul] at hU
  have ht := congrArg Matrix.transpose hU
  rw [transpose_smul, transpose_transpose] at ht
  have hs : U.val = (c * c) • U.val := by
    calc
      U.val = c • U.valᵀ := hU
      _ = c • (c • U.val) := congrArg (c • ·) ht
      _ = (c * c) • U.val := smul_smul _ _ _
  have hs' := congrArg (· * U.inv) hs
  rw [Matrix.smul_mul, U.val_inv] at hs'
  let i : ι := Classical.choice inferInstance
  have hs'' := congrFun (congrFun hs' i) i
  have hc' : c * c = 1 := by simpa [Matrix.one_apply, Matrix.smul_apply, smul_eq_mul] using hs''.symm
  rcases mul_self_eq_one_iff.mp hc' with hc' | hc'
  · left
    simpa [hc'] using ht
  · right
    simpa [hc'] using ht

private theorem scalar_gram_positive [Nonempty ι] (U : (Matrix ι ι ℂ)ˣ) (c : ℂ)
    (hc : U.valᴴ * U.val = Matrix.scalar ι c) :
    ∃ r : ℝ, 0 < r ∧ c = (r : ℂ) := by
  let i : ι := Classical.choice inferInstance
  have he := congrFun (congrFun hc i) i
  rw [scalar_apply, diagonal_apply_eq, Matrix.mul_apply] at he
  change ∑ k, star (U.val k i) * U.val k i = c at he
  simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum] at he
  refine ⟨∑ k, Complex.normSq (U.val k i), ?_, he.symm⟩
  have hnonzero : ∃ k, U.val k i ≠ 0 := by
    by_contra! hzero
    have hi := congrFun (congrFun U.inv_val i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at hi
    simp [hzero] at hi
  obtain ⟨k, hk⟩ := hnonzero
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨k, Finset.mem_univ _, Complex.normSq_pos.mpr hk⟩

/-- A compact inner automorphism has a unitary matrix representative. -/
theorem compact_inner_unitary [Nonempty ι] (U : (Matrix ι ι ℂ)ˣ)
    (h : Intertwines compactConjugation compactConjugation (matrixConjugation U)) :
    ∃ V : (Matrix ι ι ℂ)ˣ, V.valᴴ = V.inv ∧ matrixConjugation V = matrixConjugation U := by
  obtain ⟨c, hc⟩ := compact_inner_gram U h
  obtain ⟨r, hr, rfl⟩ := scalar_gram_positive U c hc
  let t : ℂ := (Real.sqrt r : ℂ)
  have htn : t ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hr).ne'
  have htt : t * t = r := by
    change (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = _
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr.le]
  have hstar : star t = t := Complex.conj_ofReal _
  let W := Units.map (Matrix.scalar ι).toMonoidHom (Units.mk0 t⁻¹ (inv_ne_zero htn))
  let V := W * U
  have hW : W.val = Matrix.scalar ι t⁻¹ := rfl
  have hv : V.val = t⁻¹ • U.val := by
    change W.val * U.val = _
    rw [hW, scalar_apply, ← smul_eq_diagonal_mul]
  have hunit : V.valᴴ * V.val = 1 := by
    rw [hv, conjTranspose_smul, star_inv₀, hstar, Matrix.smul_mul, Matrix.mul_smul,
      hc, smul_smul, ← mul_inv, htt, scalar_apply, ← Matrix.diagonal_smul,
      Pi.smul_def]
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    rw [← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ hr'
  refine ⟨V, ?_, ?_⟩
  · have hv' := congrArg (· * V.inv) hunit
    rwa [mul_assoc, V.val_inv, mul_one, one_mul] at hv'
  · ext X
    rw [matrixConjugation_mul, (matrixConjugation_scalar_iff W).mpr ⟨t⁻¹, hW⟩]

/-- The projective representative of an inner compact involution can be
chosen both unitary and of square one. -/
theorem compact_inner_signed [Nonempty ι] (U₀ : (Matrix ι ι ℂ)ˣ)
    (h : Intertwines compactConjugation compactConjugation (matrixConjugation U₀))
    (hinv : Function.Involutive (matrixConjugation U₀)) :
    ∃ V : (Matrix ι ι ℂ)ˣ, V.val.IsHermitian ∧ V.val * V.val = 1 ∧
      matrixConjugation V = matrixConjugation U₀ := by
  obtain ⟨U, hU, hAd⟩ := compact_inner_unitary U₀ h
  obtain ⟨c, hc⟩ := inner_involution_scalar_square U (hAd.symm ▸ hinv)
  have hcunit : (star c) * c = 1 := by
    have hUU : (U.val * U.val)ᴴ * (U.val * U.val) = 1 := by
      rw [conjTranspose_mul, hU, mul_assoc, ← mul_assoc U.inv U.val,
        U.inv_val, one_mul, U.inv_val]
    rw [hc, scalar_apply, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one] at hUU
    let i : ι := Classical.choice inferInstance
    exact congrFun (Matrix.diagonal_injective hUU) i
  have hcne : c ≠ 0 := by
    intro ht
    simp [ht] at hcunit
  obtain ⟨t, ht⟩ := IsAlgClosed.isSquare c
  have htn : t ≠ 0 := fun h => hcne (by simp [ht, h])
  have htnorm : Complex.normSq t = 1 := by
    have hcnorm : (Complex.normSq c : ℂ) = 1 :=
      Complex.normSq_eq_conj_mul_self.trans hcunit
    have hcnorm' : Complex.normSq c = 1 := Complex.ofReal_injective (hcnorm.trans (by simp))
    rw [ht, Complex.normSq_mul] at hcnorm'
    exact (mul_self_eq_one_iff.mp hcnorm').resolve_right (by
      have hn := Complex.normSq_nonneg t
      linarith)
  have hstar : star t * t = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, htnorm, Complex.ofReal_one]
  let W := Units.map (Matrix.scalar ι).toMonoidHom (Units.mk0 t⁻¹ (inv_ne_zero htn))
  let V := W * U
  have hW : W.val = Matrix.scalar ι t⁻¹ := rfl
  have hv : V.val = t⁻¹ • U.val := by
    change W.val * U.val = _
    rw [hW, scalar_apply, ← smul_eq_diagonal_mul]
  have hs : V.val * V.val = 1 := by
    rw [hv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_inv, ← ht, hc,
      scalar_apply, ← diagonal_smul, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ hcne
  have hvunit : V.valᴴ * V.val = 1 := by
    rw [hv, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      star_inv₀, ← mul_inv, hstar, inv_one, one_smul, hU, U.inv_val]
  have hherm : V.val.IsHermitian := by
    change V.valᴴ = V.val
    have hm := congrArg (· * V.inv) (hvunit.trans hs.symm)
    simpa only [mul_assoc, V.val_inv, mul_one] using hm
  have hV : matrixConjugation V = matrixConjugation U := by
    apply LieEquiv.ext
    intro X
    exact (matrixConjugation_mul W U X).trans
      ((matrixConjugation_scalar_iff W).mpr ⟨t⁻¹, hW⟩ _)
  exact ⟨V, hherm, hs, hV.trans hAd⟩

theorem compact_outer_comm (U : (Matrix ι ι ℂ)ˣ)
    (h : Intertwines compactConjugation compactConjugation
      (negativeTranspose.trans (matrixConjugation U))) :
    Intertwines compactConjugation compactConjugation (matrixConjugation U) := by
  intro X
  have hx := h (negativeTranspose X)
  change compactConjugation.map (matrixConjugation U (negativeTranspose (negativeTranspose X))) =
    matrixConjugation U (negativeTranspose (compactConjugation.map (negativeTranspose X))) at hx
  rwa [negativeTranspose_involutive, negativeTranspose_comm, negativeTranspose_involutive] at hx

theorem signed_hermitian_normal_form : signedHermitianNormalFormType := by
  intro ι _ _ A hA hsq
  classical
  let u := star hA.eigenvectorUnitary
  let U := Unitary.toUnits u
  have hU : U.valᴴ = U.inv := rfl
  let d : ι → ℂ := fun i => (hA.eigenvalues i : ℂ)
  have hdiag := hA.conjStarAlgAut_star_eigenvectorUnitary
  change Unitary.conjStarAlgAut ℂ _ u A = diagonal d at hdiag
  have hdsq : diagonal d * diagonal d = 1 := by
    rw [← hdiag, ← map_mul, hsq, map_one]
  have hsign (i : ι) : d i = 1 ∨ d i = -1 := by
    apply mul_self_eq_one_iff.mp
    have h := congrFun (congrFun hdsq i) i
    simpa [diagonal_mul_diagonal, one_apply] using h
  let P := {i : ι // d i = 1}
  let Q := {i : ι // d i ≠ 1}
  let p := Fintype.card P
  let q := Fintype.card Q
  let ep := Fintype.equivFin P
  let eq := Fintype.equivFin Q
  let e := (Equiv.sumCompl (fun i => d i = 1)).symm.trans (Equiv.sumCongr ep eq)
  refine ⟨p, q, e, U, ?_, hU, ?_⟩
  · simpa [Fintype.card_sum] using (Fintype.card_congr e).symm
  · change Matrix.reindex e e (Unitary.conjStarAlgAut ℂ _ u A) = _
    rw [hdiag]
    unfold signatureMatrix LieAlgebra.Orthogonal.indefiniteDiagonal
    rw [Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext x
    cases x with
    | inl i =>
        change d (ep.symm i).val = 1
        exact (ep.symm i).property
    | inr i =>
        change d (eq.symm i).val = -1
        exact (hsign (eq.symm i).val).resolve_left (eq.symm i).property

theorem inner_case : innerCaseType := by
  intro ι _ _ _ ω a hcomm hinv hω hAd
  obtain ⟨W, hW⟩ := hAd
  have ha : a = matrixConjugation W := LieEquiv.ext fun X => Subtype.ext (hW X)
  subst a
  have hω' : ω = compactConjugation := by
    apply RealForms.Conjugation.ext_map
    ext X : 1
    exact Subtype.ext (hω X)
  subst ω
  obtain ⟨A, hA, hAsq, hAd⟩ := compact_inner_signed W hcomm hinv
  obtain ⟨p, q, e, U, hn, hU, hdiag⟩ := signed_hermitian_normal_form ι A.val hA hAsq
  have hAinv : A.inv = A.val := by
    have h := congrArg (· * A.inv) hAsq
    simpa only [mul_assoc, A.val_inv, mul_one, one_mul] using h.symm
  have hU' : U.invᴴ = U.val := by rw [← hU, conjTranspose_conjTranspose]
  let b := (matrixConjugation U).trans (reindexSL e)
  let F (X : Matrix ι ι ℂ) := Matrix.reindex e e (U.val * X * U.inv)
  change F A.val = signatureMatrix p q at hdiag
  have hb (X : SL ι) : (b X).val = F X.val := rfl
  have hF (X Y : Matrix ι ι ℂ) : F (X * Y) = F X * F Y := by
    change Matrix.reindexAlgEquiv ℂ ℂ e (U.val * (X * Y) * U.inv) =
      Matrix.reindexAlgEquiv ℂ ℂ e (U.val * X * U.inv) *
        Matrix.reindexAlgEquiv ℂ ℂ e (U.val * Y * U.inv)
    rw [← unit_conj_mul, map_mul]
  have hbAd (X : SL ι) :
      (b (matrixConjugation W X)).val = signatureMatrix p q * (b X).val * signatureMatrix p q := by
    rw [← hAd, hb, matrixConjugation_apply, hAinv, hF, hF, hdiag, hb]
  have hbω : Intertwines compactConjugation compactConjugation b := by
    intro X
    change compactConjugation.map (reindexSL e (matrixConjugation U X)) = _
    rw [reindexSL_intertwines e, matrixConjugation_comm U hU hU']
    rfl
  obtain ⟨ω', a', hc', hi', _, _, hτ, _, _⟩ := unitary_model p q
  refine ⟨p, q, _, b, hn, hτ, ?_⟩
  intro X
  apply Subtype.ext
  rw [hτ]
  change -(signatureMatrix p q * (b X).valᴴ * signatureMatrix p q) =
    (b (matrixConjugation W (compactConjugation.map X))).val
  rw [hbAd, ← hbω, compact_apply, Matrix.mul_neg, Matrix.neg_mul]

theorem outer_representative : outerRepresentativeType := by
  intro ι _ _ _ ω a hcomm hinv hω hAd
  obtain ⟨U, hU⟩ := hAd
  have ha : a = negativeTranspose.trans (matrixConjugation U) :=
    LieEquiv.ext fun X => Subtype.ext (hU X)
  subst a
  have hω' : ω = compactConjugation := by
    apply RealForms.Conjugation.ext_map
    ext X : 1
    exact Subtype.ext (hω X)
  subst ω
  obtain ⟨V, hV, hAd⟩ := compact_inner_unitary U (compact_outer_comm U hcomm)
  have hsign := outer_involution_transpose_sign V (hAd.symm ▸ hinv)
  exact ⟨V, hV, hsign, fun X => congrArg Subtype.val
    (congrArg (fun f : SL ι ≃ₗ⁅ℂ⁆ SL ι => f (negativeTranspose X)) hAd.symm)⟩

end CompactMatrixRepresentatives

theorem unitary_exchange : unitaryExchangeType := by
  intro p q σ τ hσ hτ
  let e : Blocks p q ≃ Blocks q p := Equiv.sumComm (Fin p) (Fin q)
  let R := Matrix.reindexAlgEquiv ℂ ℂ e
  have hD : R (signatureMatrix p q) = -signatureMatrix q p := by
    change Matrix.reindex e e (signatureMatrix p q) = -signatureMatrix q p
    unfold signatureMatrix LieAlgebra.Orthogonal.indefiniteDiagonal
    rw [Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv, diagonal_neg]
    congr 1
    funext i
    cases i <;> simp [e]
  have hstar (A : Matrix (Blocks p q) (Blocks p q) ℂ) : R Aᴴ = (R A)ᴴ := by
    change Matrix.reindex e e Aᴴ = (Matrix.reindex e e A)ᴴ
    rw [Matrix.reindex_apply, Matrix.reindex_apply, conjTranspose_submatrix]
  refine (RealForms.forms_isomorphic_iff σ τ).mpr ⟨reindexSL e, ?_⟩
  intro X
  apply Subtype.ext
  rw [hτ, reindexSL_apply, reindexSL_apply, hσ]
  change -(signatureMatrix q p * (R X.val)ᴴ * signatureMatrix q p) =
    R (-(signatureMatrix p q * X.valᴴ * signatureMatrix p q))
  rw [map_neg, map_mul, map_mul, hD, hstar, Matrix.neg_mul, neg_mul_neg]
section OuterMatrixNormalForms

open Module
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem normalize_antiunitary (J : E →ₛₗ[starRingEnd ℂ] E)
    {x : E} (hx : x ≠ 0) :
    let y := ((‖x‖⁻¹ : ℝ) : ℂ) • x
    ‖y‖ = 1 ∧ J y = ((‖x‖⁻¹ : ℝ) : ℂ) • J x := by
  dsimp only
  constructor
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
  · rw [map_smulₛₗ, Complex.conj_ofReal]

private theorem antiunitary_span {ι : Type*}
    (J : E →ₛₗ[starRingEnd ℂ] E) (v : ι → E)
    (hv : ∀ i, J (v i) ∈ Submodule.span ℂ (Set.range v)) :
    ∀ x ∈ Submodule.span ℂ (Set.range v), J x ∈ Submodule.span ℂ (Set.range v) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hv i
  | zero => simp
  | add x y hx hy h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | smul r x hx h₁ => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ h₁

private theorem antiunitary_orthogonal (J : E →ₛₗ[starRingEnd ℂ] E)
    (hJ : ∀ x y, ⟪J x, J y⟫_ℂ = ⟪y, x⟫_ℂ)
    (s : ℂ) (hs : s ≠ 0) (hJ2 : ∀ x, J (J x) = s • x)
    {V W : Submodule ℂ E}
    (hV : ∀ x ∈ V, J x ∈ V) (hW : ∀ x ∈ W, J x ∈ W) :
    ∀ x ∈ Vᗮ ⊓ W, J x ∈ Vᗮ ⊓ W := by
  intro x hx
  refine ⟨(V.mem_orthogonal _).mpr fun y hy => ?_, hW x hx.2⟩
  have h := hJ (J y) x
  rw [hJ2, inner_smul_left, V.inner_left_of_mem_orthogonal (hV y hy) hx.1] at h
  exact (mul_eq_zero.mp h).resolve_left (by simpa using hs)

private theorem orthonormal_append {ι κ : Type*} {v : ι → E} {w : κ → E}
    (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w)
    (h : ∀ i j, ⟪v i, w j⟫_ℂ = 0) :
    Orthonormal ℂ (Sum.elim v w) := by
  classical
  rw [orthonormal_iff_ite] at hv hw ⊢
  rintro (i | i) (j | j)
  · simpa using hv i j
  · simpa using h i j
  · simpa only [Sum.elim_inl, Sum.elim_inr, Sum.inr_ne_inl, ite_false] using
      (inner_eq_zero_symm.mp (h j i))
  · simpa using hw i j

private theorem antiunitary_fixed_vector (J : E →ₛₗ[starRingEnd ℂ] E)
    (hJ2 : ∀ x, J (J x) = x)
    (W : Submodule ℂ E) (hW : ∀ x ∈ W, J x ∈ W) (hbot : W ≠ ⊥) :
    ∃ v ∈ W, v ≠ 0 ∧ J v = v := by
  obtain ⟨x, hx, hxn⟩ := (W.ne_bot_iff).mp hbot
  by_cases h : x + J x = 0
  · have h' : J x = -x := by rwa [eq_neg_iff_add_eq_zero, add_comm]
    refine ⟨Complex.I • x, W.smul_mem _ hx, smul_ne_zero Complex.I_ne_zero hxn, ?_⟩
    rw [map_smulₛₗ, Complex.conj_I, h', neg_smul_neg]
  · exact ⟨x + J x, W.add_mem hx (hW x hx), h, by rw [map_add, hJ2, add_comm]⟩

/-- A complex antiunitary involution has an orthonormal family of fixed vectors
whose size is the complex dimension of the invariant subspace. -/
private theorem antiunitary_fixed_orthonormal [FiniteDimensional ℂ E]
    (J : E →ₛₗ[starRingEnd ℂ] E)
    (hJ : ∀ x y, ⟪J x, J y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hJ2 : ∀ x, J (J x) = x)
    (n : ℕ) (W : Submodule ℂ E) (hW : ∀ x ∈ W, J x ∈ W)
    (hn : finrank ℂ W = n) :
    ∃ v : Fin n → E, Orthonormal ℂ v ∧ ∀ i, v i ∈ W ∧ J (v i) = v i := by
  classical
  induction n generalizing W with
  | zero =>
    exact ⟨Fin.elim0, by rw [orthonormal_iff_ite]; intro i; exact i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    have hbot : W ≠ ⊥ := fun hw => by have h := (Submodule.finrank_eq_zero.mpr hw); omega
    obtain ⟨x, hx, hxn, hfix⟩ := antiunitary_fixed_vector J hJ2 W hW hbot
    let y := ((‖x‖⁻¹ : ℝ) : ℂ) • x
    obtain ⟨hyn, hJy⟩ := normalize_antiunitary J hxn
    change ‖y‖ = 1 at hyn
    have hy : y ∈ W := W.smul_mem _ hx
    have hJy's : J y = y := by simpa only [y, hfix] using hJy
    let v : Unit → E := fun _ => y
    have hv : Orthonormal ℂ v := by
      rw [orthonormal_subsingleton_iff]
      exact fun _ => hyn
    let V := Submodule.span ℂ (Set.range v)
    have hV : V ≤ W := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hy)
    have hVJ : ∀ x ∈ V, J x ∈ V := antiunitary_span J v fun i => by
      change J y ∈ V
      rw [hJy's]
      exact Submodule.subset_span ⟨i, rfl⟩
    let W' := Vᗮ ⊓ W
    have hn' : finrank ℂ W' = n := by
      have h := Submodule.finrank_add_inf_finrank_orthogonal hV
      have h₁ : finrank ℂ V = 1 := by simpa [V] using finrank_span_eq_card hv.linearIndependent
      change finrank ℂ (Vᗮ ⊓ W : Submodule ℂ E) = n
      omega
    have hW' : ∀ x ∈ W', J x ∈ W' :=
      antiunitary_orthogonal J hJ 1 one_ne_zero (by simpa only [one_smul] using hJ2) hVJ hW
    obtain ⟨w, hw, hw'⟩ := ih W' hW' hn'
    let u : Unit ⊕ Fin n → E := Sum.elim v w
    let e : Fin (n + 1) ≃ Unit ⊕ Fin n :=
      (finCongr (Nat.add_comm n 1)).trans ((finSumFinEquiv (m := 1) (n := n)).symm.trans
        (Equiv.sumCongr (Equiv.ofUnique _ _) (Equiv.refl _)))
    have hu : Orthonormal ℂ u :=
      orthonormal_append hv hw fun i j =>
        V.inner_right_of_mem_orthogonal (Submodule.subset_span ⟨i, rfl⟩) (hw' j).1.1
    refine ⟨u ∘ e, hu.comp _ e.injective, fun i => ?_⟩
    change u (e i) ∈ W ∧ J (u (e i)) = u (e i)
    rcases e i with j | j
    · exact ⟨hy, hJy's⟩
    · exact ⟨(hw' j).1.2, (hw' j).2⟩


/-- When the square is minus the identity, orthonormal vectors split into
pairs exchanged by the antiunitary map with the indicated signs. -/
private theorem antiunitary_paired_orthonormal [FiniteDimensional ℂ E]
    (J : E →ₛₗ[starRingEnd ℂ] E)
    (hJ : ∀ x y, ⟪J x, J y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hJ2 : ∀ x, J (J x) = -x)
    (n : ℕ) (W : Submodule ℂ E) (hW : ∀ x ∈ W, J x ∈ W)
    (hn : finrank ℂ W = n) :
    ∃ m : ℕ, n = m + m ∧
      ∃ v : Fin m ⊕ Fin m → E, Orthonormal ℂ v ∧ (∀ i, v i ∈ W) ∧
        ∀ i, J (v (Sum.inl i)) = v (Sum.inr i) ∧ J (v (Sum.inr i)) = -v (Sum.inl i) := by
  classical
  induction n using Nat.strong_induction_on generalizing W with
  | h n ih =>
    by_cases hn₀ : n = 0
    · subst n
      exact ⟨0, by simpa using hn₀, Sum.elim Fin.elim0 Fin.elim0, Orthonormal.of_isEmpty _,
        (by rintro (i | i) <;> exact i.elim0), fun i => i.elim0⟩
    have hbot : W ≠ ⊥ := fun hw => hn₀ (hn.symm.trans (Submodule.finrank_eq_zero.mpr hw))
    obtain ⟨x, hx, hxn⟩ := (W.ne_bot_iff).mp hbot
    let y := ((‖x‖⁻¹ : ℝ) : ℂ) • x
    have hyn : ‖y‖ = 1 := (normalize_antiunitary J hxn).1
    have hy : y ∈ W := W.smul_mem _ hx
    let z := J y
    have hz : z ∈ W := hW y hy
    have hjy : J y = z := rfl
    have hjz : J z = -y := hJ2 y
    have horth : ⟪y, z⟫_ℂ = 0 := by
      have h := hJ (J y) y
      rw [hJ2, inner_neg_left] at h
      exact neg_eq_self.mp h
    have hzn : ‖z‖ = 1 := by
      change ‖J y‖ = 1
      rw [@norm_eq_sqrt_re_inner ℂ, hJ, ← @norm_eq_sqrt_re_inner ℂ, hyn]
    let v : PUnit.{1} ⊕ PUnit.{1} → E := Sum.elim (fun _ => y) (fun _ => z)
    have hv : Orthonormal ℂ v :=
      orthonormal_append (orthonormal_subsingleton_iff.mpr fun _ => hyn)
        (orthonormal_subsingleton_iff.mpr fun _ => hzn) fun _ _ => horth
    let V := Submodule.span ℂ (Set.range v)
    have hvW (i) : v i ∈ W := by cases i <;> assumption
    have hV : V ≤ W := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hvW i)
    have hyV : y ∈ V := Submodule.subset_span ⟨Sum.inl PUnit.unit, rfl⟩
    have hzV : z ∈ V := Submodule.subset_span ⟨Sum.inr PUnit.unit, rfl⟩
    have hVJ : ∀ x ∈ V, J x ∈ V := antiunitary_span J v fun i => by
      cases i with
      | inl i => exact hzV
      | inr i =>
        change J z ∈ V
        rw [hjz]
        exact V.neg_mem hyV
    let W' := Vᗮ ⊓ W
    have hn' : 2 + finrank ℂ W' = n := by
      have h := Submodule.finrank_add_inf_finrank_orthogonal hV
      have h₂ : finrank ℂ V = 2 := by
        simpa [V, Fintype.card_sum] using finrank_span_eq_card hv.linearIndependent
      rw [h₂, hn] at h
      exact h
    have hW' : ∀ x ∈ W', J x ∈ W' :=
      antiunitary_orthogonal J hJ (-1) (by simp) (by simpa only [neg_smul, one_smul] using hJ2) hVJ hW
    obtain ⟨m, hm, w, hw, hwW, hwJ⟩ := ih _ (by omega) W' hW' rfl
    let u : (PUnit.{1} ⊕ PUnit.{1}) ⊕ (Fin m ⊕ Fin m) → E := Sum.elim v w
    have hu : Orthonormal ℂ u :=
      orthonormal_append hv hw fun i j =>
        V.inner_right_of_mem_orthogonal (Submodule.subset_span ⟨i, rfl⟩) (hwW j).1
    let e₁ : Fin (m + 1) ≃ PUnit.{1} ⊕ Fin m :=
      (finSuccEquiv m).trans ((Equiv.optionEquivSumPUnit _).trans (Equiv.sumComm _ _))
    let e := (Equiv.sumCongr e₁ e₁).trans (Equiv.sumSumSumComm PUnit.{1} (Fin m) PUnit.{1} (Fin m))
    have h₀l : e (Sum.inl 0) = Sum.inl (Sum.inl PUnit.unit) := by
      simp [e, e₁, Equiv.optionEquivSumPUnit, Equiv.sumSumSumComm]
    have h₀r : e (Sum.inr 0) = Sum.inl (Sum.inr PUnit.unit) := by
      simp [e, e₁, Equiv.optionEquivSumPUnit, Equiv.sumSumSumComm]
    have hsl (i : Fin m) : e (Sum.inl i.succ) = Sum.inr (Sum.inl i) := by
      simp [e, e₁, Equiv.optionEquivSumPUnit, Equiv.sumSumSumComm]
    have hsr (i : Fin m) : e (Sum.inr i.succ) = Sum.inr (Sum.inr i) := by
      simp [e, e₁, Equiv.optionEquivSumPUnit, Equiv.sumSumSumComm]
    refine ⟨m + 1, by omega, u ∘ e, hu.comp _ e.injective, ?_, ?_⟩
    · intro i
      change u (e i) ∈ W
      cases e i with
      | inl i => exact hvW i
      | inr i => exact (hwW i).2
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa only [Function.comp_apply, h₀l, h₀r, u, v, Sum.elim_inl, Sum.elim_inr] using And.intro hjy hjz
      · simpa only [Function.comp_apply, hsl, hsr, u, Sum.elim_inr] using hwJ i


section Matrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def matrixAntiunitary (A : Matrix ι ι ℂ) :
    EuclideanSpace ℂ ι →ₛₗ[starRingEnd ℂ] EuclideanSpace ℂ ι where
  toFun x := WithLp.toLp 2 (A *ᵥ fun i => star (x i))
  map_add' x y := by
    change WithLp.toLp 2 (A *ᵥ fun i => star (x i + y i)) =
      WithLp.toLp 2 ((A *ᵥ fun i => star (x i)) + (A *ᵥ fun i => star (y i)))
    rw [← Matrix.mulVec_add]
    congr 2
    funext i
    simp only [star_add, Pi.add_apply]
  map_smul' c x := by
    change WithLp.toLp 2 (A *ᵥ fun i => star (c * x i)) =
      WithLp.toLp 2 (star c • (A *ᵥ fun i => star (x i)))
    rw [← Matrix.mulVec_smul]
    congr 2
    funext i
    rw [star_mul']
    rfl

omit [DecidableEq ι] in
private theorem matrixAntiunitary_apply (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    (matrixAntiunitary A x).ofLp = A *ᵥ fun i => star (x i) := rfl

private theorem matrixAntiunitary_inner (A : Matrix ι ι ℂ) (hA : Aᴴ * A = 1)
    (x y : EuclideanSpace ℂ ι) :
    ⟪matrixAntiunitary A x, matrixAntiunitary A y⟫_ℂ = ⟪y, x⟫_ℂ := by
  simp only [PiLp.inner_apply, matrixAntiunitary_apply, RCLike.inner_apply]
  calc
    _ = star (A *ᵥ star x.ofLp) ⬝ᵥ (A *ᵥ star y.ofLp) :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    _ = _ := by
      rw [Matrix.star_mulVec, star_star, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        hA, Matrix.one_mulVec]
      rfl

omit [DecidableEq ι] in
private theorem conjugate_mulVec (A : Matrix ι ι ℂ) (x : ι → ℂ) :
    star (A *ᵥ x) = A.map (starRingEnd ℂ) *ᵥ star x := by
  funext i
  change (starRingEnd ℂ) (∑ j, A i j * x j) = ∑ j, star (A i j) * star (x j)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => map_mul (starRingEnd ℂ) (A i j) (x j))

private theorem matrixAntiunitary_squared (A : Matrix ι ι ℂ) (s : ℂ)
    (hs : A * A.map (starRingEnd ℂ) = s • 1) (x : EuclideanSpace ℂ ι) :
    matrixAntiunitary A (matrixAntiunitary A x) = s • x := by
  apply WithLp.ofLp_injective
  rw [matrixAntiunitary_apply]
  change A *ᵥ star (A *ᵥ star x.ofLp) = s • x.ofLp
  rw [conjugate_mulVec, star_star, Matrix.mulVec_mulVec, hs, Matrix.smul_mulVec, Matrix.one_mulVec]

private theorem orthonormal_columns (v : ι → EuclideanSpace ℂ ι) (hv : Orthonormal ℂ v) :
    let P : Matrix ι ι ℂ := Matrix.of (fun i j => v j i)
    Pᴴ * P = 1 := by
  dsimp only
  ext i j
  rw [Matrix.one_apply, ← orthonormal_iff_ite.mp hv i j, PiLp.inner_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.inner_apply]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

private theorem matrix_factor_of_columns (A B : Matrix ι ι ℂ)
    (v : ι → EuclideanSpace ℂ ι) (hv : Orthonormal ℂ v)
    (h : ∀ j, (matrixAntiunitary A (v j)).ofLp = (Matrix.of (fun i k => v k i)) *ᵥ B.col j) :
    ∃ P : (Matrix ι ι ℂ)ˣ, P.valᴴ = P.inv ∧ A = P.val * B * P.valᵀ := by
  let M : Matrix ι ι ℂ := Matrix.of (fun i j => v j i)
  let P := Unitary.toUnits ⟨M, Matrix.mem_unitaryGroup_iff'.mpr (orthonormal_columns v hv)⟩
  have hP : P.valᴴ = P.inv := rfl
  have hAB : A * M.map (starRingEnd ℂ) = M * B := by
    ext i j
    exact congrFun (h j) i
  have hMT : M.map (starRingEnd ℂ) * Mᵀ = 1 := by
    have ht := congrArg Matrix.transpose (show M * Mᴴ = 1 from P.val_inv)
    rw [Matrix.transpose_mul, Matrix.transpose_one] at ht
    exact ht
  refine ⟨P, hP, ?_⟩
  change A = M * B * Mᵀ
  rw [← hAB, Matrix.mul_assoc, hMT, Matrix.mul_one]

/-- A symmetric unitary matrix is unitarily congruent to the identity. -/
theorem unitary_symmetric_congruence (A : Matrix ι ι ℂ) (hA : Aᴴ * A = 1) (hs : Aᵀ = A) :
    ∃ P : (Matrix ι ι ℂ)ˣ, P.valᴴ = P.inv ∧ A = P.val * P.valᵀ := by
  let J := matrixAntiunitary A
  have hAstar : Aᴴ = A.map (starRingEnd ℂ) :=
    congrArg (·.map (starRingEnd ℂ)) hs
  have hAA : A * Aᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl ι)).mp hA
  have hj₂ (x) : J (J x) = x := by
    apply (matrixAntiunitary_squared A 1 ?_ x).trans (one_smul _ _)
    rw [one_smul, ← hAstar, hAA]
  obtain ⟨v, hv, hv'⟩ := antiunitary_fixed_orthonormal J (matrixAntiunitary_inner A hA) hj₂
    (Fintype.card ι) ⊤ (fun _ _ => Submodule.mem_top) (by simp)
  let v' : ι → EuclideanSpace ℂ ι := v ∘ Fintype.equivFin ι
  obtain ⟨P, hP, hAP⟩ := matrix_factor_of_columns A 1 v'
    (hv.comp _ (Fintype.equivFin ι).injective) (fun j => by
      have hfix : J (v' j) = v' j := (hv' _).2
      rw [show matrixAntiunitary A (v' j) = J (v' j) from rfl, hfix]
      change ((fun i => v' j i) : ι → ℂ) = Matrix.of (fun i k => v' k i) *ᵥ (1 : Matrix ι ι ℂ).col j
      rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, Matrix.mul_one, Matrix.mulVec_single_one]
      rfl)
  exact ⟨P, hP, by simpa only [Matrix.mul_one] using hAP⟩

/-- A skew-symmetric unitary matrix is unitarily congruent to the
standard symplectic matrix in coordinates of even size. -/
theorem unitary_skew_congruence (A : Matrix ι ι ℂ) (hA : Aᴴ * A = 1) (hs : Aᵀ = -A) :
    ∃ (m : ℕ) (e : ι ≃ Blocks m m) (P : (Matrix ι ι ℂ)ˣ),
      P.valᴴ = P.inv ∧ A = P.val * (Matrix.reindex e.symm e.symm (Matrix.J (Fin m) ℂ)) * P.valᵀ := by
  let J := matrixAntiunitary A
  have hAstar : Aᴴ = -(A.map (starRingEnd ℂ)) := by
    change Aᵀ.map (starRingEnd ℂ) = _
    rw [hs, Matrix.map_neg _ (map_neg (starRingEnd ℂ))]
  have hAA : A * Aᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl ι)).mp hA
  have hj₂ (x) : J (J x) = -x := by
    have h : A * A.map (starRingEnd ℂ) = (-1 : ℂ) • 1 := by
      rw [← neg_eq_iff_eq_neg.mpr hAstar, Matrix.mul_neg, hAA, neg_smul, one_smul]
    simpa only [neg_smul, one_smul] using matrixAntiunitary_squared A (-1) h x
  obtain ⟨m, hm, v, hv, -, hvJ⟩ := antiunitary_paired_orthonormal J
    (matrixAntiunitary_inner A hA) hj₂ (Fintype.card ι) ⊤ (fun _ _ => Submodule.mem_top) (by simp)
  let e : ι ≃ Blocks m m := Fintype.equivOfCardEq (by simpa [Fintype.card_sum] using hm)
  let B := Matrix.reindex e.symm e.symm (Matrix.J (Fin m) ℂ)
  let v' : ι → EuclideanSpace ℂ ι := v ∘ e
  let P₀ : Matrix ι ι ℂ := Matrix.of (fun i k => v' k i)
  have hc₁ (j : Fin m) : B.col (e.symm (Sum.inl j)) = Pi.single (e.symm (Sum.inr j)) 1 := by
    ext i
    change Matrix.J (Fin m) ℂ (e i) (e (e.symm (Sum.inl j))) =
      ((Pi.single (e.symm (Sum.inr j)) 1 : ι → ℂ) i)
    simp only [e.apply_symm_apply, Pi.single_apply, e.eq_symm_apply]
    cases e i <;> simp [Matrix.J, Matrix.one_apply]
  have hc₂ (j : Fin m) : B.col (e.symm (Sum.inr j)) = -(Pi.single (e.symm (Sum.inl j)) 1) := by
    ext i
    change Matrix.J (Fin m) ℂ (e i) (e (e.symm (Sum.inr j))) =
      -(((Pi.single (e.symm (Sum.inl j)) 1 : ι → ℂ) i))
    simp only [e.apply_symm_apply, Pi.single_apply, e.eq_symm_apply]
    cases e i <;> simp [Matrix.J, Matrix.one_apply]
  obtain ⟨P, hP, hAP⟩ := matrix_factor_of_columns A B v' (hv.comp _ e.injective) (fun j => by
    change (J (v (e j))).ofLp = P₀ *ᵥ B.col j
    obtain ⟨j, rfl⟩ := e.symm.surjective j
    rcases j with j | j
    · rw [e.apply_symm_apply, (hvJ j).1, hc₁, Matrix.mulVec_single_one]
      change (v (Sum.inr j)).ofLp = (v (e (e.symm (Sum.inr j)))).ofLp
      rw [e.apply_symm_apply]
    · rw [e.apply_symm_apply, (hvJ j).2, hc₂, Matrix.mulVec_neg, Matrix.mulVec_single_one]
      change -(v (Sum.inl j)).ofLp = -(v (e (e.symm (Sum.inl j)))).ofLp
      rw [e.apply_symm_apply])
  exact ⟨m, e, P, hP, hAP⟩

end Matrices

end OuterMatrixNormalForms

section MatrixTransport

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

private def conjugateUnit (U : (Matrix ι ι ℂ)ˣ) : (Matrix ι ι ℂ)ˣ :=
  ⟨bar U.val, bar U.inv,
    by rw [← bar_mul, U.val_inv]; exact Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _),
    by rw [← bar_mul, U.inv_val]; exact Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _)⟩

private theorem intertwines_of_conjugate_units
    (σ τ : Conjugation (SL ι)) (U V P : (Matrix ι ι ℂ)ˣ)
    (hσ : ∀ X, (σ.map X).val = U.val * bar X.val * U.inv)
    (hτ : ∀ X, (τ.map X).val = V.val * bar X.val * V.inv)
    (hP : U.val * bar P.val = P.val * V.val) :
    Intertwines τ σ (matrixConjugation P) := by
  have hEq : U * conjugateUnit P = P * V := Units.ext hP
  have hInv : bar P.inv * U.inv = V.inv * P.inv :=
    congrArg (fun W : (Matrix ι ι ℂ)ˣ => W.inv) hEq
  intro X
  apply Subtype.ext
  rw [hσ, matrixConjugation_apply, matrixConjugation_apply, hτ, bar_mul, bar_mul]
  calc
    U.val * (bar P.val * bar X.val * bar P.inv) * U.inv =
        (U.val * bar P.val) * bar X.val * (bar P.inv * U.inv) := by simp only [mul_assoc]
    _ = P.val * (V.val * bar X.val * V.inv) * P.inv := by rw [hP, hInv]; simp only [mul_assoc]

private theorem intertwines_inverse {σ : Conjugation (SL ι)} {τ : Conjugation (SL κ)}
    {a : SL ι ≃ₗ⁅ℂ⁆ SL κ} (h : Intertwines σ τ a) : Intertwines τ σ a.symm := by
  intro X
  apply a.injective
  change a (σ.map (a.symm X)) = a (a.symm (τ.map X))
  rw [a.apply_symm_apply, ← h, a.apply_symm_apply]

private theorem unitary_congruence_mul_bar
    (U V P : (Matrix ι ι ℂ)ˣ) (hP : P.valᴴ = P.inv)
    (hU : U.val = P.val * V.val * P.valᵀ) :
    U.val * bar P.val = P.val * V.val := by
  have hstar : bar P.valᴴ = P.valᵀ := by
    change (P.valᴴ)ᴴᵀ = P.valᵀ
    rw [conjTranspose_conjTranspose]
  have h : P.valᵀ * bar P.val = 1 := by
    calc
      _ = bar (P.valᴴ * P.val) := by rw [bar_mul, hstar]
      _ = 1 := by rw [hP, P.inv_val]; exact Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _)
  rw [hU, mul_assoc, h, mul_one]

private def splitConjugation : Conjugation (SL ι) :=
  involutionConjugation compactConjugation negativeTranspose negativeTranspose_comm
    negativeTranspose_involutive

private theorem split_reindex (e : ι ≃ κ) :
    Intertwines (splitConjugation : Conjugation (SL ι))
      (splitConjugation : Conjugation (SL κ)) (reindexSL e) := by
  intro X
  apply Subtype.ext
  have h (X : SL ι) : (splitConjugation.map X).val = bar X.val := split_apply X
  rw [show (splitConjugation.map (reindexSL e X)).val = bar (reindexSL e X).val from
    split_apply _, reindexSL_apply, reindexSL_apply, h]
  rfl

private theorem split_fixed_equiv (ι : Type) [Fintype ι] [DecidableEq ι] :
    Nonempty (LieAlgebra.SpecialLinear.sl ι ℝ ≃ₗ⁅ℝ⁆ (splitConjugation : Conjugation (SL ι)).fixed) := by
  obtain ⟨ω, a, hc, hi, _, _, hτ, ⟨e, _⟩, _⟩ := split_model ι
  have h : involutionConjugation ω a hc hi = splitConjugation := by
    apply Conjugation.ext_map
    ext X : 1
    exact Subtype.ext ((hτ X).trans (split_apply X).symm)
  exact h ▸ ⟨e⟩

private theorem quaternionic_fixed_equiv (m : ℕ) :
    Nonempty (quaternionicSL (Fin m) ≃ₗ⁅ℝ⁆ (quaternionicConjugation m).fixed) := by
  obtain ⟨ω, a, hc, hi, _, _, hτ, ⟨e, _⟩, _⟩ := quaternionic_model m
  have h : involutionConjugation ω a hc hi = quaternionicConjugation m := by
    apply Conjugation.ext_map
    ext X : 1
    exact Subtype.ext ((hτ X).trans (quaternionicConjugation_apply m X).symm)
  exact h ▸ ⟨e⟩

end MatrixTransport

private def splitRankOneChangeOfBasis : (Matrix (Blocks 1 1) (Blocks 1 1) ℂ)ˣ := by
  let P : Matrix (Blocks 1 1) (Blocks 1 1) ℂ := fun i j =>
    match i, j with
    | _, .inl _ => 1
    | .inl _, .inr _ => Complex.I
    | .inr _, .inr _ => -Complex.I
  let Q : Matrix (Blocks 1 1) (Blocks 1 1) ℂ := fun i j =>
    match i, j with
    | .inl _, _ => 1 / 2
    | .inr _, .inl _ => -(Complex.I / 2)
    | .inr _, .inr _ => Complex.I / 2
  refine ⟨P, Q, ?_, ?_⟩
  all_goals
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_one]
    cases i <;> cases j <;>
      simp [P, Q, Matrix.one_apply, Subsingleton.elim (_ : Fin 1) 0] <;>
      ring_nf <;> norm_num [Complex.I_sq]

private theorem splitRankOneChangeOfBasis_apply :
    (signatureUnit 1 1 * (symplecticUnit 1)⁻¹).val * bar splitRankOneChangeOfBasis.val =
      splitRankOneChangeOfBasis.val := by
  change (signatureMatrix 1 1 * (-Matrix.J (Fin 1) ℂ)) * bar splitRankOneChangeOfBasis.val = _
  rw [mul_assoc]
  ext i j
  cases i <;> cases j <;>
    simp [splitRankOneChangeOfBasis, signatureMatrix,
      LieAlgebra.Orthogonal.indefiniteDiagonal, Matrix.J, Matrix.fromBlocks, Matrix.diagonal_apply,
      Matrix.mul_apply, Fintype.sum_sum_type, bar, Matrix.map,
      Subsingleton.elim (_ : Fin 1) 0]

/-- The two noncompact labels in size two name the same real form. -/
theorem split_rank_one : splitRankOneType := by
  intro σ hσ
  let U := signatureUnit 1 1 * (symplecticUnit 1)⁻¹
  have hneg (X : SL (Blocks 1 1)) : matrixConjugation (symplecticUnit 1)⁻¹ X =
      negativeTranspose X := by
    apply (matrixConjugation (symplecticUnit 1)).injective
    change matrixConjugation (symplecticUnit 1) (matrixConjugation (symplecticUnit 1)⁻¹ X) =
      symplecticInvolution 1 X
    rw [← matrixConjugation_mul, mul_inv_cancel, symplecticInvolution_rank_one]
    apply Subtype.ext
    simp [matrixConjugation_apply]
  have hform (X : SL (Blocks 1 1)) : (σ.map X).val = U.val * bar X.val * U.inv := by
    have hnc : negativeTranspose (splitConjugation.map X) = compactConjugation.map X :=
      negativeTranspose_involutive _
    rw [← split_apply X]
    change (σ.map X).val = (matrixConjugation U (splitConjugation.map X)).val
    dsimp only [U]
    rw [matrixConjugation_mul, hneg, hnc, matrixConjugation_apply, compact_apply, hσ]
    change _ = signatureMatrix 1 1 * (-X.valᴴ) * signatureMatrix 1 1
    rw [Matrix.mul_neg, Matrix.neg_mul]
  have hs (X : SL (Blocks 1 1)) :
      ((splitConjugation : Conjugation (SL (Blocks 1 1))).map X).val =
        (1 : (Matrix (Blocks 1 1) (Blocks 1 1) ℂ)ˣ).val * bar X.val *
          (1 : (Matrix (Blocks 1 1) (Blocks 1 1) ℂ)ˣ).inv := by
    rw [show (splitConjugation.map X).val = bar X.val from split_apply X]
    simp
  have h := intertwines_of_conjugate_units σ splitConjugation U 1 splitRankOneChangeOfBasis
    hform hs (by rw [Units.val_one, mul_one]; exact splitRankOneChangeOfBasis_apply)
  let e : Blocks 1 1 ≃ Fin 2 := (Fintype.equivFin _).trans (finCongr (by simp))
  obtain ⟨es⟩ := (forms_isomorphic_iff _ _).2 ⟨_, intertwines_inverse h⟩
  obtain ⟨er⟩ := (forms_isomorphic_iff _ _).2 ⟨_, split_reindex e⟩
  obtain ⟨ef⟩ := split_fixed_equiv (Fin 2)
  exact ⟨es.trans (er.trans ef.symm)⟩

theorem symmetric_congruence : symmetricCongruenceType :=
  fun _ _ _ => unitary_symmetric_congruence

theorem skew_congruence : skewCongruenceType :=
  fun _ _ _ => unitary_skew_congruence

theorem outer_case : outerCaseType := by
  intro ι _ _ _ ω a hc hi hω hmat
  let σ := involutionConjugation ω a hc hi
  obtain ⟨U, hU, hsign, ha⟩ := outer_representative ι ω a hc hi hω hmat
  have hσ (X : SL ι) : (σ.map X).val = U.val * bar X.val * U.inv := by
    change (a (ω.map X)).val = _
    rw [ha, hω, transpose_neg, neg_neg, transpose_adjoint]
  have hGram : U.valᴴ * U.val = 1 := by rw [hU, U.inv_val]
  rcases hsign with hsym | hskew
  · obtain ⟨P, hP, hA⟩ := symmetric_congruence ι U.val hGram hsym
    have hτ (X : SL ι) : (splitConjugation.map X).val =
        (1 : (Matrix ι ι ℂ)ˣ).val * bar X.val * (1 : (Matrix ι ι ℂ)ˣ).inv := by
      rw [show (splitConjugation.map X).val = bar X.val from split_apply X]
      simp
    have hP' : U.val * bar P.val = P.val * (1 : (Matrix ι ι ℂ)ˣ).val :=
      unitary_congruence_mul_bar U 1 P hP (by simpa using hA)
    have h := intertwines_of_conjugate_units σ splitConjugation U 1 P hσ hτ hP'
    obtain ⟨es⟩ := (forms_isomorphic_iff _ _).2 ⟨_, intertwines_inverse h⟩
    obtain ⟨ef⟩ := split_fixed_equiv ι
    exact Or.inl ⟨es.trans ef.symm⟩
  · obtain ⟨m, e, P, hP, hA⟩ := skew_congruence ι U.val hGram hskew
    let b := reindexSL e
    let τ := (quaternionicConjugation m).transport b.symm
    let V := Units.map (Matrix.reindexAlgEquiv ℂ ℂ e.symm).toRingEquiv.toMonoidHom (symplecticUnit m)
    have hτ (X : SL ι) : (τ.map X).val = V.val * bar X.val * V.inv := by
      let R := Matrix.reindexAlgEquiv ℂ ℂ e.symm
      change (b.symm ((quaternionicConjugation m).map (b X))).val = _
      have hb : b.symm = reindexSL e.symm := by
        apply LieEquiv.ext
        intro Y
        apply b.injective
        change b (b.symm Y) = b (reindexSL e.symm Y)
        rw [b.apply_symm_apply]
        apply Subtype.ext
        change Y.val = (Matrix.reindexAlgEquiv ℂ ℂ e)
          ((Matrix.reindexAlgEquiv ℂ ℂ e).symm Y.val)
        rw [AlgEquiv.apply_symm_apply]
      rw [hb, reindexSL_apply, quaternionicConjugation_apply]
      change R (-(Matrix.J (Fin m) ℂ * bar (reindexSL e X).val * Matrix.J (Fin m) ℂ)) =
        R (Matrix.J (Fin m) ℂ) * bar X.val * R (-Matrix.J (Fin m) ℂ)
      have hbar : R (bar (reindexSL e X).val) = bar X.val := by
        change bar (R ((Matrix.reindexAlgEquiv ℂ ℂ e) X.val)) = bar X.val
        dsimp only [R]
        rw [← Matrix.symm_reindexAlgEquiv, AlgEquiv.symm_apply_apply]
      rw [map_neg, map_mul, map_mul, hbar, map_neg, Matrix.mul_neg]
    have hP' := unitary_congruence_mul_bar U V P hP hA
    have h := intertwines_of_conjugate_units σ τ U V P hσ hτ hP'
    have ht : Intertwines τ (quaternionicConjugation m) b := by
      intro X
      change (quaternionicConjugation m).map (b X) =
        b (b.symm ((quaternionicConjugation m).map (b X)))
      rw [b.apply_symm_apply]
    obtain ⟨es⟩ := (forms_isomorphic_iff _ _).2 ⟨_, intertwines_inverse h⟩
    obtain ⟨er⟩ := (forms_isomorphic_iff _ _).2 ⟨_, ht⟩
    obtain ⟨ef⟩ := quaternionic_fixed_equiv m
    refine Or.inr ⟨m, ?_, ⟨es.trans (er.trans ef.symm)⟩⟩
    simpa [two_mul] using Fintype.card_congr e

section MatrixAutomorphisms

private theorem common_endpoint {α β : Type*} [Nonempty α] (u v : α → β)
    (h : ∀ i j, u i = u j ∨ v i = v j) :
    (∃ a, ∀ i, u i = a) ∨ (∃ b, ∀ i, v i = b) := by
  classical
  let i : α := Classical.arbitrary α
  by_cases hu : ∀ j, u j = u i
  · exact Or.inl ⟨u i, hu⟩
  · push Not at hu
    obtain ⟨j, hj⟩ := hu
    refine Or.inr ⟨v i, fun k => ?_⟩
    by_cases hk : u k = u i
    · exact ((h k j).resolve_left (fun e => hj (e.symm.trans hk))).trans
        ((h j i).resolve_left hj)
    · exact (h k i).resolve_left hk

private def permutationMatrixUnit (p : Equiv.Perm ι) : (Matrix ι ι ℂ)ˣ where
  val := (p⁻¹).permMatrix ℂ
  inv := p.permMatrix ℂ
  val_inv := by
    change (p⁻¹).permMatrix ℂ * p.permMatrix ℂ = 1
    rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
  inv_val := by
    change p.permMatrix ℂ * (p⁻¹).permMatrix ℂ = 1
    rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

private theorem perm_conj (p : Equiv.Perm ι) (A : Matrix ι ι ℂ) :
    (permutationMatrixUnit p).val * A * (permutationMatrixUnit p).inv =
      Matrix.reindex p p A := by
  ext i j
  change ((p⁻¹).permMatrix ℂ * A * p.permMatrix ℂ) i j =
    A (p.symm i) (p.symm j)
  have left (j : ι) : ((p⁻¹).permMatrix ℂ * A) i j = A (p.symm i) j :=
    congrFun (Matrix.permMatrix_mulVec (σ := p⁻¹) (v := fun k => A k j)) i
  calc
    ((p⁻¹).permMatrix ℂ * A * p.permMatrix ℂ) i j =
      ((p⁻¹).permMatrix ℂ * A) i (p.symm j) :=
        congrFun (Matrix.vecMul_permMatrix (σ := p)
          (v := fun k => ((p⁻¹).permMatrix ℂ * A) i k)) j
    _ = _ := left _

private def diagonalMatrixUnit (d : ι → ℂ) (hd : ∀ i, d i ≠ 0) :
    (Matrix ι ι ℂ)ˣ where
  val := diagonal d
  inv := diagonal fun i => (d i)⁻¹
  val_inv := by simp [Matrix.diagonal_mul_diagonal, hd]
  inv_val := by simp [Matrix.diagonal_mul_diagonal, hd]

private theorem diag_conj_single (d : ι → ℂ) (hd : ∀ i, d i ≠ 0) (i j : ι) :
    (diagonalMatrixUnit d hd).val * Matrix.single i j 1 * (diagonalMatrixUnit d hd).inv =
      (d i * (d j)⁻¹) • Matrix.single i j 1 := by
  ext a b
  change (diagonal d * Matrix.single i j 1 * diagonal (fun k => (d k)⁻¹) : Matrix ι ι ℂ) a b =
    (d i * (d j)⁻¹) * Matrix.single i j 1 a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases ha : i = a <;> by_cases hb : j = b <;>
    simp_all

private def offDiagonal (i j : ι) (h : i ≠ j) : SL ι :=
  LieAlgebra.SpecialLinear.single i j h 1

private theorem bracket_offDiagonal (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⁅offDiagonal i j hij, offDiagonal j k hjk⁆ = offDiagonal i k hik := by
  apply Subtype.ext
  change (Matrix.single i j 1 * Matrix.single j k 1 -
    Matrix.single j k 1 * Matrix.single i j 1 : Matrix ι ι ℂ) = Matrix.single i k 1
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hik.symm]
  simp

private theorem bracket_offDiagonal_zero (a b c d : ι) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (hbd : b ≠ d) :
    ⁅offDiagonal a b hab, offDiagonal d c hcd.symm⁆ = 0 := by
  apply Subtype.ext
  change (Matrix.single a b 1 * Matrix.single d c 1 -
    Matrix.single d c 1 * Matrix.single a b 1 : Matrix ι ι ℂ) = 0
  rw [Matrix.single_mul_single_of_ne _ _ _ _ hbd,
    Matrix.single_mul_single_of_ne _ _ _ _ hac.symm, sub_zero]

private theorem bracket_opposite_offDiagonal (i j : ι) (hij : i ≠ j) :
    ⁅offDiagonal i j hij, offDiagonal j i hij.symm⁆ =
      LieAlgebra.SpecialLinear.singleSubSingle i j 1 := by
  apply Subtype.ext
  change (Matrix.single i j 1 * Matrix.single j i 1 -
    Matrix.single j i 1 * Matrix.single i j 1 : Matrix ι ι ℂ) =
      Matrix.single i i 1 - Matrix.single j j 1
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, one_mul]

private theorem offDiagonal_ne_zero (i j : ι) (hij : i ≠ j) : offDiagonal i j hij ≠ 0 := by
  intro h
  have h' := congrArg (fun X : SL ι => X.val i j) h
  simp [offDiagonal] at h'

private theorem values_on_offDiagonal (o : ι) (f g : SL ι ≃ₗ⁅ℂ⁆ SL ι)
    (hout : ∀ i (hi : i ≠ o), f (offDiagonal i o hi) = g (offDiagonal i o hi))
    (hin : ∀ i (hi : i ≠ o), f (offDiagonal o i hi.symm) = g (offDiagonal o i hi.symm)) :
    ∀ i j (hij : i ≠ j), f (offDiagonal i j hij) = g (offDiagonal i j hij) := by
  intro i j hij
  by_cases hi : i = o
  · subst i
    exact hin j hij.symm
  by_cases hj : j = o
  · subst j
    exact hout i hij
  rw [← bracket_offDiagonal i o j hi (Ne.symm hj) hij, f.map_lie, g.map_lie, hout i hi, hin j hj]

private theorem diagonal_sum_coroots (X : SL ι) (o : ι) :
    (∑ i, (LieAlgebra.SpecialLinear.singleSubSingle i o (X.val i i)).val) =
      diagonal (diag X.val) := by
  simp only [LieAlgebra.SpecialLinear.val_singleSubSingle, Finset.sum_sub_distrib]
  rw [Matrix.sum_single_eq_diagonal]
  change diagonal (diag X.val) - ∑ i, (Matrix.singleLinearMap ℂ o o) (X.val i i) = _
  rw [← map_sum]
  change diagonal (diag X.val) - Matrix.single o o (∑ i, X.val i i) = _
  have htrace : (∑ i, X.val i i) = 0 := X.property
  rw [htrace, Matrix.single_zero, sub_zero]

private theorem off_diag_decomposition (X : SL ι) (o : ι) :
    X = (∑ i, LieAlgebra.SpecialLinear.singleSubSingle i o (X.val i i)) +
        ∑ i, ∑ j, if hij : i ≠ j then X.val i j • offDiagonal i j hij else 0 := by
  apply Subtype.ext
  change X.val = (LieAlgebra.SpecialLinear.sl ι ℂ).incl
    ((∑ i, LieAlgebra.SpecialLinear.singleSubSingle i o (X.val i i)) +
        ∑ i, ∑ j, if hij : i ≠ j then X.val i j • offDiagonal i j hij else 0)
  simp only [map_add, map_sum]
  change X.val = (∑ i, (LieAlgebra.SpecialLinear.singleSubSingle i o (X.val i i)).val) +
        ∑ i, ∑ j, (if hij : i ≠ j then X.val i j • offDiagonal i j hij else 0).val
  rw [diagonal_sum_coroots]
  have he (i j a b : ι) :
      (if hij : i ≠ j then X.val i j • offDiagonal i j hij else 0).val a b =
        if i = a ∧ j = b ∧ i ≠ j then X.val i j else 0 := by
    by_cases hij : i ≠ j
    · rw [dite_eq_left hij]
      change X.val i j * Matrix.single i j 1 a b = _
      by_cases hia : i = a <;> by_cases hjb : j = b <;>
        simp_all
    · rw [dite_eq_right hij]
      simp [hij]
  ext a b
  simp only [Matrix.add_apply, Matrix.sum_apply, he]
  by_cases hab : a = b
  · subst b
    simp [ite_and]
  · simp [ite_and, hab]

private theorem eq_of_on_rays (o : ι) (f g : SL ι ≃ₗ⁅ℂ⁆ SL ι)
    (hout : ∀ i (hi : i ≠ o), f (offDiagonal i o hi) = g (offDiagonal i o hi))
    (hin : ∀ i (hi : i ≠ o), f (offDiagonal o i hi.symm) = g (offDiagonal o i hi.symm)) :
    f = g := by
  apply LieEquiv.ext
  intro X
  rw [off_diag_decomposition X o]
  simp only [map_add, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ≠ o
    · have h := bracket_opposite_offDiagonal i o hi
      rw [show LieAlgebra.SpecialLinear.singleSubSingle i o (X.val i i) =
        X.val i i • LieAlgebra.SpecialLinear.singleSubSingle i o (1 : ℂ) by
          rw [← map_smul, smul_eq_mul, mul_one],
        map_smul, map_smul, ← h, f.map_lie, g.map_lie,
        hout i hi, hin i hi]
    · have he : i = o := not_ne_iff.mp hi
      subst i
      have hz : LieAlgebra.SpecialLinear.singleSubSingle o o (X.val o o) = 0 := by
        apply Subtype.ext
        simp
      simp [hz]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hij
    · simp only [map_smul, values_on_offDiagonal o f g hout hin i j hij]
    · simp

private theorem monomial_conj_offDiagonal (p : Equiv.Perm ι) (d : ι → ℂ)
    (hd : ∀ i, d i ≠ 0) (i j : ι) (hij : i ≠ j) :
    matrixConjugation (permutationMatrixUnit p * diagonalMatrixUnit d hd) (offDiagonal i j hij) =
      (d i * (d j)⁻¹) • offDiagonal (p i) (p j) (p.injective.ne hij) := by
  apply Subtype.ext
  change ((permutationMatrixUnit p).val * (diagonalMatrixUnit d hd).val) *
      Matrix.single i j 1 * ((diagonalMatrixUnit d hd).inv * (permutationMatrixUnit p).inv) =
    (d i * (d j)⁻¹) • Matrix.single (p i) (p j) 1
  rw [show ((permutationMatrixUnit p).val * (diagonalMatrixUnit d hd).val) *
      Matrix.single i j (1 : ℂ) * ((diagonalMatrixUnit d hd).inv * (permutationMatrixUnit p).inv) =
      (permutationMatrixUnit p).val *
        ((diagonalMatrixUnit d hd).val * Matrix.single i j 1 * (diagonalMatrixUnit d hd).inv) *
        (permutationMatrixUnit p).inv by simp [mul_assoc],
    diag_conj_single, Matrix.mul_smul, Matrix.smul_mul, perm_conj]
  congr 1
  exact Matrix.submatrix_single_equiv p.symm p.symm i j 1

private theorem matrix_of_rays (o : ι) (g : SL ι ≃ₗ⁅ℂ⁆ SL ι) (p : Equiv.Perm ι)
    (c : {i : ι // i ≠ o} → ℂ) (hc : ∀ i, c i ≠ 0)
    (hout : ∀ i (hi : i ≠ o), g (offDiagonal i o hi) =
      c ⟨i, hi⟩ • offDiagonal (p i) (p o) (p.injective.ne hi))
    (hin : ∀ i (hi : i ≠ o), g (offDiagonal o i hi.symm) =
      (c ⟨i, hi⟩)⁻¹ • offDiagonal (p o) (p i) (p.injective.ne hi.symm)) :
    ∃ U : (Matrix ι ι ℂ)ˣ, g = matrixConjugation U := by
  let d (i : ι) := if hi : i ≠ o then c ⟨i, hi⟩ else 1
  have hdo : d o = 1 := by simp [d]
  have hdi (i : ι) (hi : i ≠ o) : d i = c ⟨i, hi⟩ := by simp [d, hi]
  have hd (i : ι) : d i ≠ 0 := by
    by_cases hi : i ≠ o
    · exact (hdi i hi).symm ▸ hc ⟨i, hi⟩
    · have hio : i = o := not_ne_iff.mp hi
      subst i
      exact hdo.symm ▸ one_ne_zero
  refine ⟨permutationMatrixUnit p * diagonalMatrixUnit d hd, ?_⟩
  apply eq_of_on_rays o
  · intro i hi
    rw [hout i hi, monomial_conj_offDiagonal, hdo, hdi i hi, inv_one, mul_one]
  · intro i hi
    rw [hin i hi, monomial_conj_offDiagonal, hdo, hdi i hi, one_mul]

private theorem complete_permutation (o b : ι) (f : {i : ι // i ≠ o} → ι)
    (hf : Function.Injective f) (hb : ∀ i, f i ≠ b) :
    ∃ p : Equiv.Perm ι, p o = b ∧ ∀ i, p i.val = f i := by
  let p (i : ι) := if hi : i ≠ o then f ⟨i, hi⟩ else b
  have hpo : p o = b := by simp [p]
  have hpf (i : {i : ι // i ≠ o}) : p i.val = f i := by simp [p, i.property]
  have hp : Function.Injective p := by
    intro i j hij
    by_cases hi : i ≠ o
    · by_cases hj : j ≠ o
      · exact congrArg Subtype.val (hf ((hpf ⟨i, hi⟩).symm.trans (hij.trans (hpf ⟨j, hj⟩))))
      · have hjo : j = o := not_ne_iff.mp hj
        subst j
        exact (hb ⟨i, hi⟩ ((hpf ⟨i, hi⟩).symm.trans (hij.trans hpo))).elim
    · have hio : i = o := not_ne_iff.mp hi
      subst i
      by_cases hj : j ≠ o
      · exact (hb ⟨j, hj⟩ ((hpf ⟨j, hj⟩).symm.trans (hij.symm.trans hpo))).elim
      · exact (not_ne_iff.mp hj).symm
  exact ⟨Equiv.ofBijective p ⟨hp, Finite.injective_iff_surjective.mp hp⟩, hpo, hpf⟩
section CartanNormalizer

open Specs.LieAlgebrasAndRepresentations.ClassicalRootsA (cartan root rootVector)
open LieAlgebrasAndRepresentations.ClassicalRootsA
open private rootTransport rootTransport_mem rootSpace_map_transport
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition

variable {n : ℕ}
local notation "I" => Fin (n + 1)

private theorem root_neg (i j : I) : root n j i = -root n i j := by
  ext h
  simp [sub_eq_neg_add]

private theorem normalizer_root_pair (g : SL I ≃ₗ⁅ℂ⁆ SL I)
    (hg : (cartan n).map g.toLieHom = cartan n) (i j : I) (hij : i ≠ j) :
    ∃ (a b : I) (hab : a ≠ b) (c d : ℂ),
      rootTransport g hg (root n i j) = root n a b ∧
      c ≠ 0 ∧ d = c⁻¹ ∧
      g (offDiagonal i j hij) = c • offDiagonal a b hab ∧
      g (offDiagonal j i hij.symm) = d • offDiagonal b a hab.symm := by
  have ht := (rootTransport_mem g hg (root n i j)).2
    ((root_set n (root n i j)).2 ⟨i, j, hij, rfl⟩)
  obtain ⟨a, b, hab, ht⟩ := (root_set n _).1 ht
  have ht' : rootTransport g hg (root n j i) = root n b a := by
    rw [root_neg i j, map_neg, ht, ← root_neg a b]
  have hE (u v r s : I) (huv : u ≠ v) (hrs : r ≠ s)
      (htuv : rootTransport g hg (root n u v) = root n r s) :
      g (offDiagonal u v huv) ∈ ℂ ∙ offDiagonal r s hrs := by
    change g (rootVector n u v huv) ∈ ℂ ∙ rootVector n r s hrs
    rw [← root_space n r s hrs, ← htuv, ← rootSpace_map_transport]
    exact ⟨rootVector n u v huv, rootVector_mem u v huv, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hE i j a b hij hab ht)
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hE j i b a hij.symm hab.symm ht')
  have hcn : c ≠ 0 := by
    intro hc0
    have := hc
    rw [hc0, zero_smul, eq_comm, map_eq_zero_iff g g.injective] at this
    exact offDiagonal_ne_zero i j hij this
  have htri (u v : I) (huv : u ≠ v) :
      ⁅⁅offDiagonal u v huv, offDiagonal v u huv.symm⁆, offDiagonal u v huv⁆ =
        (2 : ℂ) • offDiagonal u v huv := by
    have h := root_triple n u v huv
    change ⁅⁅rootVector n u v huv, rootVector n v u huv.symm⁆, rootVector n u v huv⁆ = _
    rw [h.1]
    exact h.2.1
  have hv := congrArg g (htri i j hij)
  rw [g.map_lie, g.map_lie, map_smul, ← hc, ← hd] at hv
  simp only [smul_lie, lie_smul, htri, smul_smul] at hv
  have hcd : c * d = 1 := by
    have heq := (smul_left_injective ℂ (offDiagonal_ne_zero a b hab)) hv
    have heq' : d * (c * c * 2) = c * 2 := by linear_combination heq
    have hcancel : c * 2 ≠ 0 := mul_ne_zero hcn (by norm_num)
    apply mul_right_cancel₀ hcancel
    linear_combination heq'
  have hd' : d = c⁻¹ := by
    apply mul_left_cancel₀ hcn
    rw [hcd, mul_inv_cancel₀ hcn]
  exact ⟨a, b, hab, c, d, ht, hcn, hd', hc.symm, hd.symm⟩

private theorem negateTranspose_offDiagonal (i j : ι) (hij : i ≠ j) :
    negativeTranspose (offDiagonal i j hij) = -offDiagonal j i hij.symm := by
  apply Subtype.ext
  change -(Matrix.single i j (1 : ℂ)).transpose = -Matrix.single j i 1
  rw [Matrix.transpose_single]

private theorem normalizer_matrix_forms (hn : 1 ≤ n) (g : SL I ≃ₗ⁅ℂ⁆ SL I)
    (hg : (cartan n).map g.toLieHom = cartan n) :
    (∃ U, g = matrixConjugation U) ∨
      (∃ U, g = negativeTranspose.trans (matrixConjugation U)) := by
  classical
  let o : I := 0
  let K := {i : I // i ≠ o}
  have : Nonempty K := ⟨⟨⟨1, by omega⟩, fun h => by cases congrArg Fin.val h⟩⟩
  choose a b hab c d ht hc hd hout hin using
    (fun i : K => normalizer_root_pair g hg i.val o i.property)
  have halign (i j : K) : a i = a j ∨ b i = b j := by
    by_cases h : i = j
    · exact Or.inl (congrArg a h)
    · by_contra! hn'
      have hij : i.val ≠ j.val := by intro he; exact h (Subtype.ext he)
      have hz := bracket_offDiagonal_zero (a i) (b i) (a j) (b j) (hab i) (hab j) hn'.1 hn'.2
      have hv := g.map_lie (offDiagonal i.val o i.property)
        (offDiagonal o j.val j.property.symm)
      rw [bracket_offDiagonal _ _ _ _ _ hij, hout i, hin j, smul_lie, lie_smul, hz,
        smul_zero, smul_zero, map_eq_zero_iff g g.injective] at hv
      exact offDiagonal_ne_zero _ _ hij hv
  have hinj (i j : K) (h₁ : a i = a j) (h₂ : b i = b j) : i = j := by
    have he := (rootTransport g hg).injective (by rw [ht i, ht j, h₁, h₂] :
      rootTransport g hg (root n i.val o) = rootTransport g hg (root n j.val o))
    exact Subtype.ext ((root_injective i.val o j.val o i.property j.property he).1)
  rcases common_endpoint a b halign with ⟨l, ha⟩ | ⟨r, hb⟩
  · right
    obtain ⟨p, ho, hp⟩ := complete_permutation o l b
      (fun {i j} h => hinj i j ((ha i).trans (ha j).symm) h)
      (fun i h => (hab i).symm (h.trans (ha i).symm))
    have hcl (i : K) : -d i ≠ 0 := by rw [hd i]; exact neg_ne_zero.mpr (inv_ne_zero (hc i))
    have hdiag := matrix_of_rays o (negativeTranspose.trans g) p (fun i => -d i) hcl
    obtain ⟨U, hU⟩ := hdiag (by
      intro i hi
      rw [LieEquiv.trans_apply, negateTranspose_offDiagonal, map_neg, hin ⟨i, hi⟩,
        ← neg_smul]
      congr 1
      apply Subtype.ext
      change Matrix.single (b ⟨i, hi⟩) (a ⟨i, hi⟩) (1 : ℂ) =
        Matrix.single (p i) (p o) 1
      rw [hp ⟨i, hi⟩, ho, ha ⟨i, hi⟩]) (by
      intro i hi
      rw [LieEquiv.trans_apply, negateTranspose_offDiagonal, map_neg, hout ⟨i, hi⟩,
        ← neg_smul, hd ⟨i, hi⟩, inv_neg, inv_inv]
      congr 1
      apply Subtype.ext
      change Matrix.single (a ⟨i, hi⟩) (b ⟨i, hi⟩) (1 : ℂ) =
        Matrix.single (p o) (p i) 1
      rw [hp ⟨i, hi⟩, ho, ha ⟨i, hi⟩])
    refine ⟨U, LieEquiv.ext fun X => ?_⟩
    have hX := DFunLike.congr_fun hU (negativeTranspose X)
    rwa [LieEquiv.trans_apply, negativeTranspose_involutive] at hX
  · left
    obtain ⟨p, ho, hp⟩ := complete_permutation o r a
      (fun {i j} h => hinj i j h ((hb i).trans (hb j).symm))
      (fun i h => hab i (h.trans (hb i).symm))
    apply matrix_of_rays o g p c hc
    · intro i hi
      rw [hout ⟨i, hi⟩]
      congr 1
      apply Subtype.ext
      change Matrix.single (a ⟨i, hi⟩) (b ⟨i, hi⟩) (1 : ℂ) =
        Matrix.single (p i) (p o) 1
      rw [hp ⟨i, hi⟩, ho, hb ⟨i, hi⟩]
    · intro i hi
      rw [hin ⟨i, hi⟩, hd ⟨i, hi⟩]
      congr 1
      apply Subtype.ext
      change Matrix.single (b ⟨i, hi⟩) (a ⟨i, hi⟩) (1 : ℂ) =
        Matrix.single (p o) (p i) 1
      rw [hp ⟨i, hi⟩, ho, hb ⟨i, hi⟩]

end CartanNormalizer

end MatrixAutomorphisms

section MatrixAutomorphismAssembly

open Specs.LieAlgebrasAndRepresentations.ClassicalRootsA (cartan)
open private inner_module_intertwiner cartan_map
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition

local notation "StdVec" => (ι → ℂ)

private def standardMatrixRepresentation : SL ι →ₗ⁅ℂ⁆ Module.End ℂ StdVec :=
  (lieEquivMatrix' (R := ℂ) (n := ι)).symm.toLieHom.comp
    (LieAlgebra.SpecialLinear.sl ι ℂ).incl

private def endomorphismMatrixUnit (e : StdVec ≃ₗ[ℂ] StdVec) : (Matrix ι ι ℂ)ˣ where
  val := e.toLinearMap.toMatrix'
  inv := e.symm.toLinearMap.toMatrix'
  val_inv := by
    rw [← LinearMap.toMatrix'_mul, show e.toLinearMap * e.symm.toLinearMap = 1 by ext v i; simp,
      LinearMap.toMatrix'_one]
  inv_val := by
    rw [← LinearMap.toMatrix'_mul, show e.symm.toLinearMap * e.toLinearMap = 1 by ext v i; simp,
      LinearMap.toMatrix'_one]

private theorem matrix_of_standard_intertwiner (g : SL ι ≃ₗ⁅ℂ⁆ SL ι)
    (T : StdVec ≃ₗ[ℂ] StdVec)
    (hT : ∀ X v, T (standardMatrixRepresentation X v) = standardMatrixRepresentation (g X) (T v)) :
    ∃ U : (Matrix ι ι ℂ)ˣ, ∀ X, (g X).val = U.val * X.val * U.inv := by
  refine ⟨endomorphismMatrixUnit T, fun X => ?_⟩
  have he : standardMatrixRepresentation (g X) =
      T.toLinearMap * standardMatrixRepresentation X * T.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    have h := hT X (T.symm v)
    simpa using h.symm
  have h := congrArg LinearMap.toMatrix' he
  change (toLin' (g X).val).toMatrix' =
      (T.toLinearMap * toLin' X.val * T.symm.toLinearMap).toMatrix' at h
  simpa [endomorphismMatrixUnit, LinearMap.toMatrix'_mul] using h
private theorem matrixConjugation_inverse (U : (Matrix ι ι ℂ)ˣ) :
    (matrixConjugation U).symm = matrixConjugation U⁻¹ := by
  apply LieEquiv.ext
  intro X
  apply (matrixConjugation U).injective
  change matrixConjugation U ((matrixConjugation U).symm X) =
    matrixConjugation U (matrixConjugation U⁻¹ X)
  rw [LieEquiv.apply_symm_apply, ← matrixConjugation_mul, mul_inv_cancel]
  apply Subtype.ext
  simp [matrixConjugation_apply]


private theorem inner_automorphism_matrix (g : SL ι ≃ₗ⁅ℂ⁆ SL ι)
    (hg : CartanConjugacy.IsInner g) :
    ∃ U : (Matrix ι ι ℂ)ˣ, g = matrixConjugation U := by
  let : LieRingModule (SL ι) StdVec := LieRingModule.compLieHom StdVec standardMatrixRepresentation
  let : LieModule ℂ (SL ι) StdVec := LieModule.compLieHom StdVec standardMatrixRepresentation
  obtain ⟨T, hT⟩ := inner_module_intertwiner (V := StdVec) g.toLinearEquiv hg
  obtain ⟨U, hU⟩ := matrix_of_standard_intertwiner g T hT
  exact ⟨U, LieEquiv.ext (fun X => Subtype.ext (hU X))⟩

/-- Every complex automorphism of the special linear algebra in size at least
two is a matrix conjugation, possibly preceded by negative transpose. -/
theorem matrix_automorphisms : matrixAutomorphismType := by
  intro n hn g
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hk : 1 ≤ k := by omega
  let C := cartan k
  have hC := ClassicalRootsA.cartan_isCartan k
  have hC' : Specs.LieAlgebrasAndRepresentations.CartanEqualsToral.IsCartan_value C :=
    ⟨hC.nilpotent, hC.self_normalizing⟩
  obtain ⟨e, he, heC⟩ := cartan_conjugacy (SL (Fin (k+1)))
    (special_linear_semisimple _) (C.map g.toLieHom) C (cartan_map C hC' g) hC'
  have hnorm : C.map (g.trans e).toLieHom = C :=
    (CartanConjugacy.map_trans C g e).trans heC
  obtain ⟨U, hU⟩ := inner_automorphism_matrix e he
  have hU' : e.symm = matrixConjugation U⁻¹ := hU ▸ matrixConjugation_inverse U
  rcases normalizer_matrix_forms hk (g.trans e) hnorm with ⟨W, hW⟩ | ⟨W, hW⟩
  · left
    refine ⟨U⁻¹ * W, fun X => ?_⟩
    have h := congrArg (fun f : SL (Fin (k+1)) ≃ₗ⁅ℂ⁆ SL (Fin (k+1)) => e.symm (f X)) hW
    rw [LieEquiv.trans_apply, LieEquiv.symm_apply_apply, hU', ← matrixConjugation_mul] at h
    exact congrArg Subtype.val h
  · right
    refine ⟨U⁻¹ * W, fun X => ?_⟩
    have h := congrArg (fun f : SL (Fin (k+1)) ≃ₗ⁅ℂ⁆ SL (Fin (k+1)) => e.symm (f X)) hW
    rw [LieEquiv.trans_apply, LieEquiv.symm_apply_apply, hU', LieEquiv.trans_apply,
      ← matrixConjugation_mul] at h
    exact congrArg Subtype.val h

end MatrixAutomorphismAssembly

/-- Every embedded real form of `sl_n(ℂ)` is one of the three matrix families.
The quaternionic case of size two is represented by the compact unitary form. -/
theorem classification : classificationType := by
  intro n hn S hS
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let Ω : Conjugation (SL (Fin n)) := compactConjugation
  obtain ⟨θ, a, hc, hi, _, _, ⟨es⟩⟩ :=
    PolarRealStructures.real_form_reduction Ω (compactConjugation_isCompact (Fin n)) S hS
  rcases matrix_automorphisms n hn a with hInner | hOuter
  · obtain ⟨p, q, τ, b, hpq, hτ, hb⟩ := inner_case (Fin n) Ω a hc hi compact_apply hInner
    obtain ⟨e⟩ := (forms_isomorphic_iff _ _).2 ⟨b, hb⟩
    exact Or.inl ⟨p, q, by simpa using hpq, τ, es.trans e, hτ⟩
  · rcases outer_case (Fin n) Ω a hc hi compact_apply hOuter with hSplit | ⟨m, hm, ⟨e⟩⟩
    · obtain ⟨e⟩ := hSplit
      exact Or.inr (Or.inl ⟨es.trans e⟩)
    have he : n = 2 * m := by simpa using hm
    by_cases h : 2 ≤ m
    · exact Or.inr (Or.inr ⟨m, h, he, ⟨es.trans e⟩⟩)
    have hm1 : m = 1 := by omega
    subst m
    obtain ⟨ω, hω, eq, _⟩ := quaternionic_rank_one
    obtain ⟨ω', a', hc', hi', hω', _, hτ, _, _⟩ := unitary_model 2 0
    let τ := involutionConjugation ω' a' hc' hi'
    let reindex : Blocks 1 1 ≃ Blocks 2 0 :=
      (Fintype.equivFin _).trans ((finCongr (by simp)).trans (Fintype.equivFin _).symm)
    have hb : Intertwines ω τ (reindexSL reindex) := by
      intro X
      apply Subtype.ext
      rw [hτ, compact_endpoints 2 0 (Or.inr rfl), reindexSL_apply, reindexSL_apply, hω]
      rfl
    obtain ⟨er⟩ := (forms_isomorphic_iff _ _).2 ⟨_, hb⟩
    exact Or.inl ⟨2, 0, by omega, τ, es.trans (e.trans (eq.trans er)), hτ⟩

theorem abstract_classification : abstractClassificationType := by
  intro n hn A _ _ ⟨e⟩
  let ρ := coefficientConjugation A
  let σ := ρ.transport e
  have h : Intertwines ρ σ e := by
    intro z
    change e (ρ.map (e.symm (e z))) = e (ρ.map z)
    rw [e.symm_apply_apply]
  obtain ⟨f, _⟩ := restrict_complex_isomorphism ρ σ e h
  obtain ⟨g, _⟩ := coefficient_fixed_equiv A
  let d := g.trans f
  rcases classification n hn σ.fixed (fixed_isRealForm σ) with ⟨p, q, hpq, τ, b, hτ⟩ | hOther
  · exact Or.inl ⟨p, q, hpq, τ, d.trans b, hτ⟩
  · rcases hOther with hSplit | ⟨m, hm, hs, ⟨b⟩⟩
    · obtain ⟨b⟩ := hSplit
      exact Or.inr (Or.inl ⟨d.trans b⟩)
    · exact Or.inr (Or.inr ⟨m, hm, hs, ⟨d.trans b⟩⟩)

open scoped TensorProduct in
/-- The listed matrix models exhaust the real forms and have the indicated complexification. -/
theorem type_a_real_form_iff (n : ℕ) (hn : 2 ≤ n) (A : Type*)
    [LieRing A] [LieAlgebra ℝ A] :
    Nonempty ((ℂ ⊗[ℝ] A) ≃ₗ⁅ℂ⁆ SL (Fin n)) ↔ IsTypeARealFormModel n A := by
  refine ⟨abstract_classification n hn A, ?_⟩
  intro h
  rcases h with hUnitary | hSplit | hQuaternionic
  · obtain ⟨p, q, hpq, σ, e, _⟩ := hUnitary
    obtain ⟨f, _⟩ := fixed_complexification σ
    let r : Blocks p q ≃ Fin n := finSumFinEquiv.trans (finCongr hpq)
    exact ⟨(complexifyEquiv e).trans (f.trans (reindexSL r))⟩
  · obtain ⟨e⟩ := hSplit
    obtain ⟨b⟩ := split_fixed_equiv (Fin n)
    obtain ⟨f, _⟩ := fixed_complexification (splitConjugation : Conjugation (SL (Fin n)))
    exact ⟨(complexifyEquiv (e.trans b)).trans f⟩
  · obtain ⟨m, _, hsize, ⟨e⟩⟩ := hQuaternionic
    subst n
    obtain ⟨b⟩ := quaternionic_fixed_equiv m
    obtain ⟨f, _⟩ := fixed_complexification (quaternionicConjugation m)
    let r : Blocks m m ≃ Fin (2 * m) := finSumFinEquiv.trans (finCongr (by omega))
    exact ⟨(complexifyEquiv (e.trans b)).trans (f.trans (reindexSL r))⟩

section CompactGeometry

open scoped TensorProduct
open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature
  (compactPart noncompactPart fixedConjugation compactEigenspace mulI)
open private cartan_parts_complementary from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanDecompositionSignature

private theorem killing_nonpositive_of_compactly_embedded
    {A : Type*} [LieRing A] [LieAlgebra ℝ A] [FiniteDimensional ℝ A]
    {K : LieSubalgebra ℝ A} (hK : IsCompactlyEmbedded K) (x : K) :
    _root_.killingForm ℝ A x.val x.val ≤ 0 := by
  classical
  obtain ⟨B, hsymm, hpos, hskew⟩ := hK
  let core : InnerProductSpace.Core ℝ A :=
    { inner := fun v w => B v w
      conj_inner_symm := fun v w => hsymm.eq w v
      re_inner_nonneg := fun v => by
        change 0 ≤ B v v
        by_cases h : v = 0
        · simp [h]
        · exact (hpos v h).le
      add_left := fun v w z => by rw [map_add, LinearMap.add_apply]
      smul_left := fun v w r => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
        RCLike.conj_to_real]
      definite := fun v hv => by
        by_contra h
        exact (hpos v h).ne' hv }
  let : NormedAddCommGroup A := core.toNormedAddCommGroup
  let : InnerProductSpace.Core ℝ A := core
  let : InnerProductSpace ℝ A := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ A)
  let b := stdOrthonormalBasis ℝ A
  let f := LieAlgebra.ad ℝ A x.val
  let M := LinearMap.toMatrix b.toBasis b.toBasis f
  have hM i j : M j i = -M i j := by
    simp only [M, LinearMap.toMatrix_apply]
    rw [OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
    change B (b j) ⁅x.val, b i⁆ = -B (b i) ⁅x.val, b j⁆
    rw [hsymm.eq (b j) _, hskew]
  rw [killingForm_apply_apply, LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  change (LinearMap.toMatrix b.toBasis b.toBasis (f * f)).trace ≤ 0
  rw [LinearMap.toMatrix_mul]
  change (M * M).trace ≤ 0
  exact Finset.sum_nonpos fun i _ => by
    change (M * M) i i ≤ 0
    rw [Matrix.mul_apply]
    exact Finset.sum_nonpos fun j _ => by
      rw [hM i j, mul_neg]
      exact neg_nonpos.mpr (mul_self_nonneg _)

theorem model_compact_part : modelCompactPartType := by
  intro ι _ _ ω a hcomm hinv hcompact
  let S := (involutionConjugation ω a hcomm hinv).fixed
  let C := modelCompactPart ω a hcomm hinv
  let P := compactPart ω a hcomm hinv
  let N := noncompactPart ω a hcomm hinv
  let κ := fixedConjugation ω a hcomm
  have ha (x : C) : a x.val.val = x.val.val := by
    have h := x.val.property
    change a (ω.map x.val.val) = x.val.val at h
    rw [show ω.map x.val.val = x.val.val from x.property] at h
    exact h
  have hω (x : κ.fixed) : ω.map x.val.val = x.val.val :=
    congrArg Subtype.val x.property
  let e : C ≃ₗ⁅ℝ⁆ κ.fixed :=
    { toFun := fun x => ⟨⟨x.val.val, ha x⟩, Subtype.ext x.property⟩
      invFun := fun x => ⟨⟨x.val.val, by
        change a (ω.map x.val.val) = x.val.val
        rw [hω x]
        exact x.val.property⟩, hω x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_lie' := fun {_ _} => rfl }
  have hP (x : S) : x ∈ C ↔ x ∈ P := by
    change ω.map x.val = x.val ↔ ω.map x.val = x.val ∧ a x.val = (1 : ℂ) • x.val
    constructor
    · intro hx
      exact ⟨hx, (ha ⟨x, hx⟩).trans (one_smul ℂ _).symm⟩
    · exact And.left
  obtain ⟨ef, hef⟩ := fixed_complexification κ
  obtain ⟨hneg, hpos, horth⟩ := CartanDecompositionSignature.cartan_killing ω a hcomm hinv hcompact
  have hsum : P ⊔ N = ⊤ := (cartan_parts_complementary ω a hcomm hinv).sup_eq_top
  have hparts (x : S) : ∃ p ∈ P, ∃ n ∈ N, p + n = x :=
    Submodule.mem_sup.mp (hsum.symm ▸ Submodule.mem_top)
  have hmax (K : LieSubalgebra ℝ S) (hCK : C ≤ K)
      (hK : ∀ x : K, _root_.killingForm ℝ S x.val x.val ≤ 0) : K = C := by
    apply le_antisymm _ hCK
    intro x hx
    obtain ⟨p, hp, n, hn, heq⟩ := hparts x
    have hpC := (hP p).mpr hp
    have hnK : n ∈ K := by
      have hs := K.sub_mem hx (hCK hpC)
      have he : x - p = n := by rw [← heq]; abel
      exact he ▸ hs
    have hn0 : n = 0 := by
      by_contra hnz
      exact (not_lt_of_ge (hK ⟨n, hnK⟩)) (hpos ⟨n, hn⟩ hnz)
    rw [hn0, add_zero] at heq
    exact heq ▸ hpC
  have hωa (x : S) : ω.map x.val = a x.val := by
    have h := congrArg (fun z => a z) x.property
    change a (a (ω.map x.val)) = a x.val at h
    rwa [hinv] at h
  let act (x : S) : S := ⟨a x.val, by
    change a (ω.map (a x.val)) = a x.val
    rw [hcomm, hinv, hωa]⟩
  have hact (x : S) : act (act x) = x := Subtype.ext (hinv _)
  let θ : S ≃ₗ⁅ℝ⁆ S :=
    { toFun := act
      invFun := act
      left_inv := hact
      right_inv := hact
      map_add' := fun x y => Subtype.ext (map_add a x.val y.val)
      map_smul' := fun r x => Subtype.ext (map_smul a (r : ℂ) x.val)
      map_lie' := fun {x y} => Subtype.ext (a.map_lie x.val y.val) }
  have hpθ (p : P) : θ p.val = p.val := Subtype.ext (ha ⟨p.val, (hP p.val).mpr p.property⟩)
  have hnθ (n : N) : θ n.val = -n.val := by
    obtain ⟨z, hz, hIz⟩ :
        n.val.val ∈ (compactEigenspace ω a (-1)).map mulI := n.property
    have haz : a z = -z := hz.2.trans (neg_one_smul ℂ _)
    apply Subtype.ext
    change a n.val.val = -n.val.val
    change Complex.I • z = n.val.val at hIz
    rw [← hIz, map_smul, haz, smul_neg]
  let K := _root_.killingForm ℝ S
  let B := -K.compRight θ.toLinearEquiv.toLinearMap
  have hCcompact : IsCompactlyEmbedded C := by
    refine ⟨B, ⟨fun x y => ?_⟩, ?_, ?_⟩
    · change -K x (θ y) = -K y (θ x)
      have hsymm : K x (θ y) = K (θ y) x := LieModule.traceForm_comm ℝ S S x (θ y)
      rw [hsymm]
      have h := LieAlgebra.killingForm_of_equiv_apply θ (θ y) x
      change K (act (act y)) (θ x) = K (θ y) x at h
      rw [hact] at h
      rw [h]
    · intro x hx
      obtain ⟨p, hp, n, hn, heq⟩ := hparts x
      have hc₁ : K p n = 0 := horth ⟨p, hp⟩ ⟨n, hn⟩
      have hc₂ : K n p = 0 := (LieModule.traceForm_comm ℝ S S n p).trans hc₁
      have hxB : B x x = -K p p + K n n := by
        change -K x (θ x) = _
        rw [← heq, map_add θ, hpθ ⟨p, hp⟩, hnθ ⟨n, hn⟩]
        simp only [map_add, map_neg, LinearMap.add_apply, hc₁, hc₂]
        ring
      rw [hxB]
      by_cases hp0 : p = 0
      · have hn0 : n ≠ 0 := fun h => hx (by rw [← heq, hp0, h, add_zero])
        have hpz : K p p = 0 := by rw [hp0, map_zero]
        rw [hpz, neg_zero, zero_add]
        exact hpos ⟨n, hn⟩ hn0
      · have hnle : 0 ≤ K n n := by
          by_cases hn0 : n = 0
          · simp [hn0, K]
          · exact (hpos ⟨n, hn⟩ hn0).le
        exact add_pos_of_pos_of_nonneg (neg_pos.mpr (hneg ⟨p, hp⟩ hp0)) hnle
    · intro x y z
      have hθx : θ x.val = x.val := Subtype.ext (ha x)
      have hθbr : θ ⁅x.val, z⁆ = ⁅x.val, θ z⁆ := by rw [θ.map_lie, hθx]
      change -(K ⁅x.val, y⁆ (θ z)) = -(-(K y (θ ⁅x.val, z⁆)))
      rw [hθbr]
      exact congrArg Neg.neg (LieModule.traceForm_apply_lie_apply' ℝ S S x.val y (θ z))
  let : FiniteDimensional ℝ (SL ι) := FiniteDimensional.trans ℝ ℂ (SL ι)
  let : FiniteDimensional ℝ S :=
    FiniteDimensional.of_injective S.toSubmodule.subtype Subtype.val_injective
  refine ⟨⟨(complexifyEquiv e).trans ef, ?_⟩, ?_, hmax, hCcompact, ?_⟩
  · intro c x
    change (ef ((complexifyEquiv e) (c ⊗ₜ[ℝ] x))).val = _
    rw [complexifyEquiv_tmul, hef]
    rfl
  · intro x hx
    exact hneg ⟨x.val, (hP x.val).mp x.property⟩ hx
  · intro K hCK hK
    exact hmax K hCK (killing_nonpositive_of_compactly_embedded hK)

end CompactGeometry

section ModelInvariants

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

section CompactFixedInvariants

open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (IsCompact)

open private compact_intertwiner from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

private def complexFixedEquiv (a : SL ι ≃ₗ⁅ℂ⁆ SL ι) (b : SL κ ≃ₗ⁅ℂ⁆ SL κ)
    (f : SL ι ≃ₗ⁅ℂ⁆ SL κ) (h : ∀ z, b (f z) = f (a z)) :
    complexFixed a ≃ₗ⁅ℂ⁆ complexFixed b where
  toFun z := ⟨f z.val, (h z.val).trans (congrArg f z.property)⟩
  invFun z := ⟨f.symm z.val, f.injective (by
    change f (a (f.symm z.val)) = f (f.symm z.val)
    rw [← h, f.apply_symm_apply]
    exact z.property)⟩
  left_inv z := Subtype.ext (f.symm_apply_apply z.val)
  right_inv z := Subtype.ext (f.apply_symm_apply z.val)
  map_add' x y := Subtype.ext (map_add f x.val y.val)
  map_smul' c x := Subtype.ext (map_smul f c x.val)
  map_lie' := Subtype.ext (f.map_lie _ _)

private theorem unitary_conjugation_eq {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    {σ τ : Conjugation L} (h : ∀ x, σ.map x = τ.map x) : σ = τ := by
  apply Conjugation.ext_map
  exact LieHom.ext h

private theorem compactFixed_of_isomorphic (e : ι ≃ κ)
    (ω : Conjugation (SL ι)) (υ : Conjugation (SL κ))
    (hc : IsCompact ω) (he : Intertwines ω υ (reindexSL e))
    (a : SL ι ≃ₗ⁅ℂ⁆ SL ι) (b : SL κ ≃ₗ⁅ℂ⁆ SL κ)
    (ha : Intertwines ω ω a) (hb : Intertwines υ υ b)
    (hai : Function.Involutive a) (hbi : Function.Involutive b)
    (h : Nonempty ((involutionConjugation ω a ha hai).fixed ≃ₗ⁅ℝ⁆
      (involutionConjugation υ b hb hbi).fixed)) :
    Nonempty (complexFixed a ≃ₗ⁅ℂ⁆ complexFixed b) := by
  let f := reindexSL e
  let b' := (f.trans b).trans f.symm
  have hb' : Intertwines ω ω b' := by
    intro x
    apply f.injective
    change f (ω.map (f.symm (b (f x)))) = f (f.symm (b (f (ω.map x))))
    rw [← he, f.apply_symm_apply, f.apply_symm_apply, ← he, hb]
  have hbi' : Function.Involutive b' := by
    intro x
    change f.symm (b (f (f.symm (b (f x))))) = x
    rw [f.apply_symm_apply, hbi, f.symm_apply_apply]
  obtain ⟨g, hg⟩ := (forms_isomorphic_iff _ _).mp h
  have hg' : Intertwines (involutionConjugation ω a ha hai)
      (involutionConjugation ω b' hb' hbi') (g.trans f.symm) := by
    intro x
    apply f.injective
    have h₁ := hg x
    change b (υ.map (g x)) = g (a (ω.map x)) at h₁
    change f (f.symm (b (f (ω.map (f.symm (g x)))))) =
      f (f.symm (g (a (ω.map x))))
    rw [f.apply_symm_apply, f.apply_symm_apply, ← he, f.apply_symm_apply, h₁]
  obtain ⟨k, _, hk⟩ := compact_intertwiner ω hc a b' ha hb' hai hbi' _ hg'
  refine ⟨complexFixedEquiv a b (k.trans f) ?_⟩
  intro x
  have h₁ := congrArg f (hk x)
  change f (f.symm (b (f (k x)))) = f (k (a x)) at h₁
  simpa using h₁

private def blockTrace (p q : ℕ) :
    (Matrix (Fin p) (Fin p) ℂ × Matrix (Fin q) (Fin q) ℂ) →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin p) ℂ ℂ).coprod (Matrix.traceLinearMap (Fin q) ℂ ℂ)

private theorem fromBlocks_trace (A : Matrix (Fin p) (Fin p) ℂ)
    (B : Matrix (Fin q) (Fin q) ℂ) :
    (Matrix.fromBlocks A 0 0 B).trace = A.trace + B.trace := by
  unfold Matrix.trace
  rw [Fintype.sum_sum_type]
  rfl

private def blockFixedLinearEquiv {p q : ℕ}
    (a : SL (Blocks p q) ≃ₗ⁅ℂ⁆ SL (Blocks p q))
    (ha : ∀ X : SL (Blocks p q), X ∈ complexFixed a ↔ isBlockDiagonal X.val) :
    complexFixed a ≃ₗ[ℂ] LinearMap.ker (blockTrace p q) where
  toFun X := ⟨(X.val.val.toBlocks₁₁, X.val.val.toBlocks₂₂), by
    change X.val.val.toBlocks₁₁.trace + X.val.val.toBlocks₂₂.trace = 0
    rw [← fromBlocks_trace]
    have h := (ha X.val).mp X.property
    have hm : Matrix.fromBlocks X.val.val.toBlocks₁₁ 0 0 X.val.val.toBlocks₂₂ = X.val.val := by
      ext i j
      cases i <;> cases j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, h.1, h.2]
    rw [hm]
    exact X.val.property⟩
  invFun X :=
    ⟨⟨Matrix.fromBlocks X.val.1 0 0 X.val.2, by
      change (Matrix.fromBlocks X.val.1 0 0 X.val.2).trace = 0
      rw [fromBlocks_trace]
      exact X.property⟩, (ha _).mpr ⟨by simp, by simp⟩⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    have h := (ha X.val).mp X.property
    ext i j
    cases i <;> cases j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, h.1, h.2]
  right_inv X := by
    apply Subtype.ext
    simp
  map_add' X Y := rfl
  map_smul' c X := rfl

private theorem blockFixed_finrank {p q : ℕ} (h : 0 < p + q)
    (a : SL (Blocks p q) ≃ₗ⁅ℂ⁆ SL (Blocks p q))
    (ha : ∀ X : SL (Blocks p q), X ∈ complexFixed a ↔ isBlockDiagonal X.val) :
    Module.finrank ℂ (complexFixed a) + 1 = p * p + q * q := by
  have hs : Function.Surjective (blockTrace p q) := by
    intro z
    rcases Nat.eq_zero_or_pos p with hp | hp
    · have hq : 0 < q := by omega
      let i : Fin q := ⟨0, hq⟩
      exact ⟨(0, Matrix.single i i z), by simp [blockTrace]⟩
    · let i : Fin p := ⟨0, hp⟩
      exact ⟨(Matrix.single i i z, 0), by simp [blockTrace]⟩
  have hr := (blockTrace p q).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self,
    Module.finrank_prod, Module.finrank_matrix, Module.finrank_matrix,
    Fintype.card_fin, Fintype.card_fin,
    ← (blockFixedLinearEquiv a ha).finrank_eq, add_comm 1] at hr
  simpa using hr

private theorem compact_model_unique (ι : Type) [Fintype ι] [DecidableEq ι]
    (ω : Conjugation (SL ι)) (hω : ∀ X, (ω.map X).val = -X.valᴴ) :
    ω = compactConjugation :=
  unitary_conjugation_eq (fun X => Subtype.ext ((hω X).trans (compact_apply X).symm))

theorem unitary_uniqueness : unitaryUniquenessType := by
  intro p q r s hsize hsum σ τ hσ hτ
  constructor
  · intro hiso
    obtain ⟨ω, a, ha, hai, hω, _, hσ', _, hfix⟩ := unitary_model p q
    obtain ⟨υ, b, hb, hbi, hυ, _, hτ', _, hfix'⟩ := unitary_model r s
    have eqω := compact_model_unique _ _ hω
    have eqυ := compact_model_unique _ _ hυ
    subst ω
    subst υ
    have eqσ : σ = involutionConjugation compactConjugation a ha hai :=
      unitary_conjugation_eq (fun X => Subtype.ext ((hσ X).trans (hσ' X).symm))
    have eqτ : τ = involutionConjugation compactConjugation b hb hbi :=
      unitary_conjugation_eq (fun X => Subtype.ext ((hτ X).trans (hτ' X).symm))
    rw [eqσ, eqτ] at hiso
    let e : Blocks p q ≃ Blocks r s := (finSumFinEquiv.trans (finCongr hsum)).trans finSumFinEquiv.symm
    obtain ⟨k⟩ := compactFixed_of_isomorphic e _ _ (compactConjugation_isCompact (Blocks p q))
      (reindexSL_intertwines e) a b
      ha hb hai hbi hiso
    have hn := blockFixed_finrank (by omega : 0 < p + q) a hfix
    have hn' := blockFixed_finrank (by omega : 0 < r + s) b hfix'
    rw [k.toLinearEquiv.finrank_eq] at hn
    have hsq : p * p + q * q = r * r + s * s := hn.symm.trans hn'
    have hprod : (p : ℤ) * q = (r : ℤ) * s := by
      have h₁ : (p : ℤ) + q = r + s := by exact_mod_cast hsum
      have h₂ : (p : ℤ) * p + (q : ℤ) * q = (r : ℤ) * r + (s : ℤ) * s := by
        exact_mod_cast hsq
      nlinarith [congrArg (· ^ (2 : ℕ)) h₁]
    have hp : ((p : ℤ) - r) * ((p : ℤ) - s) = 0 := by
      have h₁ : (p : ℤ) + q = r + s := by exact_mod_cast hsum
      calc
        ((p : ℤ) - r) * ((p : ℤ) - s) = p * ((p : ℤ) - (r + s)) + r * s := by ring
        _ = 0 := by rw [← h₁, ← hprod]; ring
    rcases mul_eq_zero.mp hp with hp | hp
    · left
      have hpr : p = r := by omega
      exact ⟨hpr, by omega⟩
    · right
      have hps : p = s := by omega
      exact ⟨hps, by omega⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have h : σ = τ := unitary_conjugation_eq (fun X => Subtype.ext ((hσ X).trans (hτ X).symm))
      subst τ
      exact ⟨LieEquiv.refl⟩
    · exact unitary_exchange _ _ _ _ hσ hτ

end CompactFixedInvariants

section ClassicalFixedDimensions

private def UpperPair (ι : Type*) [LT ι] := {ij : ι × ι // ij.1 < ij.2}

private def symmetricMatrixSpace (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Submodule ℂ (Matrix ι ι ℂ) :=
  selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ)

private theorem mem_symmetricMatrixSpace (X : Matrix ι ι ℂ) :
    X ∈ symmetricMatrixSpace ι ↔ Xᵀ = X := by
  rw [symmetricMatrixSpace, mem_selfAdjointMatricesSubmodule,
    Matrix.IsSelfAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]

section OrderedIndex

variable [LinearOrder ι]

private instance : Fintype (UpperPair ι) := inferInstanceAs
  (Fintype {ij : ι × ι // ij.1 < ij.2})

private def triangularPairEquiv : (ι × ι) ≃ ι ⊕ (UpperPair ι ⊕ UpperPair ι) where
  toFun ij :=
    if h : ij.1 < ij.2 then Sum.inr (Sum.inl ⟨ij, h⟩)
    else if h' : ij.2 < ij.1 then Sum.inr (Sum.inr ⟨(ij.2, ij.1), h'⟩)
    else Sum.inl ij.1
  invFun
    | Sum.inl i => (i, i)
    | Sum.inr (Sum.inl ij) => ij.val
    | Sum.inr (Sum.inr ij) => (ij.val.2, ij.val.1)
  left_inv := by
    rintro ⟨i, j⟩
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h]
    · simp
    · simp [h, not_lt_of_gt h]
  right_inv := by
    rintro (i | ⟨⟨i, j⟩, hij⟩ | ⟨⟨i, j⟩, hij⟩)
    · simp
    · simp [hij]
    · simp [hij, not_lt_of_gt hij]

omit [DecidableEq ι] in
private theorem triangular_card :
    Fintype.card ι + 2 * Fintype.card (UpperPair ι) =
      Fintype.card ι * Fintype.card ι := by
  have h := Fintype.card_congr (triangularPairEquiv : (ι × ι) ≃ _)
  simp only [Fintype.card_prod, Fintype.card_sum] at h
  omega

private def triangularMatrix (c : ℂ) (u : UpperPair ι → ℂ) (d : ι → ℂ) :
    Matrix ι ι ℂ :=
  fun i j => if h : i < j then u ⟨(i, j), h⟩
    else if h' : j < i then c * u ⟨(j, i), h'⟩
    else d i

omit [Fintype ι] [DecidableEq ι] in
private theorem triangularMatrix_lt (c : ℂ) (u : UpperPair ι → ℂ) (d : ι → ℂ)
    {i j : ι} (h : i < j) :
    triangularMatrix c u d i j = u ⟨(i, j), h⟩ := by
  simp [triangularMatrix, h]

omit [Fintype ι] [DecidableEq ι] in
private theorem triangularMatrix_gt (c : ℂ) (u : UpperPair ι → ℂ) (d : ι → ℂ)
    {i j : ι} (h : j < i) :
    triangularMatrix c u d i j = c * u ⟨(j, i), h⟩ := by
  simp [triangularMatrix, h, not_lt_of_gt h]

omit [Fintype ι] [DecidableEq ι] in
private theorem triangularMatrix_diag (c : ℂ) (u : UpperPair ι → ℂ) (d : ι → ℂ)
    (i : ι) :
    triangularMatrix c u d i i = d i := by
  simp [triangularMatrix]

private def skewCoordinates : LieAlgebra.Orthogonal.so ι ℂ ≃ₗ[ℂ] (UpperPair ι → ℂ) where
  toFun X ij := X.val ij.val.1 ij.val.2
  invFun u := ⟨triangularMatrix (-1) u 0, (LieAlgebra.Orthogonal.mem_so _ _ _).mpr (by
    ext i j
    change triangularMatrix (-1) u 0 j i = -triangularMatrix (-1) u 0 i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [triangularMatrix_lt _ _ _ h, triangularMatrix_gt _ _ _ h, neg_one_mul]
    · simp [triangularMatrix_diag]
    · rw [triangularMatrix_gt _ _ _ h, triangularMatrix_lt _ _ _ h, neg_one_mul, neg_neg])⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    change triangularMatrix (-1) (fun ij => X.val ij.val.1 ij.val.2) 0 i j = X.val i j
    have hX := (LieAlgebra.Orthogonal.mem_so _ _ _).mp X.property
    have hx (i j : ι) : X.val j i = -X.val i j := congrFun (congrFun hX i) j
    rcases lt_trichotomy i j with h | rfl | h
    · exact triangularMatrix_lt _ _ _ h
    · rw [triangularMatrix_diag]
      change 0 = X.val i i
      linear_combination (-1 / 2 : ℂ) * hx i i
    · rw [triangularMatrix_gt _ _ _ h, neg_one_mul, ← hx]
  right_inv u := by
    funext ij
    exact triangularMatrix_lt _ _ _ ij.property
  map_add' X Y := rfl
  map_smul' c X := rfl

private def symmetricCoordinates :
    symmetricMatrixSpace ι ≃ₗ[ℂ] ((UpperPair ι → ℂ) × (ι → ℂ)) where
  toFun X := (fun ij => X.val ij.val.1 ij.val.2, fun i => X.val i i)
  invFun v := ⟨triangularMatrix 1 v.1 v.2, (mem_symmetricMatrixSpace _).mpr (by
    ext i j
    change triangularMatrix 1 v.1 v.2 j i = triangularMatrix 1 v.1 v.2 i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [triangularMatrix_lt _ _ _ h, triangularMatrix_gt _ _ _ h, one_mul]
    · rfl
    · rw [triangularMatrix_gt _ _ _ h, triangularMatrix_lt _ _ _ h, one_mul])⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    change triangularMatrix 1 (fun ij => X.val ij.val.1 ij.val.2) (fun k => X.val k k) i j = X.val i j
    have hX := (mem_symmetricMatrixSpace _).mp X.property
    have hx (i j : ι) : X.val j i = X.val i j := congrFun (congrFun hX i) j
    rcases lt_trichotomy i j with h | rfl | h
    · exact triangularMatrix_lt _ _ _ h
    · exact triangularMatrix_diag _ _ _ _
    · rw [triangularMatrix_gt _ _ _ h, one_mul, hx]
  right_inv v := by
    apply Prod.ext
    · funext ij
      exact triangularMatrix_lt _ _ _ ij.property
    · funext i
      exact triangularMatrix_diag _ _ _ _
  map_add' X Y := rfl
  map_smul' c X := rfl

private theorem so_finrank_twice :
    2 * Module.finrank ℂ (LieAlgebra.Orthogonal.so ι ℂ) + Fintype.card ι =
      Fintype.card ι * Fintype.card ι := by
  rw [(skewCoordinates (ι := ι)).finrank_eq, Module.finrank_fintype_fun_eq_card]
  exact add_comm _ _ |>.trans triangular_card

private theorem symmetric_finrank_twice :
    2 * Module.finrank ℂ (symmetricMatrixSpace ι) =
      Fintype.card ι * Fintype.card ι + Fintype.card ι := by
  rw [(symmetricCoordinates (ι := ι)).finrank_eq, Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
  have h := triangular_card (ι := ι)
  omega

end OrderedIndex

private theorem mem_sp_iff_symmetric_product (m : ℕ)
    (X : Matrix (Blocks m m) (Blocks m m) ℂ) :
    X ∈ LieAlgebra.Symplectic.sp (Fin m) ℂ ↔
      (Matrix.J (Fin m) ℂ * X) ∈ symmetricMatrixSpace (Blocks m m) := by
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
    mem_symmetricMatrixSpace, transpose_mul, J_transpose, mul_neg, mul_neg]
  exact neg_eq_iff_eq_neg.symm

private def symplecticToSymmetric (m : ℕ) :
    LieAlgebra.Symplectic.sp (Fin m) ℂ ≃ₗ[ℂ] symmetricMatrixSpace (Blocks m m) where
  toFun X := ⟨Matrix.J (Fin m) ℂ * X.val, (mem_sp_iff_symmetric_product m _).mp X.property⟩
  invFun X := ⟨(-Matrix.J (Fin m) ℂ) * X.val, (mem_sp_iff_symmetric_product m _).mpr (by
    rw [← mul_assoc, mul_neg, J_squared, neg_neg, one_mul]
    exact X.property)⟩
  left_inv X := Subtype.ext (by
    change (-Matrix.J (Fin m) ℂ) * (Matrix.J (Fin m) ℂ * X.val) = X.val
    rw [← mul_assoc, neg_mul, J_squared, neg_neg, one_mul])
  right_inv X := Subtype.ext (by
    change Matrix.J (Fin m) ℂ * ((-Matrix.J (Fin m) ℂ) * X.val) = X.val
    rw [← mul_assoc, mul_neg, J_squared, neg_neg, one_mul])
  map_add' X Y := Subtype.ext (Matrix.mul_add _ _ _)
  map_smul' c X := Subtype.ext (Matrix.mul_smul _ _ _)

private theorem sp_finrank_twice (m : ℕ) :
    2 * Module.finrank ℂ (LieAlgebra.Symplectic.sp (Fin m) ℂ) =
      (m + m) * (m + m) + (m + m) := by
  let : LinearOrder (Blocks m m) := LinearOrder.lift' (finSumFinEquiv : Blocks m m ≃ Fin (m + m))
    finSumFinEquiv.injective
  have h := symmetric_finrank_twice (ι := Blocks m m)
  rw [Fintype.card_sum, Fintype.card_fin] at h
  rw [(symplecticToSymmetric m).finrank_eq]
  exact h

end ClassicalFixedDimensions

section ClassicalFixedCenters

omit [Fintype ι] [DecidableEq ι] in
private theorem matrix_eq_zero_of_eq_neg (X : Matrix ι ι ℂ) (h : X = -X) : X = 0 := by
  ext i j
  have hij := congrFun (congrFun h i) j
  change X i j = -(X i j) at hij
  change X i j = 0
  linear_combination (1 / 2 : ℂ) * hij

private theorem sp_trivial_center (m : ℕ)
    (X : LieAlgebra.Symplectic.sp (Fin m) ℂ)
    (hX : ∀ Y : LieAlgebra.Symplectic.sp (Fin m) ℂ, ⁅X, Y⁆ = 0) : X = 0 := by
  let A := X.val.toBlocks₁₁
  let B := X.val.toBlocks₁₂
  let C := X.val.toBlocks₂₁
  let D := X.val.toBlocks₂₂
  have hblocks : X.val = Matrix.fromBlocks A B C D := (Matrix.fromBlocks_toBlocks _).symm
  have hcomm (Z : Matrix (Blocks m m) (Blocks m m) ℂ)
      (hZ : Z ∈ LieAlgebra.Symplectic.sp (Fin m) ℂ) : X.val * Z = Z * X.val := by
    apply sub_eq_zero.mp
    exact congrArg Subtype.val (hX ⟨Z, hZ⟩)
  have hsp (Y : Matrix (Fin m) (Fin m) ℂ) :
      Matrix.fromBlocks Y 0 0 (-Yᵀ) ∈ LieAlgebra.Symplectic.sp (Fin m) ℂ := by
    rw [mem_sp_iff_symmetric_product, mem_symmetricMatrixSpace, Matrix.J,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose]
    simp
  have h₁ := hcomm _ (hsp 1)
  rw [hblocks, Matrix.transpose_one, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h₁
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.fromBlocks_inj, true_and, and_true] at h₁
  have hB : B = 0 := matrix_eq_zero_of_eq_neg _ h₁.1.symm
  have hC : C = 0 := matrix_eq_zero_of_eq_neg _ h₁.2
  rw [hB, hC] at hblocks
  have hJ : Matrix.J (Fin m) ℂ ∈ LieAlgebra.Symplectic.sp (Fin m) ℂ := by
    rw [mem_sp_iff_symmetric_product, mem_symmetricMatrixSpace, Matrix.J_squared]
    simp
  have h₂ := hcomm _ hJ
  rw [hblocks, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h₂
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.fromBlocks_inj, true_and] at h₂
  have hAD : A = D := h₂.2.1.symm
  have h₃ (Y : Matrix (Fin m) (Fin m) ℂ) : Y * A = A * Y := by
    have h := hcomm _ (hsp Y)
    rw [hblocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.fromBlocks_inj,
      true_and] at h
    exact h.1.symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := A)
    (fun i j _ => h₃ (Matrix.single i j 1))
  have hAtranspose : Aᵀ = A := by
    rw [← hc]
    exact Matrix.diagonal_transpose _
  have h₄ := (mem_symmetricMatrixSpace _).mp
    ((mem_sp_iff_symmetric_product m _).mp X.property)
  rw [hblocks, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose] at h₄
  simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.neg_mul, Matrix.fromBlocks_inj, Matrix.transpose_zero,
    Matrix.transpose_neg, true_and, and_true] at h₄
  have hA : A = 0 := matrix_eq_zero_of_eq_neg _ (by
    have h := h₄.1
    rw [← hAD, hAtranspose] at h
    exact h)
  apply Subtype.ext
  rw [hblocks, ← hAD, hA, Matrix.fromBlocks_zero]
  rfl

private theorem blockFixed_nontrivial_center {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (a : SL (Blocks p q) ≃ₗ⁅ℂ⁆ SL (Blocks p q))
    (ha : ∀ X : SL (Blocks p q), X ∈ complexFixed a ↔ isBlockDiagonal X.val) :
    ∃ X : complexFixed a, X ≠ 0 ∧ ∀ Y : complexFixed a, ⁅X, Y⁆ = 0 := by
  let A : Matrix (Fin p) (Fin p) ℂ := Matrix.scalar (Fin p) (q : ℂ)
  let B : Matrix (Fin q) (Fin q) ℂ := Matrix.scalar (Fin q) (-(p : ℂ))
  let X : SL (Blocks p q) := ⟨Matrix.fromBlocks A 0 0 B, by
    change (Matrix.fromBlocks A 0 0 B).trace = 0
    rw [fromBlocks_trace]
    change (Matrix.scalar (Fin p) (q : ℂ)).trace +
      (Matrix.scalar (Fin q) (-(p : ℂ))).trace = 0
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.trace_diagonal, Matrix.trace_diagonal]
    simp [mul_comm]⟩
  have hx : X ∈ complexFixed a := (ha _).mpr ⟨by simp [X], by simp [X]⟩
  refine ⟨⟨X, hx⟩, ?_, ?_⟩
  · intro h
    let i : Fin p := ⟨0, hp⟩
    have hi := congrArg (fun Z : complexFixed a => Z.val.val (Sum.inl i) (Sum.inl i)) h
    change Matrix.scalar (Fin p) (q : ℂ) i i = 0 at hi
    have hqcast : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hi
    exact hqcast hi
  · intro Y
    apply Subtype.ext
    apply Subtype.ext
    change X.val * Y.val.val - Y.val.val * X.val = 0
    apply sub_eq_zero.mpr
    have hY := (ha Y.val).mp Y.property
    have hblocks : Y.val.val = Matrix.fromBlocks Y.val.val.toBlocks₁₁ 0 0 Y.val.val.toBlocks₂₂ := by
      ext i j
      cases i <;> cases j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, hY.1, hY.2]
    have hA := (Matrix.scalar_comm (q : ℂ) (Commute.all _) Y.val.val.toBlocks₁₁)
    have hB := (Matrix.scalar_comm (-(p : ℂ)) (Commute.all _) Y.val.val.toBlocks₂₂)
    rw [show X.val = Matrix.fromBlocks A 0 0 B from rfl, hblocks]
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [show A * _ = _ * A from hA, show B * _ = _ * B from hB]

end ClassicalFixedCenters

section TypeARowSeparation

open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (IsCompact)

private theorem unitary_model_with_compact {p q : ℕ} (σ : Conjugation (SL (Blocks p q)))
    (hσ : ∀ X, (σ.map X).val = -(signatureMatrix p q * X.valᴴ * signatureMatrix p q)) :
    ∃ (a : SL (Blocks p q) ≃ₗ⁅ℂ⁆ SL (Blocks p q))
      (ha : Intertwines compactConjugation compactConjugation a) (hai : Function.Involutive a),
      σ = involutionConjugation compactConjugation a ha hai ∧
      ∀ X : SL (Blocks p q), X ∈ complexFixed a ↔ isBlockDiagonal X.val := by
  obtain ⟨ω, a, ha, hai, hω, _, hσ', _, hfix⟩ := unitary_model p q
  have eqω := compact_model_unique _ _ hω
  subst ω
  exact ⟨a, ha, hai, unitary_conjugation_eq (fun X =>
    Subtype.ext ((hσ X).trans (hσ' X).symm)), hfix⟩

private theorem split_model_with_compact (n : ℕ) :
    ∃ (a : SL (Fin n) ≃ₗ⁅ℂ⁆ SL (Fin n))
      (ha : Intertwines compactConjugation compactConjugation a) (hai : Function.Involutive a),
      Nonempty (LieAlgebra.SpecialLinear.sl (Fin n) ℝ ≃ₗ⁅ℝ⁆
        (involutionConjugation compactConjugation a ha hai).fixed) ∧
      Nonempty (complexFixed a ≃ₗ⁅ℂ⁆ LieAlgebra.Orthogonal.so (Fin n) ℂ) := by
  obtain ⟨ω, a, ha, hai, hω, _, _, ⟨e, _⟩, ⟨k, _⟩⟩ := split_model (Fin n)
  have eqω := compact_model_unique _ _ hω
  subst ω
  exact ⟨a, ha, hai, ⟨e⟩, ⟨k⟩⟩

private theorem quaternionic_model_with_compact (m : ℕ) :
    ∃ (a : SL (Blocks m m) ≃ₗ⁅ℂ⁆ SL (Blocks m m))
      (ha : Intertwines compactConjugation compactConjugation a) (hai : Function.Involutive a),
      Nonempty (quaternionicSL (Fin m) ≃ₗ⁅ℝ⁆
        (involutionConjugation compactConjugation a ha hai).fixed) ∧
      Nonempty (complexFixed a ≃ₗ⁅ℂ⁆ LieAlgebra.Symplectic.sp (Fin m) ℂ) := by
  obtain ⟨ω, a, ha, hai, hω, _, _, ⟨e, _⟩, ⟨k, _⟩⟩ := quaternionic_model m
  have eqω := compact_model_unique _ _ hω
  subst ω
  exact ⟨a, ha, hai, ⟨e⟩, ⟨k⟩⟩

theorem distinct_rows : distinctRowsType := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q hsize σ hσ ⟨iso⟩
    obtain ⟨a, ha, hai, rfl, hfix⟩ := unitary_model_with_compact σ hσ
    obtain ⟨b, hb, hbi, ⟨r⟩, ⟨k⟩⟩ := split_model_with_compact (p + q)
    let e : Blocks p q ≃ Fin (p + q) := finSumFinEquiv
    obtain ⟨c⟩ := compactFixed_of_isomorphic e _ _ (compactConjugation_isCompact _)
      (reindexSL_intertwines e) a b ha hb hai hbi ⟨iso.trans r⟩
    have hblock := blockFixed_finrank (by omega : 0 < p + q) a hfix
    rw [(c.trans k).toLinearEquiv.finrank_eq] at hblock
    have hso := so_finrank_twice (ι := Fin (p + q))
    simp only [Fintype.card_fin] at hso
    have hval : (Module.finrank ℂ (LieAlgebra.Orthogonal.so (Fin (p + q)) ℂ) : ℤ) + 1 =
        (p : ℤ) * p + (q : ℤ) * q := by exact_mod_cast hblock
    have hval' : 2 * (Module.finrank ℂ (LieAlgebra.Orthogonal.so (Fin (p + q)) ℂ) : ℤ) +
        ((p : ℤ) + q) = ((p : ℤ) + q) * ((p : ℤ) + q) := by exact_mod_cast hso
    have hsize' : 2 < (p : ℤ) + q := by exact_mod_cast hsize
    nlinarith [sq_nonneg ((p : ℤ) - q)]
  · intro p q m hm hsum σ hσ ⟨iso⟩
    obtain ⟨a, ha, hai, rfl, hfix⟩ := unitary_model_with_compact σ hσ
    obtain ⟨b, hb, hbi, ⟨r⟩, ⟨k⟩⟩ := quaternionic_model_with_compact m
    have hm' : p + q = m + m := by omega
    let e : Blocks p q ≃ Blocks m m :=
      (finSumFinEquiv.trans (finCongr hm')).trans finSumFinEquiv.symm
    obtain ⟨c⟩ := compactFixed_of_isomorphic e _ _ (compactConjugation_isCompact _)
      (reindexSL_intertwines e) a b ha hb hai hbi ⟨iso.trans r⟩
    let u := c.trans k
    rcases eq_zero_or_pos p with hp | hp
    · have hblock := blockFixed_finrank (by omega : 0 < p + q) a hfix
      rw [u.toLinearEquiv.finrank_eq, hp, zero_mul, zero_add] at hblock
      have hsp := sp_finrank_twice m
      have hq : q = m + m := by omega
      rw [hq] at hblock
      nlinarith [Nat.mul_self_le_mul_self (show 4 ≤ m + m by omega)]
    · rcases eq_zero_or_pos q with hq | hq
      · have hblock := blockFixed_finrank (by omega : 0 < p + q) a hfix
        rw [u.toLinearEquiv.finrank_eq, hq, zero_mul, add_zero] at hblock
        have hsp := sp_finrank_twice m
        have hp' : p = m + m := by omega
        rw [hp'] at hblock
        nlinarith [Nat.mul_self_le_mul_self (show 4 ≤ m + m by omega)]
      · obtain ⟨X, hn, hX⟩ := blockFixed_nontrivial_center hp hq a hfix
        have hcenter (Y : LieAlgebra.Symplectic.sp (Fin m) ℂ) : ⁅u X, Y⁆ = 0 := by
          rw [← u.apply_symm_apply Y, ← u.map_lie, hX, map_zero]
        exact hn (u.injective ((sp_trivial_center m (u X) hcenter).trans (map_zero u).symm))
  · intro m hm ⟨iso⟩
    obtain ⟨a, ha, hai, ⟨r⟩, ⟨k⟩⟩ := split_model_with_compact (2 * m)
    obtain ⟨b, hb, hbi, ⟨r'⟩, ⟨k'⟩⟩ := quaternionic_model_with_compact m
    have hm' : 2 * m = m + m := by omega
    let e : Fin (2 * m) ≃ Blocks m m := (finCongr hm').trans finSumFinEquiv.symm
    obtain ⟨c⟩ := compactFixed_of_isomorphic e _ _ (compactConjugation_isCompact _)
      (reindexSL_intertwines e) a b ha hb hai hbi ⟨r.symm.trans (iso.trans r')⟩
    let u := k.symm.trans (c.trans k')
    have hso := so_finrank_twice (ι := Fin (2 * m))
    simp only [Fintype.card_fin] at hso
    rw [u.toLinearEquiv.finrank_eq, hm'] at hso
    have hsp := sp_finrank_twice m
    omega

end TypeARowSeparation

theorem unitary_compact_block : unitaryCompactBlockType := by
  intro p q a ha
  let f : complexFixed a ≃ₗ[ℂ] blockTraceZero p q := blockFixedLinearEquiv a ha
  have hX (X : complexFixed a) :
      X.val.val = Matrix.fromBlocks (f X).val.1 0 0 (f X).val.2 := by
    change X.val.val = (f.symm (f X)).val.val
    rw [f.symm_apply_apply]
  refine ⟨{ f with map_lie' := ?_ }, fun _ => rfl⟩
  intro X Y
  apply Subtype.ext
  let bx := Matrix.fromBlocks (f X).val.1 0 0 (f X).val.2
  let by' := Matrix.fromBlocks (f Y).val.1 0 0 (f Y).val.2
  have hbr : X.val.val * Y.val.val - Y.val.val * X.val.val = bx * by' - by' * bx :=
    congrArg₂ (fun A B : Matrix (Blocks p q) (Blocks p q) ℂ => A * B - B * A)
      (hX X) (hX Y)
  change ((X.val.val * Y.val.val - Y.val.val * X.val.val).toBlocks₁₁,
      (X.val.val * Y.val.val - Y.val.val * X.val.val).toBlocks₂₂) =
    ((f X).val.1 * (f Y).val.1 - (f Y).val.1 * (f X).val.1,
      (f X).val.2 * (f Y).val.2 - (f Y).val.2 * (f X).val.2)
  rw [hbr]
  simp only [bx, by', fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rfl

theorem split_rank_one_uniqueness : splitRankOneUniquenessType := by
  intro p q h σ hσ
  constructor
  · rintro ⟨f⟩
    obtain ⟨ω, a, hc, hi, _, _, hτ, _, _⟩ := unitary_model 1 1
    let τ := involutionConjugation ω a hc hi
    obtain ⟨e⟩ := split_rank_one τ hτ
    have hu := (unitary_uniqueness p q 1 1 (by omega) (by omega) σ τ hσ hτ).1 ⟨f.trans e.symm⟩
    exact hu.elim id id
  · rintro ⟨rfl, rfl⟩
    exact split_rank_one σ hσ

end ModelInvariants

end

end LieAlgebrasAndRepresentations.RealFormsTypeA
