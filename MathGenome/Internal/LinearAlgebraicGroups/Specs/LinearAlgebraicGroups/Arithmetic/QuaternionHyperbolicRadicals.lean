import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.CharacteristicTwoQuadraticPairs
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuaternionSpinScaleCover
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

open AlgebraicGeometry CategoryTheory Matrix MulOpposite ValuativeRel
open scoped TensorProduct Matrix CategoryTheory.MonObj
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.QuaternionHyperbolicRadicals

open NontrialitarianSpinModels (DescendedQuadraticPair SpinModel symmetricPart)
open QuaternionSpinScaleCover
open CharacteristicTwoQuadraticPairs
open SymplecticDivisionForms (antiValue hermitianValue)
open SymplecticInvolutionModels (HermitianPairing)
open CharacterDescent (Cocharacter)
open OppositeRadicals (IsNoncentral)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint HasLimit oppositeCocharacter)

section Coordinates

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K] [Fintype I] [DecidableEq I]
  [DivisionRing B] [Algebra F B] {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}

def column (x : B) (y : Fin d → B) (z : B) : QuaternionPairIndex d → B :=
  Sum.elim ![x, z] y

/-- The pairing and trace-one endomorphism in the coordinates of the given
complement, with its refinement identified in the original descended algebra. -/
structure ComplementRefinement (Q : QuaternionHyperbolicPresentation D hB d) where
  pairing : HermitianPairing Q.conjugation.anti (Fin d → B)
  pairingFormula : pairing.value = hermitianValue Q.conjugation.anti Q.complement.val
  ell : ρ.fixedSubalgebra
  ellTraceOne : ell + D.involution.toLinearMap ell = 1
  semitraceFormula : ∀ a : symmetricPart D.involution,
    D.semitrace a = algebraReducedTrace D.centralSimple (ell * a.val)
  complementAction : (Fin d → B) →ₗ[Bᵐᵒᵖ] (Fin d → B)
  complementTraceOne : IsTraceOne pairing complementAction
  quadraticFormula : ∀ x y z,
    scalarClass F (hermitianValue Q.conjugation.anti (quaternionHyperbolicGram Q.complement.val)
      (column x y z) (Q.matrixModel ell *ᵥ column x y z)) =
      scalarClass F (antiValue Q.conjugation.anti x * z) + refinement pairing complementAction y

def IsPairDiagonal (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    (c : Cocharacter G.val) : Prop :=
  ∀ (R : TestAlgebra F) (r : Rˣ),
    Q.matrixAt R (spinVectorProjection M R (cocharacterPoint c R r)).val =
      Matrix.fromBlocks
        (!![(algebraMap R (R ⊗[F] B) (r : R)), 0;
          0, (algebraMap R (R ⊗[F] B) (↑r⁻¹ : R))] : Matrix (Fin 2) (Fin 2) (R ⊗[F] B))
        0 0 1

/-- The vector action on the original columns, using the actual vector projection. -/
def ActsOnColumns (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    (g : Points G.val.X (CommAlgCat.of F F))
    (f : B × (Fin d → B) × B → B × (Fin d → B) × B) : Prop :=
  let R := CommAlgCat.of F F
  let T := Q.matrixAt R (spinVectorProjection M R g).val
  let col := fun p : B × (Fin d → B) × B => fun j =>
    (1 : F) ⊗ₜ[F] column p.1 p.2.1 p.2.2 j
  ∀ p, T *ᵥ col p = col (f p)

end Coordinates

/-- The simultaneous orthogonal complement of the two marked vectors. -/
def complementSubmodule {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    {s : SymplecticInvolutionModels.AntiAutomorphism F B} {n : ℕ}
    (h : HermitianPairing s (Fin n → B)) (x z : Fin n → B) :
    Submodule Bᵐᵒᵖ (Fin n → B) where
  carrier := {y | IsHyperbolicComplement h x z y}
  zero_mem' := by
    constructor
    · simpa using h.smul_right x (0 : Fin n → B) (0 : B)
    · simpa using h.smul_right z (0 : Fin n → B) (0 : B)
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [h.add_right, ha, hb, add_zero], by rw [h.add_right, ha', hb', add_zero]⟩
  smul_mem' := by
    rintro a b ⟨hb, hb'⟩
    exact ⟨by rw [← op_unop a, h.smul_right, hb, zero_mul],
      by rw [← op_unop a, h.smul_right, hb', zero_mul]⟩

def RecoverComplement : Prop :=
  ∀ {F K I B : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
    [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} {D : DescendedQuadraticPair ρ}
    (hB : isCentralSimple F B), degree F B = 2 →
    ∀ {d : ℕ} (Q : QuaternionHyperbolicPresentation D hB d), Nonempty (ComplementRefinement Q)

def OppositeColumnActions : Prop :=
  ∀ {F K I B : Type u} [Field F] [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Fintype I] [DecidableEq I]
    [DivisionRing B] [Algebra F B] {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
    (M : SpinModel G D), 4 ≤ Fintype.card I →
    ∀ (hB : isCentralSimple F B), degree F B = 2 →
    ∀ {d : ℕ} (Q : QuaternionHyperbolicPresentation D hB d)
      (c : Cocharacter G.val), IsPairDiagonal M Q c →
    ∀ (W : ComplementRefinement Q) (w : Fin d → B) (b : B),
      scalarClass F b = refinement W.pairing W.complementAction w →
      ∃ gPlus gMinus : Points G.val.X (CommAlgCat.of F F),
        HasLimit c gPlus 1 ∧ HasLimit (oppositeCocharacter c) gMinus 1 ∧
        ActsOnColumns M Q gPlus (fun (x, y, z) =>
          (x + W.pairing.value w y + b * z, y + fun j => w j * z, z)) ∧
        ActsOnColumns M Q gMinus (fun (x, y, z) =>
          (x, y + (fun j => w j * x), z + W.pairing.value w y + b * x))

def CentralizerColumns : Prop :=
  ∀ {F K I B : Type u} [Field F] [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Fintype I] [DecidableEq I]
    [DivisionRing B] [Algebra F B] {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
    (M : SpinModel G D), 4 ≤ Fintype.card I →
    ∀ (hB : isCentralSimple F B), degree F B = 2 →
    ∀ {d : ℕ} (Q : QuaternionHyperbolicPresentation D hB d)
      (c : Cocharacter G.val), IsPairDiagonal M Q c →
    ∀ (W : ComplementRefinement Q) (g : Points G.val.X (CommAlgCat.of F F)),
      Centralizes c g →
      ∃ (t : Bˣ) (r : (Fin d → B) ≃ₗ[Bᵐᵒᵖ] (Fin d → B)),
        (∀ x y, W.pairing.value (r x) (r y) = W.pairing.value x y) ∧
        (∀ x, refinement W.pairing W.complementAction (r x) =
          refinement W.pairing W.complementAction x) ∧
        ActsOnColumns M Q g (fun (x, y, z) =>
          ((t : B) * x, r y, (antiValue Q.conjugation.anti (t : B))⁻¹ * z))

def PairDiagonalNoncentral : Prop :=
  ∀ {F K I B : Type u} [Field F] [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Fintype I] [DecidableEq I]
    [DivisionRing B] [Algebra F B] {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
    (M : SpinModel G D), 4 ≤ Fintype.card I →
    ∀ (hB : isCentralSimple F B), degree F B = 2 →
    ∀ {d : ℕ} (Q : QuaternionHyperbolicPresentation D hB d)
      (c : Cocharacter G.val), IsPairDiagonal M Q c → IsNoncentral c

/-- The arithmetic hyperbolic pair supplies an adapted basis in the same
division algebra presentation, with precisely two quaternionic lines removed. -/
def ArithmeticPresentation : Prop :=
  ∀ {F K I B : Type u} [Field F] [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Fintype I] [DecidableEq I]
    [DivisionRing B] [Algebra F B] {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
    (_M : SpinModel G D) (hB : isCentralSimple F B), degree F B = 2 →
    ∀ (n : ℕ), 4 ≤ n →
    ∀ (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) B),
      ∃ (P : QuaternionPair D hB n e) (x z : Fin n → B)
        (W : (Fin (n - 2) → B) ≃ₗ[Bᵐᵒᵖ]
          complementSubmodule P.pairing x z),
        x ≠ 0 ∧ refinement P.pairing P.ellAction x = 0 ∧
        refinement P.pairing P.ellAction z = 0 ∧
        P.pairing.value x x = 0 ∧ P.pairing.value z z = 0 ∧
        P.pairing.value x z = 1 ∧ P.pairing.value z x = 1 ∧
        ∃ Q : QuaternionHyperbolicPresentation D hB (n - 2),
          Q.conjugation = P.bar ∧
          let into := fun q : QuaternionPairIndex (n - 2) → B =>
            op (q (Sum.inl 0)) • x + (W (q ∘ Sum.inr)).val + op (q (Sum.inl 1)) • z
          (∀ (a : ρ.fixedSubalgebra) (p : QuaternionPairIndex (n - 2) → B),
            into (Q.matrixModel a *ᵥ p) = e a *ᵥ into p) ∧
          (∀ p q, hermitianValue Q.conjugation.anti (quaternionHyperbolicGram Q.complement.val)
            p q = P.pairing.value (into p) (into q)) ∧
          (∀ p, scalarClass F
            (hermitianValue Q.conjugation.anti (quaternionHyperbolicGram Q.complement.val)
              p (Q.matrixModel P.ell *ᵥ p)) = refinement P.pairing P.ellAction (into p))

end LinearAlgebraicGroups.Specs.Arithmetic.QuaternionHyperbolicRadicals
