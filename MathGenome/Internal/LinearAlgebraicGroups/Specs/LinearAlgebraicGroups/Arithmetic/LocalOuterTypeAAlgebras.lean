import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Degree
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Data.Complex.Basic

namespace LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras

open LinearAlgebraicGroups.UnitaryNormEquations (SecondKind)
open _root_.Specs.RM03.CSA (degree isCentralSimple)

universe u v

open scoped Matrix

/-- Conjugation on coefficients followed by transposition. -/
def conjugateTranspose {F E : Type u} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (σ : E ≃ₐ[F] E) (X : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) E :=
  X.transpose.map σ

/-- A unit matrix fixed by conjugate transposition gives a nondegenerate
Hermitian form in the column basis. The equation specifies its adjoint
after transporting the original involution to that basis. -/
def HasHermitianMatrix {F E A : Type u} [Field F] [Field E] [Algebra F E]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A]
    (s : SecondKind F E A) {n : ℕ} (e : A ≃ₐ[E] Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ H : (Matrix (Fin n) (Fin n) E)ˣ,
    conjugateTranspose s.conjugation (H : Matrix (Fin n) (Fin n) E) = H ∧
    ∀ x : A, e (s.adjoint x).unop =
      (↑H⁻¹ : Matrix (Fin n) (Fin n) E) *
        conjugateTranspose s.conjugation (e x) * H

/-- A nondegenerate Hermitian pairing with the transported involution as its
adjoint. Linearity in the second argument and conjugate symmetry also give
conjugate linearity in the first argument. -/
def IsHermitianAdjointForm {F E A : Type u} [Field F] [Field E] [Algebra F E]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A]
    (s : SecondKind F E A) {n : ℕ} (e : A ≃ₐ[E] Matrix (Fin n) (Fin n) E)
    (h : (Fin n → E) → (Fin n → E) → E) : Prop :=
  (∀ x, IsLinearMap E (h x)) ∧
  (∀ x y, s.conjugation (h x y) = h y x) ∧
  (∀ x, (∀ y, h y x = 0) → x = 0) ∧
  ∀ z x y, h (e z *ᵥ x) y = h x (e (s.adjoint z).unop *ᵥ y)

/-- Every central simple algebra with a unitary involution over a quadratic
extension of a nonarchimedean local field is split, in any characteristic. -/
def LocalSplitting : Prop :=
  ∀ {F E A : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field E] [Algebra F E] [Algebra.IsSeparable F E]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A],
    Module.finrank F E = 2 → isCentralSimple E A → SecondKind F E A →
    Nonempty (A ≃ₐ[E] Matrix (Fin (degree E A)) (Fin (degree E A)) E)

/-- The central simple algebra is split for the archimedean pair ℂ/ℝ. -/
def ArchimedeanSplitting : Prop :=
  ∀ {A : Type v} [Ring A] [Algebra ℂ A],
    isCentralSimple ℂ A →
    Nonempty (A ≃ₐ[ℂ] Matrix (Fin (degree ℂ A)) (Fin (degree ℂ A)) ℂ)

/-- Over any separable quadratic field extension, a unitary involution on a
split algebra is adjoint to a nondegenerate Hermitian form. -/
def HermitianAdjoint : Prop :=
  ∀ {F E A : Type u} [Field F] [Field E] [Algebra F E] [Algebra.IsSeparable F E]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A],
    Module.finrank F E = 2 → ∀ (s : SecondKind F E A) {n : ℕ},
    (e : A ≃ₐ[E] Matrix (Fin n) (Fin n) E) → ∃ h, IsHermitianAdjointForm s e h

end LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras
