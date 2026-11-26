import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.RingTheory.MatrixAlgebra

/-! The matrix presentation of a first-kind symplectic involution over a field
or a quaternion division algebra, with scalar extension over test algebras. -/

open scoped TensorProduct Matrix
open MulOpposite

universe u v w z q

namespace LinearAlgebraicGroups.Specs.SymplecticDivisionForms

variable {F : Type u} [Field F] {A : Type v} [Ring A] [Algebra F A]

abbrev AntiEquiv (F : Type*) (A : Type*) [CommRing F] [Ring A] [Algebra F A] :=
  A ≃ₐ[F] Aᵐᵒᵖ

def antiValue {R D : Type*} [CommRing R] [Ring D] [Algebra R D]
    (s : AntiEquiv R D) (x : D) : D := unop (s x)

structure Involution (F : Type*) (A : Type*) [Field F] [Ring A] [Algebra F A] where
  anti : AntiEquiv F A
  square : Function.Involutive (antiValue anti)

/-- Scalar extension of the actual first-kind algebra anti-automorphism. -/
noncomputable def extendAnti {F A : Type*} [CommRing F] [Ring A] [Algebra F A] (s : AntiEquiv F A) (R : Type*) [CommRing R] [Algebra F R] :
    AntiEquiv R (R ⊗[F] A) :=
  (Algebra.TensorProduct.congr (AlgEquiv.toOpposite R R) s).trans
    (Algebra.TensorProduct.opAlgEquiv F R R A)

def standardAdjoint {R : Type*} [CommRing R] (n : ℕ)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  (-Matrix.J (Fin n) R) * X.transpose * Matrix.J (Fin n) R

/-- A splitting of the algebra with involution, using the hyperbolic adjoint. -/
structure SplitComparison (s : Involution F A) (L : Type*) [Field L] [Algebra F L]
    (n : ℕ) where
  equiv : (L ⊗[F] A) ≃ₐ[L] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L
  adjoint (x : A) :
    equiv (1 ⊗ₜ[F] antiValue s.anti x) = standardAdjoint n (equiv (1 ⊗ₜ[F] x))

/-- Alternation is tested by self-pairing, including in characteristic two. -/
def AlternatingMatrix {I K : Type*} [Fintype I] [CommRing K] (H : Matrix I I K) : Prop :=
  ∀ x : I → K, x ⬝ᵥ (H *ᵥ x) = 0

def dagger {R D I : Type*} [CommRing R] [Ring D] [Algebra R D]
    (s : AntiEquiv R D) (X : Matrix I I D) : Matrix I I D :=
  fun i j => antiValue s (X j i)

def hermitianValue {R D I : Type*} [CommRing R] [Ring D] [Algebra R D] [Fintype I]
    (s : AntiEquiv R D) (H : Matrix I I D) (x y : I → D) : D :=
  (fun i => antiValue s (x i)) ⬝ᵥ (H *ᵥ y)

/-- Sesquilinearity on the right module, together with Hermitian symmetry.
The right action is written explicitly as pointwise multiplication. -/
structure HermitianLaws {R D I : Type*} [CommRing R] [Ring D] [Algebra R D]
    (s : AntiEquiv R D) (h : (I → D) → (I → D) → D) : Prop where
  add_right (x y z : I → D) : h x (y + z) = h x y + h x z
  mul_right (x y : I → D) (a : D) : h x (fun i => y i * a) = h x y * a
  symmetric (x y : I → D) : h y x = antiValue s (h x y)

def tensorMap {F : Type*} [CommRing F] (A : Type*) [Ring A] [Algebra F A]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) : R ⊗[F] A →ₐ[F] S ⊗[F] A :=
  Algebra.TensorProduct.map f (AlgHom.id F A)

def intoTensor {F : Type*} [CommRing F] (R : Type*) [CommRing R] [Algebra F R] (A : Type*) [Ring A] [Algebra F A] :
    A →ₐ[F] R ⊗[F] A := Algebra.TensorProduct.includeRight

/-- A chosen hyperbolic basis, expressed by the matrix with its vectors as columns. -/
def FieldModel : Prop :=
  ∀ {F : Type u} [Field F] {A : Type v} [Ring A] [Algebra F A]
    (_ : _root_.Specs.RM03.CSA.isCentralSimple F A)
    (s : Involution F A) {L : Type z} [Field L] [Algebra F L] {n r : ℕ},
    SplitComparison s L n → (e : A ≃ₐ[F] Matrix (Fin r) (Fin r) F) →
    ∃ (H : (Matrix (Fin r) (Fin r) F)ˣ)
      (P : Matrix (Fin n ⊕ Fin n) (Fin r) F) (Q : Matrix (Fin r) (Fin n ⊕ Fin n) F),
      AlternatingMatrix (H : Matrix (Fin r) (Fin r) F) ∧
      (∀ a, e (antiValue s.anti a) = H.inv * (e a).transpose * H.val) ∧
      P * Q = 1 ∧ Q * P = 1 ∧ Q.transpose * H.val * Q = Matrix.J (Fin n) F ∧
      ∃ E : ∀ (R : Type q) [CommRing R] [Algebra F R],
          (R ⊗[F] A) ≃ₐ[R] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R,
        (∀ (R : Type q) [CommRing R] [Algebra F R] (a : A),
          E R (1 ⊗ₜ[F] a) =
            ((P * e a * Q).map (algebraMap F R))) ∧
        (∀ (R : Type q) [CommRing R] [Algebra F R] (x : R ⊗[F] A),
          E R x ∈ Matrix.symplecticGroup (Fin n) R ↔
            antiValue (extendAnti s.anti R) x * x = 1) ∧
        ∀ (R S : Type q) [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
          (f : R →ₐ[F] S) (x : R ⊗[F] A), E S (tensorMap A f x) = (E R x).map f

open LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction (reducedTrace)

/-- The allowed input identifies the canonical conjugation with the size-two
adjugate in a splitting. The trace formula refers to the coefficient-defined
reduced trace of the original division algebra. -/
structure CanonicalConjugation {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (b : Involution F B) : Prop where
  trace (x : B) : antiValue b.anti x = algebraMap F B (reducedTrace hB x) - x
  adjugate (L : Type z) [Field L] [Algebra F L]
      (e : (L ⊗[F] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) (x : B) :
    e (1 ⊗ₜ[F] antiValue b.anti x) = (e (1 ⊗ₜ[F] x)).adjugate

def QuaternionModel : Prop :=
  ∀ {F : Type u} [Field F] {A : Type v} [Ring A] [Algebra F A]
    (_ : _root_.Specs.RM03.CSA.isCentralSimple F A)
    (s : Involution F A) {L : Type z} [Field L] [Algebra F L] {n r : ℕ},
    SplitComparison s L n →
    ∀ {B : Type w} [DivisionRing B] [Algebra F B]
      (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
      _root_.Specs.RM03.CSA.degree F B = 2 →
      ∀ (b : Involution F B), CanonicalConjugation.{u,w,z} hB b →
      ∀ (e : A ≃ₐ[F] Matrix (Fin r) (Fin r) B),
        ∃ H : (Matrix (Fin r) (Fin r) B)ˣ,
          dagger b.anti (H : Matrix (Fin r) (Fin r) B) = H.val ∧
          (∀ a, e (antiValue s.anti a) = H.inv * dagger b.anti (e a) * H.val) ∧
          (∀ i, ∃ a : F, (H : Matrix (Fin r) (Fin r) B) i i = algebraMap F B a) ∧
          HermitianLaws b.anti (hermitianValue b.anti H.val) ∧
          (∀ x, x ≠ 0 → ∃ y, hermitianValue b.anti H.val x y ≠ 0) ∧
          (∀ x, ∃ a : F, hermitianValue b.anti H.val x x = algebraMap F B a) ∧
          ∃ E : ∀ (R : Type q) [CommRing R] [Algebra F R],
              (R ⊗[F] A) ≃ₐ[R] Matrix (Fin r) (Fin r) (R ⊗[F] B),
            (∀ (R : Type q) [CommRing R] [Algebra F R] (a : A),
              E R (1 ⊗ₜ[F] a) = (e a).map (intoTensor R B)) ∧
            (∀ (R : Type q) [CommRing R] [Algebra F R],
              HermitianLaws (extendAnti b.anti R)
                (hermitianValue (extendAnti b.anti R) (H.val.map (intoTensor R B)))) ∧
            (∀ (R : Type q) [CommRing R] [Algebra F R] (g : (R ⊗[F] A)ˣ),
              antiValue (extendAnti s.anti R) (g : R ⊗[F] A) * ↑g = 1 ↔
                let h := hermitianValue (extendAnti b.anti R)
                  ((H : Matrix (Fin r) (Fin r) B).map (intoTensor R B))
                ∀ x y, h (E R ↑g *ᵥ x) (E R ↑g *ᵥ y) = h x y) ∧
            ∀ (R S : Type q) [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
              (f : R →ₐ[F] S) (x : R ⊗[F] A),
              E S (tensorMap A f x) = (E R x).map (tensorMap B f)

end LinearAlgebraicGroups.Specs.SymplecticDivisionForms
