import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Polynomial
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Conormal
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! KD-12. A presentation includes the specified variables, relations and the
assertion that these relations generate the kernel. Both finite index sets may
be empty. No nonzero-ring hypothesis is imposed. -/
namespace Specs.AdvCommAlg.Differentials

universe u v
noncomputable section

/-- Rows are variables; columns are defining relations. -/
def presentationJacobian {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] {n m : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m)) :
    Matrix (Fin n) (Fin m) B :=
  fun i j => MvPolynomial.aeval P.val (MvPolynomial.pderiv i (P.relation j))

/-- The map between the actual finite powers B^m and B^n. -/
def jacobianRelationMap {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] {n m : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m)) :
    (Fin m → B) →ₗ[B] (Fin n → B) :=
  (presentationJacobian P).mulVecLin

/-- The displayed quotient map, specified independently by its values on variables. -/
def jacobianDifferentialMap {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] {n m : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m)) :
    (Fin n → B) →ₗ[B] KaehlerDifferential A B :=
  (Pi.basisFun B (Fin n)).constr B (fun i => KaehlerDifferential.D A B (P.val i))

def jacobianColumns : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (n m : ℕ)
    (P : Algebra.Presentation A B (Fin n) (Fin m)) (j : Fin m),
  jacobianRelationMap P (Pi.single j 1) =
    ∑ i : Fin n, MvPolynomial.aeval P.val (MvPolynomial.pderiv i (P.relation j)) •
      (Pi.single i 1 : Fin n → B)

def jacobianVariables : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (n m : ℕ)
    (P : Algebra.Presentation A B (Fin n) (Fin m)) (i : Fin n),
  jacobianDifferentialMap P (Pi.single i 1) = KaehlerDifferential.D A B (P.val i)

def jacobianExact : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (n m : ℕ)
    (P : Algebra.Presentation A B (Fin n) (Fin m)),
  Function.Exact (jacobianRelationMap P) (jacobianDifferentialMap P) ∧
    Function.Surjective (jacobianDifferentialMap P)

/-- The cokernel identification commutes with the entire quotient map, and
in particular sends each variable class to d of the specified generator. -/
def jacobianCokernel : Prop := ∀ (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (n m : ℕ)
    (P : Algebra.Presentation A B (Fin n) (Fin m)),
  ∃ e : ((Fin n → B) ⧸ LinearMap.range (jacobianRelationMap P)) ≃ₗ[B]
      KaehlerDifferential A B,
    (∀ x, e ((LinearMap.range (jacobianRelationMap P)).mkQ x) =
      jacobianDifferentialMap P x) ∧
    (∀ i : Fin n, e ((LinearMap.range (jacobianRelationMap P)).mkQ (Pi.single i 1)) =
      KaehlerDifferential.D A B (P.val i))

/-- The literal quotient appearing in the source. -/
abbrev JacobianQuotient (A : Type u) [CommRing A] (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) A) :=
  MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)

def quotientJacobianMatrix (A : Type u) [CommRing A] (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) A) :
    Matrix (Fin n) (Fin m) (JacobianQuotient A n m f) :=
  fun i j => Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.pderiv i (f j))

/-- Specialization to every displayed quotient, without requiring presentation
metadata as an extra input. -/
def quotientJacobianCokernel : Prop := ∀ (A : Type u) [CommRing A] (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) A),
  ∃ e : ((Fin n → JacobianQuotient A n m f) ⧸
      LinearMap.range (quotientJacobianMatrix A n m f).mulVecLin) ≃ₗ[JacobianQuotient A n m f]
        KaehlerDifferential A (JacobianQuotient A n m f),
    ∀ i : Fin n, e ((LinearMap.range (quotientJacobianMatrix A n m f).mulVecLin).mkQ
      (Pi.single i 1)) = KaehlerDifferential.D A (JacobianQuotient A n m f)
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.X i))

end
end Specs.AdvCommAlg.Differentials
