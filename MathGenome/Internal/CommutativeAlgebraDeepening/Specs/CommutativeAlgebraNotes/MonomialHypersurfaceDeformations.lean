import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.KoszulFlatDeformationModels

noncomputable section

open scoped TensorProduct

namespace Specs.CommutativeAlgebraNotes.MonomialHypersurfaceDeformations

open _root_.CommutativeAlgebraNotes
open SquareZeroLift
open CompleteIntersectionTangentSpace (dual reduction)
open SquareZeroLiftTorsor (ActsByReduction liftClass)

universe u z

abbrev P (R : Type u) [CommRing R] := MvPolynomial (Fin 1) R

abbrev X (R : Type u) [CommRing R] : P R := MvPolynomial.X 0

variable {k : Type u} [Field k]

abbrev equation (k : Type u) [Field k] (m : ℕ) : Fin 1 → P k := fun _ => X k ^ m

abbrev B (k : Type u) [Field k] (m : ℕ) := CompleteIntersectionTangentSpace.B (equation k m)

abbrev residue (m : ℕ) : P k →ₐ[k] B k m :=
  CompleteIntersectionTangentSpace.q (equation k m)

def slope (k : Type u) [Field k] (m : ℕ) : P k := (m : P k) * X k ^ (m - 1)

def jacobianIdeal (k : Type u) [Field k] (m : ℕ) : Ideal (B k m) :=
  Ideal.span {residue m (slope k m)}

abbrev Tangent (k : Type u) [Field k] (m : ℕ) := B k m ⧸ jacobianIdeal k m

abbrev tangentClass (m : ℕ) (q : P k) : Tangent k m :=
  Ideal.Quotient.mk _ (residue m q)

abbrev ε (k : Type u) [Field k] : dual k := TrivSqZeroExt.inr 1

abbrev εP (k : Type u) [Field k] : P (dual k) := MvPolynomial.C (ε k)

abbrev extend (k : Type u) [Field k] : P k →+* P (dual k) :=
  MvPolynomial.map (algebraMap k (dual k))

abbrev reduce (k : Type u) [Field k] : P (dual k) →+* P k :=
  MvPolynomial.map (dual k).residue.toRingHom

def perturbedEquation (m : ℕ) (q : P k) : P (dual k) :=
  X (dual k) ^ m + εP k * extend k q

abbrev Model (m : ℕ) (q : P k) :=
  KoszulFlatDeformationModelsSpec.Model [perturbedEquation m q]

abbrev Deformation (k : Type u) [Field k] (m : ℕ) :=
  MarkedDeformation.{u,u,u,z} (dual k) (B k m)

abbrev Classes (k : Type u) [Field k] (m : ℕ) :=
  MarkedDeformation.Classes.{u,u,u,z} (dual k) (B k m)

/-- The marking on the presented quotient is reduction of coefficients and the variable. -/
def Represents {m : ℕ} (q : P k) (D : Deformation.{u,z} k m) : Prop :=
  ∃ e : ULift.{z} (Model m q) ≃ₐ[dual k] D, ∀ p : P (dual k),
    reduction D (e (ULift.up (Ideal.Quotient.mk _ p))) = residue m (reduce k p)

def Regular : Prop :=
  ∀ {k : Type u} [Field k] {m : ℕ}, 1 ≤ m →
    RingTheory.Sequence.IsRegular (P k) (List.ofFn (equation k m))

def JacobianIdentification : Prop :=
  ∀ {k : Type u} [Field k] (m : ℕ),
    ∃ E : CompleteIntersectionTangentSpace.JacobianCokernel (equation k m) ≃ₗ[B k m] Tangent k m,
      ∀ v : Fin 1 → B k m,
        E ((CompleteIntersectionTangentSpace.jacobian (equation k m)).range.mkQ v) =
          Ideal.Quotient.mk _ (v 0)

abbrev PolynomialFibre (k : Type u) [Field k] (m : ℕ) :=
  Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ m}

def polynomialJacobianIdeal (k : Type u) [Field k] (m : ℕ) : Ideal (PolynomialFibre k m) :=
  Ideal.span {Ideal.Quotient.mk _ ((m : Polynomial k) * Polynomial.X ^ (m - 1))}

def PolynomialPresentations : Prop :=
  ∀ {k : Type u} [Field k] (m : ℕ),
    let e := MvPolynomial.uniqueAlgEquiv k (Fin 1)
    ∃ b : B k m ≃ₐ[k] PolynomialFibre k m,
      (∀ p : P k, b (residue m p) = Ideal.Quotient.mk _ (e p)) ∧
      (∃ t : Tangent k m ≃ₐ[k] PolynomialFibre k m ⧸ polynomialJacobianIdeal k m,
        ∀ p : P k, t (tangentClass m p) = Ideal.Quotient.mk _ (b (residue m p))) ∧
      ∀ q : P k,
        let e' := MvPolynomial.uniqueAlgEquiv (dual k) (Fin 1)
        ∃ d : Model m q ≃ₐ[dual k]
            Polynomial (dual k) ⧸ Ideal.span
              {Polynomial.X ^ m + Polynomial.C (ε k) * Polynomial.map (algebraMap k (dual k)) (e q)},
          ∀ p : P (dual k), d (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (e' p)

def Models : Prop :=
  ∀ {k : Type u} [Field k] {m : ℕ}, 1 ≤ m →
    ∀ q : P k, ∃ D : Deformation.{u,z} k m, Represents q D

/-- The tangent space from the square-zero lift action, pointed at the constant family.
The sign records that the equation sets x^m equal to -εq in its quotient. -/
def Coordinates : Prop :=
  ∀ {k : Type u} [Field k] {m : ℕ}, 1 ≤ m →
    let f := equation k m
    let C := B k m
    let D₀ := CompleteIntersectionTangentSpace.trivial.{u,z} k C
    ∃ (F : Classes.{u,z} k m ≃ CompleteIntersectionTangentSpace.LiftClasses (k := k) C)
      (a : AddTorsor (CompleteIntersectionTangentSpace.TangentModule f)
        (CompleteIntersectionTangentSpace.LiftClasses (k := k) C))
      (E : CompleteIntersectionTangentSpace.TangentModule f ≃ₗ[C] Tangent k m)
      (G : Classes.{u,z} k m ≃ Tangent k m),
      (∀ D L, CompleteIntersectionTangentSpace.Corresponds D L →
        F (MarkedDeformation.classModel D) = liftClass L) ∧
      ActsByReduction (CompleteIntersectionTangentSpace.presentation f) a.toAddAction.toVAdd ∧
      (∀ Y, G Y = E (a.vsub (F Y) (F (MarkedDeformation.classModel D₀)))) ∧
      G (MarkedDeformation.classModel D₀) = 0 ∧
      (∀ q D, Represents q D → G (MarkedDeformation.classModel D) = -tangentClass m q) ∧
      (letI := G.addCommGroup
       letI := G.addEquiv.module k
       ∃ H : Classes.{u,z} k m ≃ₗ[k] Tangent k m, H.toEquiv = G)

def Classification : Prop :=
  ∀ {k : Type u} [Field k] {m : ℕ}, 1 ≤ m →
    (∀ D : Deformation.{u,z} k m, ∃ (q : P k) (D' : Deformation.{u,z} k m),
      Represents q D' ∧ D.Isomorphic D') ∧
    (∀ (q r : P k) (D E : Deformation.{u,z} k m), Represents q D → Represents r E →
      (D.Isomorphic E ↔ tangentClass m (q - r) = 0))

/-- Substitution in the dual-number polynomial ring and multiplication by a unit. -/
def EquationChanges : Prop :=
  ∀ {k : Type u} [Field k] (m : ℕ) (q u v : P k),
    (MvPolynomial.aeval (fun _ : Fin 1 => X (dual k) + εP k * extend k u)
      (perturbedEquation m q) = perturbedEquation m (q + slope k m * u)) ∧
    (IsUnit (1 + εP k * extend k v) ∧
      (1 + εP k * extend k v) * perturbedEquation m q =
        perturbedEquation m (q + X k ^ m * v)) ∧
    tangentClass m (q + slope k m * u) = tangentClass m q ∧
    tangentClass m (q + X k ^ m * v) = tangentClass m q

def BoundaryCases : Prop :=
  ∀ {k : Type u} [Field k],
    Subsingleton (Tangent k 1) ∧
    ∀ m : ℕ, (m : k) = 0 → ∃ E : Tangent k m ≃ₐ[B k m] B k m,
      ∀ q : P k, E (tangentClass m q) = residue m q

end Specs.CommutativeAlgebraNotes.MonomialHypersurfaceDeformations
