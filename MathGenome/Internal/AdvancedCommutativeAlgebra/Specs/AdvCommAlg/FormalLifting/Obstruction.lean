import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.TorsorOfLifts
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Conormal
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.JacobianPresentation

/-! FL-06. An extension packages an arbitrary surjection P → B, together with
its compatible A-algebra structures. Its Cotangent is I/I² and its
CotangentSpace is B ⊗[P] Ω[P/A]. No finiteness or nonzero hypotheses occur. -/
namespace Specs.AdvCommAlg.FormalLifting.Obstruction

open Specs.AdvCommAlg.Differentials.SquareZero
open TensorProduct
universe u v w z
noncomputable section

section General
variable {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

abbrev presentationMap (E : Algebra.Extension.{z} A B) : E.Ring →ₐ[A] B :=
  IsScalarTower.toAlgHom A E.Ring B

/-- δ* is precomposition by the actual conormal map. -/
def deltaStar (E : Algebra.Extension.{z} A B) (N : Ideal C) (hN : N ^ 2 = ⊥)
    (u : B →ₐ[A] C ⧸ N) :=
  letI := idealModule N hN u
  { toFun := fun h : E.CotangentSpace →ₗ[B] N => h.comp E.cotangentComplex
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl :
      (E.CotangentSpace →ₗ[B] N) →ₗ[B] (E.Cotangent →ₗ[B] N) }

/-- There is a lift on the presenting algebra whenever it is formally smooth. -/
def presentationLift : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  ∀ (E : Algebra.Extension.{z} A B),
  formallySmoothValue A E.Ring → ∀ (N : Ideal C) (hN : N ^ 2 = ⊥)
    (u : B →ₐ[A] C ⧸ N), Nonempty (Lifts N (u.comp (presentationMap E)))

/-- Evaluation on I descends to a B-linear obstruction. Its image in the
literal Hom cokernel is independent of the presenting lift, and zero exactly
when the original map lifts. A chosen presenting lift suffices; the preceding
statement supplies one under formal smoothness. -/
def obstructionTheory : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  ∀ (E : Algebra.Extension.{z} A B)
    (N : Ideal C) (hN : N ^ 2 = ⊥) (u : B →ₐ[A] C ⧸ N),
  letI := idealModule N hN u
  ∃ o : Lifts N (u.comp (presentationMap E)) → (E.Cotangent →ₗ[B] N),
    (∀ φ f, (o φ (Algebra.Extension.Cotangent.mk f) : C) = φ.1 f.val) ∧
    (∀ φ ψ, (LinearMap.range (deltaStar E N hN u)).mkQ (o φ) =
      (LinearMap.range (deltaStar E N hN u)).mkQ (o ψ)) ∧
    (∀ φ, (LinearMap.range (deltaStar E N hN u)).mkQ (o φ) = 0 ↔
      Nonempty (Lifts N u))

/-- The source theorem specialized to every specified surjective tower,
using exactly the shared conormal object and its given scalar structures. -/
def surjectivePresentation : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (P : Type z) [CommRing P] [Algebra A P] [Algebra P B] [IsScalarTower A P B]
    (h : Function.Surjective (algebraMap P B)),
  formallySmoothValue A P → ∀ (N : Ideal C) (hN : N ^ 2 = ⊥) (u : B →ₐ[A] C ⧸ N),
  let E := Specs.AdvCommAlg.Differentials.conormalExtension A P B h
  Nonempty (Lifts N (u.comp (presentationMap E))) ∧
    (letI := idealModule N hN u
     ∃ o : Lifts N (u.comp (presentationMap E)) → (E.Cotangent →ₗ[B] N),
       (∀ φ f, (o φ (Algebra.Extension.Cotangent.mk f) : C) = φ.1 f.val) ∧
       (∀ φ ψ, (LinearMap.range (deltaStar E N hN u)).mkQ (o φ) =
         (LinearMap.range (deltaStar E N hN u)).mkQ (o ψ)) ∧
       (∀ φ, (LinearMap.range (deltaStar E N hN u)).mkQ (o φ) = 0 ↔
         Nonempty (Lifts N u)))

end General

section Finite
variable {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- First-order Taylor's formula, with the coefficients acting through u.
It is stated for every polynomial, and thus in particular every relation. -/
def polynomialCorrection : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  ∀ (n m : ℕ)
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (N : Ideal C) (hN : N ^ 2 = ⊥) (u : B →ₐ[A] C ⧸ N)
    (x : Fin n → C) (hx : ∀ i, Ideal.Quotient.mk N (x i) = u (P.val i)),
  letI := idealModule N hN u
  ∀ (t : Fin n → N) (f : MvPolynomial (Fin n) A),
    MvPolynomial.aeval (fun i => x i + (t i : C)) f =
      MvPolynomial.aeval x f +
        ((∑ i : Fin n, MvPolynomial.aeval P.val (MvPolynomial.pderiv i f) • t i : N) : C)

/-- The corrected variable values define a lift precisely when all displayed
linear equations hold. Equality is in C using N's injective inclusion. -/
def finiteLiftingEquation : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  ∀ (n m : ℕ)
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (N : Ideal C) (hN : N ^ 2 = ⊥) (u : B →ₐ[A] C ⧸ N)
    (x : Fin n → C) (hx : ∀ i, Ideal.Quotient.mk N (x i) = u (P.val i)),
  letI := idealModule N hN u
  ∀ (t : Fin n → N),
    (∃ g : Lifts N u, ∀ i, g.1 (P.val i) = x i + (t i : C)) ↔
      ∀ j : Fin m,
        ((∑ i : Fin n,
          MvPolynomial.aeval P.val (MvPolynomial.pderiv i (P.relation j)) • t i : N) : C) =
            -MvPolynomial.aeval x (P.relation j)

/-- The relation errors lie in N, and existence of an arbitrary lift is
equivalent to solvability of the finite linear system. -/
def finiteSolvability : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (n m : ℕ) (P : Algebra.Presentation A B (Fin n) (Fin m))
    (N : Ideal C) (hN : N ^ 2 = ⊥) (u : B →ₐ[A] C ⧸ N)
    (x : Fin n → C) (hx : ∀ i, Ideal.Quotient.mk N (x i) = u (P.val i)),
  letI := idealModule N hN u
  (∀ j, MvPolynomial.aeval x (P.relation j) ∈ N) ∧
    (Nonempty (Lifts N u) ↔ ∃ t : Fin n → N, ∀ j : Fin m,
      ((∑ i : Fin n,
        MvPolynomial.aeval P.val (MvPolynomial.pderiv i (P.relation j)) • t i : N) : C) =
          -MvPolynomial.aeval x (P.relation j))

end Finite
end
end Specs.AdvCommAlg.FormalLifting.Obstruction
