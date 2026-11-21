import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions

/-! Independent statements for SM-01, paper.tex:939–950.
All commutative unital bases and algebras, including the zero ring, are allowed.
The lifting predicate is the common one from FL-01. Its arbitrary-universe
version is also recorded below.
-/
namespace Specs.AdvCommAlg.Smooth

universe u v w

def smoothType := FormalLifting.propertyType.{u,v}

/-- Mathlib's canonical smoothness predicate. -/
def smoothValue : smoothType.{u,v} := fun A B _ _ _ => Algebra.Smooth A B

def smoothIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  smoothValue A B ↔
    Algebra.FinitePresentation A B ∧ FormalLifting.formallySmoothValue A B

/-- Finite presentation is a quotient by finitely many equations in finitely
many variables, over the specified base, rather than merely finite type. -/
def finitePresentationIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  Algebra.FinitePresentation A B ↔
    ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) A),
      Nonempty (B ≃ₐ[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)))

def smoothPresentationIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  smoothValue A B ↔
    (∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) A),
      Nonempty (B ≃ₐ[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)))) ∧
    (∀ {C : Type (max u v)} [CommRing C] [Algebra A C]
      (N : Ideal C), N ^ 2 = ⊥ →
      Function.Surjective (FormalLifting.reductionMap (A := A) (B := B) N))

/-- The lifting consequence has no restriction on the universe of test rings. -/
def smoothReduction : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  smoothValue A B → ∀ (N : Ideal C), N ^ 2 = ⊥ →
    Function.Surjective (FormalLifting.reductionMap (A := A) (B := B) N)

end Specs.AdvCommAlg.Smooth
