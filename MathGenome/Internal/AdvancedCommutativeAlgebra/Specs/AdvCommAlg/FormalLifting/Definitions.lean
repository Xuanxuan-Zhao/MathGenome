import Mathlib.RingTheory.Etale.Basic

/-! Independent statements for FL-01 (paper.tex, Definition 2.1).
All rings are commutative and unital; no nontriviality or finiteness is imposed.
The quotient algebra structure is induced by the given A-algebra structure.
The definitions test in the universe containing A and B, as in Mathlib.
The three reduction statements below extend each condition to test algebras
in every universe, so the choice of testing universe imposes no size condition.
-/
namespace Specs.AdvCommAlg.FormalLifting

universe u v w

/-- Reduction of an A-algebra homomorphism modulo an ideal. -/
def reductionMap {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (N : Ideal C) : (B →ₐ[A] C) → (B →ₐ[A] C ⧸ N) :=
  (Ideal.Quotient.mkₐ A N).comp

def propertyType := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B], Prop

/-- Existence of lifts through every square-zero quotient. -/
def formallySmoothValue : propertyType.{u,v} :=
  fun A B _ _ _ => ∀ {C : Type (max u v)} [CommRing C] [Algebra A C]
    (N : Ideal C), N ^ 2 = ⊥ → Function.Surjective (reductionMap (A := A) (B := B) N)

/-- Uniqueness of lifts through every square-zero quotient. -/
def formallyUnramifiedValue : propertyType.{u,v} :=
  fun A B _ _ _ => ∀ {C : Type (max u v)} [CommRing C] [Algebra A C]
    (N : Ideal C), N ^ 2 = ⊥ → Function.Injective (reductionMap (A := A) (B := B) N)

/-- Existence and uniqueness of lifts through every square-zero quotient. -/
def formallyEtaleValue : propertyType.{u,v} :=
  fun A B _ _ _ => ∀ {C : Type (max u v)} [CommRing C] [Algebra A C]
    (N : Ideal C), N ^ 2 = ⊥ → Function.Bijective (reductionMap (A := A) (B := B) N)

def formallySmoothIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  formallySmoothValue A B ↔ Algebra.FormallySmooth A B

def formallyUnramifiedIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  formallyUnramifiedValue A B ↔ Algebra.FormallyUnramified A B

def formallyEtaleIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  formallyEtaleValue A B ↔ Algebra.FormallyEtale A B

def smoothReduction : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  formallySmoothValue A B → ∀ (N : Ideal C), N ^ 2 = ⊥ →
    Function.Surjective (reductionMap (A := A) (B := B) N)

def unramifiedReduction : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  formallyUnramifiedValue A B → ∀ (N : Ideal C), N ^ 2 = ⊥ →
    Function.Injective (reductionMap (A := A) (B := B) N)

def etaleReduction : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  formallyEtaleValue A B → ∀ (N : Ideal C), N ^ 2 = ⊥ →
    Function.Bijective (reductionMap (A := A) (B := B) N)

end Specs.AdvCommAlg.FormalLifting
