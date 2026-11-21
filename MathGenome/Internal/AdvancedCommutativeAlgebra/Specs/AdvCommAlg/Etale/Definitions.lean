import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions

/-! Independent specification of ET-01, paper.tex, Definition 4.1.
The finite type and finite presentation conditions are those for algebras.
No nontriviality or Noetherian hypothesis is imposed.
-/
namespace Specs.AdvCommAlg.Etale

universe u v w

open Specs.AdvCommAlg.FormalLifting

/-- Use the canonical Mathlib étale predicate. -/
def etaleValue : propertyType.{u,v} := fun A B _ _ _ => Algebra.Etale A B

/-- Use the canonical Mathlib finite-type unramified predicate. -/
def unramifiedValue : propertyType.{u,v} := fun A B _ _ _ => Algebra.Unramified A B

/-- The stronger finiteness condition is recorded separately. -/
def finitelyPresentedUnramifiedValue : propertyType.{u,v} := fun A B _ _ _ =>
  Algebra.FinitePresentation A B ∧ Algebra.Unramified A B

def etaleIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  etaleValue A B ↔ Algebra.FinitePresentation A B ∧ formallyEtaleValue A B

def unramifiedIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  unramifiedValue A B ↔ Algebra.FiniteType A B ∧ formallyUnramifiedValue A B

def finitelyPresentedUnramifiedIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  finitelyPresentedUnramifiedValue A B ↔
    Algebra.FinitePresentation A B ∧ formallyUnramifiedValue A B

def finitelyPresentedUnramifiedImpliesUnramified : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  finitelyPresentedUnramifiedValue A B → unramifiedValue A B

/-- Test algebras may lie in an arbitrary universe and may be zero rings. -/
def etaleReduction : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  etaleValue A B → ∀ (N : Ideal C), N ^ 2 = ⊥ →
    Function.Bijective (reductionMap (A := A) (B := B) N)

def unramifiedReduction : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  unramifiedValue A B → ∀ (N : Ideal C), N ^ 2 = ⊥ →
    Function.Injective (reductionMap (A := A) (B := B) N)

end Specs.AdvCommAlg.Etale
