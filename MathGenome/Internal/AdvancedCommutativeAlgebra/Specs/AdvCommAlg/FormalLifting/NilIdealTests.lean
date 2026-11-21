import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! Independent statements for FL-18, paper.tex:903–927.
The ideal is nil element by element; there is no common nilpotence exponent.
Existence requires finite presentation, whereas uniqueness only requires finite
type. Test algebras have arbitrary universe and may be zero rings.
-/
namespace Specs.AdvCommAlg.FormalLifting

universe u v w

/-- A finitely presented formally smooth algebra lifts through nil ideals. -/
def smoothNilReduction : Prop :=
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra.FinitePresentation A B],
    formallySmoothValue A B → ∀ (N : Ideal C),
      (∀ x ∈ N, IsNilpotent x) →
      Function.Surjective (reductionMap (A := A) (B := B) N)

/-- Two maps from a finite-type formally unramified algebra agreeing modulo a
nil ideal are equal. -/
def unramifiedNilReduction : Prop :=
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra.FiniteType A B],
    formallyUnramifiedValue A B → ∀ (N : Ideal C),
      (∀ x ∈ N, IsNilpotent x) →
      Function.Injective (reductionMap (A := A) (B := B) N)

/-- A finitely presented formally étale algebra has unique lifts through every
nil ideal. -/
def etaleNilReduction : Prop :=
  ∀ {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra.FinitePresentation A B],
    formallyEtaleValue A B → ∀ (N : Ideal C),
      (∀ x ∈ N, IsNilpotent x) →
      Function.Bijective (reductionMap (A := A) (B := B) N)

end Specs.AdvCommAlg.FormalLifting
