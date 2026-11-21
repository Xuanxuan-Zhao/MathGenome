import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions

/-! Independent statements for paper.tex, res:FL-02 (lines 505–516).
`IsNilpotent N` means that `N ^ m = 0` for some natural number `m`;
for ideals, zero is the bottom ideal. There is no bound on this exponent.
The equivalences use the testing universe of FL-01. The reduction statements
also cover test algebras in every universe. All rings, including zero rings,
are allowed, with their specified algebra structures.
-/
namespace Specs.AdvCommAlg.FormalLifting

universe u v w

/-- Existence for square-zero quotients is equivalent to existence for all
nilpotent quotients. -/
def smoothNilpotentIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  formallySmoothValue A B ↔
    ∀ {C : Type (max u v)} [CommRing C] [Algebra A C] (N : Ideal C),
      IsNilpotent N → Function.Surjective (reductionMap (A := A) (B := B) N)

/-- Uniqueness for square-zero quotients is equivalent to uniqueness for all
nilpotent quotients. -/
def unramifiedNilpotentIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  formallyUnramifiedValue A B ↔
    ∀ {C : Type (max u v)} [CommRing C] [Algebra A C] (N : Ideal C),
      IsNilpotent N → Function.Injective (reductionMap (A := A) (B := B) N)

/-- Bijectivity for square-zero quotients is equivalent to bijectivity for all
nilpotent quotients. -/
def etaleNilpotentIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  formallyEtaleValue A B ↔
    ∀ {C : Type (max u v)} [CommRing C] [Algebra A C] (N : Ideal C),
      IsNilpotent N → Function.Bijective (reductionMap (A := A) (B := B) N)

/-- Nilpotent existence tests in an arbitrary universe. -/
def smoothNilpotentReduction : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  formallySmoothValue A B → ∀ (N : Ideal C), IsNilpotent N →
    Function.Surjective (reductionMap (A := A) (B := B) N)

/-- Nilpotent uniqueness tests in an arbitrary universe. -/
def unramifiedNilpotentReduction : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  formallyUnramifiedValue A B → ∀ (N : Ideal C), IsNilpotent N →
    Function.Injective (reductionMap (A := A) (B := B) N)

/-- Nilpotent bijectivity tests in an arbitrary universe. -/
def etaleNilpotentReduction : Prop := ∀ {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
  formallyEtaleValue A B → ∀ (N : Ideal C), IsNilpotent N →
    Function.Bijective (reductionMap (A := A) (B := B) N)

end Specs.AdvCommAlg.FormalLifting
