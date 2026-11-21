import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions

/-! Independent statements for SM-14, paper.tex:1408–1423.
Products carry the componentwise ring and algebra structures. No factor,
base, or index type is required to be nonempty or nontrivial. -/
namespace Specs.AdvCommAlg.Smooth

universe u v w

/-- A finite product is smooth exactly when all its factors are smooth. -/
def smoothFiniteProducts : Prop :=
  ∀ (A : Type u) (T : Type w) (B : T → Type v)
    [CommRing A] [Finite T] [∀ t, CommRing (B t)] [∀ t, Algebra A (B t)],
    smoothValue A (∀ t, B t) ↔ ∀ t, smoothValue A (B t)

/-- The empty product, a zero algebra, is smooth. -/
def smoothEmptyProduct : Prop :=
  ∀ (A : Type u) (T : Type w) (B : T → Type v)
    [CommRing A] [IsEmpty T] [∀ t, CommRing (B t)] [∀ t, Algebra A (B t)],
    smoothValue A (∀ t, B t)

/-- Smoothness of the zero algebra is independent of its representation. -/
def smoothZeroAlgebra : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [Subsingleton B], smoothValue A B

end Specs.AdvCommAlg.Smooth
