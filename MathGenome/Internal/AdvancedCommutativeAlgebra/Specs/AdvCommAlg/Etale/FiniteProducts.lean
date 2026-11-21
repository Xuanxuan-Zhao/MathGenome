import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.Algebra.Algebra.Pi

/-! Independent statements for ET-17 (paper.tex:1987–1997).
The products use the canonical componentwise algebra structure. The finite
index type may be empty, and all rings, including the base, may be zero. -/
namespace Specs.AdvCommAlg.Etale

universe u v w

/-- A finite product is étale if and only if each factor is étale. -/
def etaleFiniteProducts : Prop :=
  ∀ (A : Type u) (ι : Type v) (B : ι → Type w)
    [CommRing A] [Finite ι] [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)],
    etaleValue A (∀ i, B i) ↔ ∀ i, etaleValue A (B i)

/-- The empty product is étale over its specified base. -/
def etaleEmptyProduct : Prop :=
  ∀ (A : Type u) (ι : Type v) (B : ι → Type w)
    [CommRing A] [IsEmpty ι] [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)],
    etaleValue A (∀ i, B i)

/-- The zero algebra is étale, independently of its representation. -/
def etaleZeroAlgebra : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [Subsingleton B], etaleValue A B

end Specs.AdvCommAlg.Etale
