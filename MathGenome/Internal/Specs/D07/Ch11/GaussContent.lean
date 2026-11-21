import MathGenome.Internal.Specs.D07.Ch11.ContentPrimitive

/-!
Independent statements for K07.11.gauss_content, paper.tex:2521–2556.
The coefficient ring is a UFD, with no chosen gcd structure required.
`IsContent` is the upstream universal divisibility predicate, so the main
association statement quantifies over every choice of the three contents.
The final equality uses a multiplicative normalization explicitly.
-/

universe u

namespace Specs.D07.Ch11.GaussContent

open Polynomial Specs.D07.Ch11.ContentPrimitive

def PrimitiveProduct : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f g : R[X]), f.IsPrimitive → g.IsPrimitive → (f * g).IsPrimitive

/-- All polynomials, including zero, and all choices of their contents. -/
def ContentProductAssociated : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f g : R[X]) (a b c : R),
    IsContent f a → IsContent g b → IsContent (f * g) c → Associated c (a * b)

/-- Equivalently, the product of any two content representatives is itself
a content representative of the product polynomial. -/
def ProductIsContent : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f g : R[X]) (a b : R),
    IsContent f a → IsContent g b → IsContent (f * g) (a * b)

/-- The particular internal choice of the upstream content definition also
satisfies association, without assuming that its normalization is strong. -/
def ChosenContentProductAssociated : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f g : R[X]), Associated (content (f * g)) (content f * content g)

/-- Literal equality for the library content computed with an explicitly
multiplicative normalization of associates. -/
def NormalizedContentProduct : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [StrongNormalizedGCDMonoid R] (f g : R[X]),
    (f * g).content = f.content * g.content

end Specs.D07.Ch11.GaussContent
