import MathGenome.Internal.Specs.D07.Ch08.IdealProduct
import MathGenome.Internal.Specs.D07.Ch09.Comaximal

/-!
Independent specification of K07.09.product_intersection,
paper.tex:1719–1735. The chapter assumes commutativity from line 1631.
The canonical ideal product is identified with finite sums of products
in the upstream IdealProduct specification; meet is set intersection.
Comaximality is the shared predicate that the sum is the whole ring.
No properness, domain, or nontriviality hypothesis is required.

Finite families are indexed by a finite subset of an arbitrary type,
with a whole-finite-type formulation as well. The empty family is
included: the empty ideal product and intersection are both the top ideal.
-/

universe u v

namespace Specs.D07.Ch09.ProductIntersection

open scoped BigOperators

/-- The product of two comaximal ideals is their intersection. -/
def BinaryProductIntersection : Prop :=
  ∀ (R : Type u) [CommRing R] (I J : Ideal R),
    Comaximal.comaximalPredicateValue I J → I * J = I ⊓ J

/-- Products and intersections agree for every finite pairwise comaximal
family, including the empty family. Pairwise refers to distinct indices. -/
def FiniteProductIntersection : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) (s : Finset ι) (I : ι → Ideal R),
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Comaximal.comaximalPredicateValue (I i) (I j)) →
      (∏ i ∈ s, I i) = ⨅ i ∈ s, I i

/-- In particular, a family on any finite index type has product equal
to its intersection when its ideals are pairwise comaximal. -/
def IndexedProductIntersection : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Fintype ι] (I : ι → Ideal R),
    (∀ i j, i ≠ j → Comaximal.comaximalPredicateValue (I i) (I j)) →
      (∏ i, I i) = ⨅ i, I i

end Specs.D07.Ch09.ProductIntersection
