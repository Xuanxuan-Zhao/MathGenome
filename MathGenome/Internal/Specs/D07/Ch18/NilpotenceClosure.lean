import MathGenome.Internal.Specs.D07.Ch18.NilpotenceCriteria
import MathGenome.Internal.Specs.D07.Ch04.DirectProducts

/-!
Independent specification of `K07.18.nilpotence_closure`, paper.tex:5031–5054.

All bounds use the canonical `classAtMostValue`, namely Z_c(G) = G.
Exact class uses `hasClassValue`, so none of these statements interprets the
default numerical class of a nonnilpotent group as a nilpotence assertion.
Homomorphic images are represented both by a surjective homomorphism and by
the range of an arbitrary homomorphism. No finiteness of the groups is assumed.

Products use the canonical Cartesian product from DirectProducts, with a finite
index type only. The finite supremum on ℕ is the maximum of the factor classes,
with empty supremum zero. The final clause states the empty case independently.
-/

namespace Specs.D07.Ch18.NilpotenceClosure

open Specs.D07.Ch18.NilpotenceCriteria

universe u v w

def SubgroupClassAtMost : Prop :=
  ∀ (G : Type u) [Group G] (H : Subgroup G) (c : ℕ),
    classAtMostValue G c → classAtMostValue H c

def SurjectiveClassAtMost : Prop :=
  ∀ (G : Type u) (Q : Type v) [Group G] [Group Q] (f : G →* Q),
    Function.Surjective f → ∀ c : ℕ,
      classAtMostValue G c → classAtMostValue Q c

def RangeClassAtMost : Prop :=
  ∀ (G : Type u) (Q : Type v) [Group G] [Group Q] (f : G →* Q) (c : ℕ),
    classAtMostValue G c → classAtMostValue f.range c

def ProdClassAtMostIff : Prop :=
  ∀ (A : Type u) (B : Type v) [Group A] [Group B] (c : ℕ),
    classAtMostValue (A × B) c ↔ classAtMostValue A c ∧ classAtMostValue B c

def ProdHasClass : Prop :=
  ∀ (A : Type u) (B : Type v) [Group A] [Group B] (a b : ℕ),
    hasClassValue A a → hasClassValue B b → hasClassValue (A × B) (max a b)

def FiniteProductClassAtMostIff : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)] [Finite I] (c : ℕ),
    classAtMostValue (∀ i, G i) c ↔ ∀ i, classAtMostValue (G i) c

def FiniteProductNilpotent : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)] [Finite I],
    (∀ i, Group.IsNilpotent (G i)) → Group.IsNilpotent (∀ i, G i)

def FiniteProductHasClass : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)] [Fintype I] (c : I → ℕ),
    (∀ i, hasClassValue (G i) (c i)) →
      hasClassValue (∀ i, G i) (Finset.univ.sup c)

def EmptyProductHasClassZero : Prop :=
  ∀ (I : Type u) (G : I → Type v) [∀ i, Group (G i)] [IsEmpty I],
    hasClassValue (∀ i, G i) 0

end Specs.D07.Ch18.NilpotenceClosure
