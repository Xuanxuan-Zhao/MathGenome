import MathGenome.Internal.Specs.D07.Ch06.SylowDefinition
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Index

/-!
Independent statements for K07.18.frattini_argument, paper.tex:5135–5155.

`P : Sylow p A` is a maximal p-subgroup of the group A, not of G.
Its image `P.map A.subtype` is the same subgroup in the ambient group G.
The upstream Sylow definition entry proves that this library structure
agrees with the finite-cardinality and maximality definitions in the paper.
The normalizer below is taken in G.

The product is a pointwise product of sets, in the order A N_G(P).
`A.subgroupOf N` consists of the elements of N whose ambient values belong
to A, so its index in N is precisely [N : N ∩ A]. Finiteness is explicit
in every index/cardinality assertion. No nontriviality or divisibility of
|A| by p is assumed.
-/

namespace Specs.D07.Ch18.FrattiniArgument

open scoped Pointwise
universe u

/-- Every ambient element is a product of an element of A and a normalizer element. -/
def NormalProduct : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    (p : ℕ), p.Prime → ∀ P : Sylow p A,
      (Set.univ : Set G) = (A : Set G) * 
      (Subgroup.normalizer (P.map A.subtype : Set G) : Set G)

/-- The equality [G : A] = [N_G(P) : N_G(P) ∩ A]. -/
def IndexFormula : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    (p : ℕ), p.Prime → ∀ P : Sylow p A,
      A.index = (A.subgroupOf (Subgroup.normalizer (P.map A.subtype : Set G))).index

/-- The ambient index divides the order of the ambient normalizer. -/
def IndexDividesNormalizerOrder : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    (p : ℕ), p.Prime → ∀ P : Sylow p A,
      A.index ∣ Nat.card (Subgroup.normalizer (P.map A.subtype : Set G))

/-- Primes absent from |A| give the trivial Sylow and full ambient normalizer. -/
def NormalizerOfNotDvdCard : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    (p : ℕ), p.Prime → ∀ P : Sylow p A,
      ¬ p ∣ Nat.card A →
        (P : Subgroup A) = ⊥ ∧ Subgroup.normalizer (P.map A.subtype : Set G) = ⊤

end Specs.D07.Ch18.FrattiniArgument
