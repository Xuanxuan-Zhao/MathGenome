import MathGenome.Internal.Specs.D07.Ch18.CentralSeries
import MathGenome.Internal.Specs.D07.Ch18.MixedCommutators

/-!
Independent specification of `K07.18.nilpotence_criteria`, paper.tex:4997–5029.

The upper and lower terms are the canonical objects of the prerequisite Specs.
`classAtMostValue` is upper termination, with no default numerical convention.
`hasClassValue` says that this termination length is the least one. Thus it is
false at every length for a nonnilpotent group.

A length-c chain is represented by a sequence on ℕ, with conditions only on
indices 0,…,c. Its values outside that interval are irrelevant. Adjacent
inclusions express precisely the finite increasing chain; every term in that
interval must be normal in the ambient group. All comparisons involving natural
subtraction have the source's explicit bounds.

The counterexample to reverse interlacing is allocated separately to
`K07.18.nilpotence_examples.reverse_interlacing_failure`.
-/

namespace Specs.D07.Ch18.NilpotenceCriteria

open Specs.D07.Ch18.CentralSeries

universe u

def ClassPredicateType := (G : Type u) → [Group G] → ℕ → Prop

def classAtMostValue (G : Type u) [Group G] (c : ℕ) : Prop :=
  upperValue G c = ⊤

def hasClassValue (G : Type u) [Group G] (c : ℕ) : Prop :=
  classAtMostValue G c ∧ ∀ d : ℕ, classAtMostValue G d → c ≤ d

def ChainPredicateType :=
  (G : Type u) → [Group G] → ℕ → (ℕ → Subgroup G) → Prop

def centralChainValue (G : Type u) [Group G] (c : ℕ) (C : ℕ → Subgroup G) : Prop :=
  C 0 = ⊥ ∧ C c = ⊤ ∧
    (∀ i : ℕ, i ≤ c → (C i).Normal) ∧
    (∀ i : ℕ, i < c → C i ≤ C (i + 1)) ∧
    (∀ i : ℕ, i < c → ⁅(⊤ : Subgroup G), C (i + 1)⁆ ≤ C i)

def ClassAtMostIffUpper : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ),
    classAtMostValue G c ↔ upperValue G c = ⊤

def ClassAtMostIffLower : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ),
    classAtMostValue G c ↔ lowerValue G (c + 1) = ⊥

def ClassAtMostIffCentralChain : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ),
    classAtMostValue G c ↔ ∃ C : ℕ → Subgroup G, centralChainValue G c C

def ChainMonotone : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ) (C : ℕ → Subgroup G),
    centralChainValue G c C →
      ∀ i j : ℕ, i ≤ j → j ≤ c → C i ≤ C j

def ChainLeUpper : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ) (C : ℕ → Subgroup G),
    centralChainValue G c C → ∀ i : ℕ, i ≤ c → C i ≤ upperValue G i

def LowerLeChain : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ) (C : ℕ → Subgroup G),
    centralChainValue G c C →
      ∀ j : ℕ, 1 ≤ j → j ≤ c + 1 → lowerValue G j ≤ C (c + 1 - j)

def UpperIsCentralChain : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ),
    classAtMostValue G c → centralChainValue G c (upperValue G)

def ReversedLowerIsCentralChain : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ),
    lowerValue G (c + 1) = ⊥ →
      centralChainValue G c (fun i => lowerValue G (c + 1 - i))

def LowerLeUpper : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ),
    classAtMostValue G c →
      ∀ i : ℕ, i ≤ c → lowerValue G (c + 1 - i) ≤ upperValue G i

def NilpotentIffExistsBound : Prop :=
  ∀ (G : Type u) [Group G],
    Group.IsNilpotent G ↔ ∃ c : ℕ, classAtMostValue G c

def HasClassExistsIffNilpotent : Prop :=
  ∀ (G : Type u) [Group G],
    (∃ c : ℕ, hasClassValue G c) ↔ Group.IsNilpotent G

def HasClassUnique : Prop :=
  ∀ (G : Type u) [Group G] (c d : ℕ),
    hasClassValue G c → hasClassValue G d → c = d

def HasClassIffLibraryClass : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ),
    hasClassValue G c ↔ Group.IsNilpotent G ∧ Group.nilpotencyClass G = c

def HasClassIffLeastLowerLength : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ),
    hasClassValue G c ↔
      lowerValue G (c + 1) = ⊥ ∧
        ∀ d : ℕ, lowerValue G (d + 1) = ⊥ → c ≤ d

def LeastTerminationLengthsAgree : Prop :=
  ∀ (G : Type u) [Group G] (c d : ℕ),
    hasClassValue G c →
      (lowerValue G (d + 1) = ⊥ ∧
        ∀ e : ℕ, lowerValue G (e + 1) = ⊥ → d ≤ e) → c = d

def ClassZeroIffSubsingleton : Prop :=
  ∀ (G : Type u) [Group G], hasClassValue G 0 ↔ Subsingleton G

def ClassOneIffNontrivialAbelian : Prop :=
  ∀ (G : Type u) [Group G],
    hasClassValue G 1 ↔ Nontrivial G ∧ ∀ x y : G, x * y = y * x

end Specs.D07.Ch18.NilpotenceCriteria
