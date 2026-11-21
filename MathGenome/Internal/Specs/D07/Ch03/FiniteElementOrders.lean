import MathGenome.Internal.Specs.D07.Ch02.CyclicModelsIsomorphism
import MathGenome.Internal.Specs.D07.Ch03.Lagrange

/-!
Independent statements for K07.03.finite_element_orders
(paper.tex:611–619). Natural cardinalities are used only for finite groups.
`orderOf` denotes the canonical element order; its positivity explicitly
excludes the zero encoding of infinite order. The model `C_p` is the additive
residue group `ZMod p`, written multiplicatively via the standard type tag.
No commutativity or nontriviality assumption is added to the ambient group.
-/

namespace Specs.D07.Ch03.FiniteElementOrders

universe u

def OrderPositive : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (x : G), 0 < orderOf x

def OrderDividesCard : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (x : G), orderOf x ∣ Nat.card G

def PowerCardEqOne : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (x : G), x ^ Nat.card G = 1

def PrimeNonidentityOrder : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ),
    p.Prime → Nat.card G = p → ∀ x : G, x ≠ 1 → orderOf x = p

def PrimeNonidentityGenerates : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ),
    p.Prime → Nat.card G = p → ∀ x : G, x ≠ 1 → Subgroup.zpowers x = ⊤

def PrimeIsomorphicCyclicModel : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ),
    p.Prime → Nat.card G = p → Nonempty (G ≃* Multiplicative (ZMod p))

end Specs.D07.Ch03.FiniteElementOrders
