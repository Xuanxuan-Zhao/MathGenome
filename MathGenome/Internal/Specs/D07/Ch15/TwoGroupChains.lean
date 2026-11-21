import Mathlib.GroupTheory.Index
import Mathlib.Order.Fin.Basic

/-!
Independent statement of `lem:two-group-chains` (paper.tex:4505–4513).
The finite group need not be commutative and the starting subgroup need
not be normal. Exponent zero and the chain of length zero are allowed.
`H.relIndex K` is the index of `H.subgroupOf K` in `K`; the strict
inclusions below ensure that this is precisely [K : H].
-/

namespace Specs.D07.Ch15.TwoGroupChains

universe u

/-- Every subgroup of a finite group of 2-power order admits a strict
finite chain to the whole group, with relative index two at every step. -/
def ChainExists : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    (∃ a : ℕ, Nat.card G = 2 ^ a) → ∀ H : Subgroup G,
      ∃ (s : ℕ) (C : Fin (s + 1) → Subgroup G),
        C 0 = H ∧ C (Fin.last s) = ⊤ ∧ StrictMono C ∧
          ∀ i : Fin s, (C i.castSucc).relIndex (C i.succ) = 2

end Specs.D07.Ch15.TwoGroupChains
