import MathGenome.Internal.Specs.D07.Ch02.SymmetricOrder
import Mathlib.Algebra.Group.Hom.Defs

/-!
Independent specification of `K07.02.cayley` (paper.tex:560–567).
An embedding is an injective group homomorphism. Permutations use the
canonical rightmost-first composition from `PermutationConvention`.
-/

namespace Specs.D07.Ch02.Cayley

universe u

/-- Left translations embed every group in the permutations of its carrier.
There is no finiteness, commutativity, or nontriviality hypothesis. -/
def CayleyEmbedding : Prop :=
  ∀ (G : Type u) [Group G],
    ∃ ρ : G →* Equiv.Perm G,
      Function.Injective ρ ∧ ∀ (g x : G), ρ g x = g * x

/-- A group of finite order `n` embeds in `S_n`. The explicit finiteness
hypothesis ensures that `Nat.card` denotes the actual finite order. -/
def FiniteCayleyEmbedding : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (n : ℕ), Nat.card G = n →
    ∃ ρ : G →* Equiv.Perm (Fin n), Function.Injective ρ

end Specs.D07.Ch02.Cayley
