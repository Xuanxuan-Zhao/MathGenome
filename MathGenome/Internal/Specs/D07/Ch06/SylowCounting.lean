import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs

/-!
Independent statements for `K07.06.sylow_counting`, paper.tex:1048–1058.
The number being counted is explicitly the number of distinct subgroups
of order p^a, under the source's factorization |G| = p^a m, p ∤ m.
All groups are finite, p is prime, and a = 0 is permitted.
The normalizer index is the number of cosets; normality is not assumed.
-/

namespace Specs.D07.Ch06.SylowCounting

universe u

/-- The number of Sylow subgroups is the index of the normalizer of any one. -/
def CountEqIndexNormalizer : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a m : ℕ),
    p.Prime → Nat.card G = p ^ a * m → ¬ p ∣ m →
    ∀ P : Subgroup G, Nat.card P = p ^ a →
      Nat.card {Q : Subgroup G // Nat.card Q = p ^ a} =
        (Subgroup.normalizer (P : Set G)).index

/-- The number of Sylow subgroups divides the prime-to-p factor of |G|. -/
def CountDvdCofactor : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a m : ℕ),
    p.Prime → Nat.card G = p ^ a * m → ¬ p ∣ m →
      Nat.card {Q : Subgroup G // Nat.card Q = p ^ a} ∣ m

/-- The number of Sylow subgroups is congruent to one modulo p. -/
def CountModEqOne : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a m : ℕ),
    p.Prime → Nat.card G = p ^ a * m → ¬ p ∣ m →
      Nat.ModEq p (Nat.card {Q : Subgroup G // Nat.card Q = p ^ a}) 1

end Specs.D07.Ch06.SylowCounting
