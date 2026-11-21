import MathGenome.Internal.ExtremalOptimization.Specs.P205.Ramsey.Infinite

universe u

namespace P205.Ramsey

/-- Every coloring on an arbitrary `N`-point ground set has an `m`-point
homogeneous subset. The ground set is a finset in an arbitrary ambient type. -/
def RamseyProperty (k r m N : ℕ) : Prop :=
  ∀ (X : Type u) (S : Finset X), S.card = N →
    ∀ c : KSubsets X k → Fin r,
      ∃ t : Finset X, t ⊆ S ∧ t.card = m ∧ Homogeneous c (↑t : Set X)

namespace Specs

def FiniteRamsey : Prop :=
  ∀ k r m : ℕ, 1 ≤ k → 1 ≤ r → 1 ≤ m →
    ∃ N : ℕ, m ≤ N ∧ RamseyProperty.{u} k r m N

def FiniteRamseyOfLt : Prop :=
  ∀ k r m : ℕ, 1 ≤ k → 1 ≤ r → 1 ≤ m → m < k →
    RamseyProperty.{u} k r m m

def FiniteRamseyOneColor : Prop :=
  ∀ k m : ℕ, 1 ≤ k → 1 ≤ m → RamseyProperty.{u} k 1 m m

def FiniteRamseySingleton : Prop :=
  ∀ r m : ℕ, 1 ≤ r → 1 ≤ m →
    m ≤ r * (m - 1) + 1 ∧ RamseyProperty.{u} 1 r m (r * (m - 1) + 1)

end Specs
end P205.Ramsey
