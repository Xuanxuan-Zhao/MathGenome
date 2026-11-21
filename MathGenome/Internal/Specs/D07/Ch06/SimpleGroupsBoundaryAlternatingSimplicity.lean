import MathGenome.Internal.Specs.D07.Ch02.AlternatingGroups
import Mathlib.GroupTheory.Subgroup.Simple

/-!
Independent specification for the alternating-group assertion in
`K07.06.simple_groups_boundary`, paper.tex:1103–1131.

The alternating group is the same sign kernel as in the accepted chapter-two
interface. The finite carrier has n letters, and the hypothesis is exactly
n ≥ 5. `IsSimpleGroup` includes nontriviality, as well as the assertion that
every normal subgroup is bottom or top. Nonabelianness is expressed by an
actual pair of elements that do not commute.
-/

namespace Specs.D07.Ch06.SimpleGroupsBoundaryAlternatingSimplicity

universe u

def AlternatingSimple : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (n : ℕ), Nat.card X = n → 5 ≤ n →
    IsSimpleGroup (alternatingGroup X)

def AlternatingNonabelian : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (n : ℕ), Nat.card X = n → 5 ≤ n →
    ∃ σ τ : alternatingGroup X, σ * τ ≠ τ * σ

def NontrivialNormalSubgroupEqTop : Prop := by
  classical
  exact ∀ (X : Type u) [Fintype X] (n : ℕ), Nat.card X = n → 5 ≤ n →
    ∀ N : Subgroup (alternatingGroup X), N.Normal → N ≠ ⊥ → N = ⊤

end Specs.D07.Ch06.SimpleGroupsBoundaryAlternatingSimplicity
