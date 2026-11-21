import MathGenome.Internal.Specs.D07.Ch15.SolvableGroups
import MathGenome.Internal.Specs.D07.Ch18.NilpotenceCriteria

/-!
Independent specification of K07.18.derived_comparison, paper.tex:5180–5197.

The derived series is the same `derivedSeries` used in SolvableGroups, starting
at G and iterating self-commutators. The lower terms are the canonical
`lowerValue` of CentralSeries, with γ₁ = G. Characteristicity is in the whole
ambient group. No group here is assumed finite.

Class at most c means Z_c = G, as in NilpotenceCriteria; it is not a bound on
the library's default numerical class. Vanishing of the c-th derived term
expresses the claimed bound on derived length, also for c = 0. The separate
solvability conclusions use the original derived-series criterion.
-/

namespace Specs.D07.Ch18.DerivedComparison

open Specs.D07.Ch18.CentralSeries
open Specs.D07.Ch18.NilpotenceCriteria

universe u

def DerivedCharacteristic : Prop :=
  ∀ (G : Type u) [Group G] (r : ℕ), (derivedSeries G r).Characteristic

def DerivedLeLower : Prop :=
  ∀ (G : Type u) [Group G] (r : ℕ),
    derivedSeries G r ≤ lowerValue G (r + 1)

def ClassAtMostDerivedTerminates : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ),
    classAtMostValue G c → derivedSeries G c = ⊥

def ClassAtMostSolvable : Prop :=
  ∀ (G : Type u) [Group G] (c : ℕ),
    classAtMostValue G c → Group.IsSolvable G

def NilpotentSolvable : Prop :=
  ∀ (G : Type u) [Group G], Group.IsNilpotent G → Group.IsSolvable G

end Specs.D07.Ch18.DerivedComparison
