import MathGenome.Internal.Specs.D07.Ch03.CosetBijections
import Mathlib.SetTheory.Cardinal.NatCard

/-!
Independent specification of K07.03.lagrange (paper.tex:591–598).
The number of left cosets counts distinct subsets `gH`, using the same
set-valued cosets as the upstream partition and bijection specifications.
All natural-number cardinalities below have the explicit hypothesis that
the ambient group is finite. No normality or commutativity is required.
-/

namespace Specs.D07.Ch03.Lagrange

open Specs.D07.Ch03.CosetsPartition

universe u

def CardinalityFormula : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G),
    Nat.card G = Nat.card H * Nat.card ↥(Set.range (leftCoset H))

def SubgroupCardDivides : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G),
    Nat.card H ∣ Nat.card G

def CosetCountDivides : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G),
    Nat.card ↥(Set.range (leftCoset H)) ∣ Nat.card G

/-- The positive finite cardinalities used in the source's counting proof. -/
def PositiveCardinalities : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G),
    0 < Nat.card H ∧ 0 < Nat.card ↥(Set.range (leftCoset H))

end Specs.D07.Ch03.Lagrange
