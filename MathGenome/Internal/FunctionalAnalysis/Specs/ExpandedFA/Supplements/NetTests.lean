import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Data.PNat.Basic

/-! Independent statements for paper.tex, Proposition `fa2:p1:nets`.
Nets have nonempty directed preorders of indices. Subnet maps are both
order preserving and cofinal. No separation axiom is imposed on the spaces.
The criteria quantify over index sets in the universe of the domain; the
separate compact-subnet statement allows index sets in any universe. -/

open Set Filter Topology

universe u v

namespace ExpandedFA.NetTests

/-- The Moore–Smith subnet convention: an order-preserving cofinal map. -/
def IsSubnetMap {ι κ : Type*} [Preorder ι] [Preorder κ] (φ : κ → ι) : Prop :=
  Monotone φ ∧ ∀ i, ∃ j, i ≤ φ j

/-- A genuine convergent subnet, with an explicit directed index set and map. -/
def HasConvergentSubnet {X : Type u} [TopologicalSpace X]
    {ι : Type v} [Preorder ι] (a : ι → X) : Prop :=
  ∃ (κ : Type (max u v)) (_ : Preorder κ) (_ : Nonempty κ) (_ : IsDirectedOrder κ)
    (φ : κ → ι) (x : X), IsSubnetMap φ ∧ Tendsto (a ∘ φ) atTop (𝓝 x)

/-- The real net on the product of the positive naturals specified in the source. -/
def spikeNet (i : ℕ+ × ℕ+) : ℝ :=
  if i.2 = 1 then (i.1 : ℕ) else 0

end ExpandedFA.NetTests

namespace Specs.ExpandedFA.NetTests

open _root_.ExpandedFA.NetTests

/-- A set is closed exactly when it contains the limits of all its nets. -/
def closedCriterion : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (s : Set X),
    IsClosed s ↔
      ∀ (ι : Type u) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
        (a : ι → X) (x : X),
        (∀ i, a i ∈ s) → Tendsto a atTop (𝓝 x) → x ∈ s

/-- Continuity is equivalent to preservation of every convergent directed net. -/
def continuousCriterion : Prop :=
  ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y),
    Continuous f ↔
      ∀ (ι : Type u) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
        (a : ι → X) (x : X),
        Tendsto a atTop (𝓝 x) → Tendsto (f ∘ a) atTop (𝓝 (f x))

/-- The compactness test, with genuine monotone cofinal subnet maps. -/
def compactCriterion : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    CompactSpace X ↔
      ∀ (ι : Type u) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
        (a : ι → X), HasConvergentSubnet a

/-- The forward compactness statement also applies to larger index universes. -/
def compactSubnet : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X]
    (ι : Type v) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (a : ι → X), HasConvergentSubnet a

/-- The specified net is eventually zero and converges to zero, yet its full
range is unbounded in the TVS sense (indeed, unbounded above). -/
def unboundedNetExample : Prop :=
  (∀ᶠ i in atTop, spikeNet i = 0) ∧
    Tendsto spikeNet atTop (𝓝 0) ∧
    (∀ R : ℝ, ∃ i, R < spikeNet i) ∧
    ¬ Bornology.IsVonNBounded ℝ (range spikeNet)

end Specs.ExpandedFA.NetTests
