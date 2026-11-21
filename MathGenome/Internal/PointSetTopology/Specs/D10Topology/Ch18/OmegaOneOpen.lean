import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.OrdinalCompact
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.CountableCompactness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.SetTheory.Cardinal.Regular

/-! Independent statements for the Y part of paper.tex, d10:18:omega-one.
The first uncountable ordinal is Mathlib's ω₁, not an arbitrary uncountable
linear order. The nonnegative ordinal interval [0,ω₁) is represented by Iio ω₁;
ordinals are nonnegative. Its inherited topology is identified explicitly with
its intrinsic order topology. No extra topological hypotheses are assumed. -/

open Set
open scoped Ordinal

namespace Specs.D10Topology.Ch18.OmegaOneOpen

abbrev Y : Type 1 := Iio (ω₁ : Ordinal.{0})

def spaceType := Type 1
def spaceValue : spaceType := Y

def orderTopology_eq_subspace : Prop :=
  Ch01.OrderTopologies.topologyValue Y = (inferInstance : TopologicalSpace Y)

def firstCountable : Prop :=
  Ch04.FirstCountableSequences.FirstCountable (inferInstance : TopologicalSpace Y)

def locallyCompact : Prop := Ch11.LocalCompactConventions.LocallyCompact Y

def countablyCompact : Prop := Ch05.CountableCompactness.CountableCoverCompact Y

def sequentiallyCompact : Prop := Ch05.CountableCompactness.SequentiallyCompact Y

def not_compact : Prop := ¬ Ch05.Compactness.CoverCompact Y

def not_lindelof : Prop := ¬ LindelofSpace Y

def not_sigmaCompact : Prop := ¬ Ch11.LocalCompactConventions.SigmaCompact Y

/-- The bound itself is countable and belongs to the same ordinal universe. -/
def compact_subset_bounded : Prop :=
  ∀ K : Set Y, IsCompact K →
    ∃ β : Ordinal.{0}, β < ω₁ ∧ ∀ x ∈ K, (x : Ordinal.{0}) ≤ β

end Specs.D10Topology.Ch18.OmegaOneOpen
