import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.SorgenfreyLine

/-! Independent obligations for paper.tex, d10:08:sorgenfrey-line:
every open cover in the lower-limit topology has a countable subcover,
and this same space is normal and T₄ (normal plus T₁).
-/
open Set
universe v

namespace Specs.D10Topology.Ch08.SorgenfreyLindelof

local instance : TopologicalSpace ℝ := Ch01.ElementaryTopologies.lowerLimitTopology

def lindelof : Prop := LindelofSpace ℝ

def countable_subcover : Prop :=
  ∀ {ι : Type v} (U : ι → Set ℝ), (∀ i, IsOpen (U i)) →
    (⋃ i, U i) = univ → ∃ J : Set ι, J.Countable ∧ (⋃ i ∈ J, U i) = univ

def normal : Prop := NormalSpace ℝ

def t4 : Prop := NormalSpace ℝ ∧ T1Space ℝ

end Specs.D10Topology.Ch08.SorgenfreyLindelof
