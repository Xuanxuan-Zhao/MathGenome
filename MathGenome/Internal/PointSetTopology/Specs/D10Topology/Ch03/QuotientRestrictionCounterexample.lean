import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.QuotientMaps
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
Independent data and full propositions for paper.tex, d10:03:restriction-failure
(lines 463–465). Intervals carry their usual induced real topologies, the
binary sum carries the disjoint-sum topology, and A carries the subspace
topology of that sum. In particular no quotient topology is assigned to the
target or to the restriction's target.
-/

open Set Topology

namespace D10Topology.Ch03.RestrictionExampleData

abbrev Left := Icc (0 : ℝ) 1
abbrev Right := Icc (2 : ℝ) 3
abbrev Y := Icc (0 : ℝ) 2
abbrev X := Left ⊕ Right

def leftMap (t : Left) : Y :=
  ⟨t.val, t.property.1, t.property.2.trans (by norm_num)⟩

def rightMap (t : Right) : Y :=
  ⟨t.val - 1, by constructor <;> linarith [t.property.1, t.property.2]⟩

/-- The two formulas in the source, on tagged summands. -/
def q : X → Y := Sum.elim leftMap rightMap

/-- Exactly [0,1) in the first summand and all of [2,3] in the second. -/
def A : Set X := {x | Sum.elim (fun t : Left => t.val < 1) (fun _ : Right => True) x}

/-- The actual restriction of q to the indicated subspace. -/
def restricted : A → Y := fun a => q a.val

/-- [1,2] as a subset of [0,2]. -/
def V : Set Y := {y | 1 ≤ y.val}

/-- The open second summand, traced onto the subspace A. -/
def secondSummand : Set A :=
  (Subtype.val : A → X) ⁻¹' range (Sum.inr : Right → X)

def discarded : X := Sum.inl ⟨1, by norm_num⟩
def retained : X := Sum.inr ⟨2, by norm_num⟩
def one : Y := ⟨1, by norm_num⟩

end D10Topology.Ch03.RestrictionExampleData

namespace Specs.D10Topology.Ch03.QuotientRestrictionCounterexample
open _root_.D10Topology.Ch03.RestrictionExampleData
open _root_.D10Topology.Ch03.QuotientData

def q_continuous : Prop := Continuous q
def q_closed : Prop := IsClosedMap q
def q_surjective : Prop := Function.Surjective q
def q_quotient : Prop := QuotientMap q
def restriction_continuous : Prop := Continuous restricted
def restriction_surjective : Prop := Function.Surjective restricted

def witness_preimage : Prop := restricted ⁻¹' V = secondSummand
def witness_preimage_open : Prop := IsOpen (restricted ⁻¹' V)
def witness_not_open : Prop := ¬ IsOpen V
def restriction_not_quotient : Prop := ¬ QuotientMap restricted

def fiber_witness : Prop :=
  retained ∈ A ∧ discarded ∉ A ∧ retained ≠ discarded ∧
    q retained = one ∧ q discarded = one

def fiber_one : Prop := q ⁻¹' {one} = {discarded, retained}

def restricted_fiber_one : Prop :=
  restricted ⁻¹' {one} = {⟨retained, trivial⟩}

def A_not_saturated : Prop := ¬ Saturated q A

end Specs.D10Topology.Ch03.QuotientRestrictionCounterexample
