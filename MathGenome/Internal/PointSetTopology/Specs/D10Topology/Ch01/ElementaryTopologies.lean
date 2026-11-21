import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.BasesAndNeighborhoods
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions
import Mathlib.Data.Set.Countable

/-! Independent specification of paper.tex, d10:01:examples.
All topology parameters are explicit; the real line retains its usual instance.
The topology constructions allow empty underlying types. -/
open Set
open scoped Topology
universe u

namespace Specs.D10Topology.Ch01.ElementaryTopologies

/-- All nonempty bounded ordinary open intervals. -/
def realIntervalBasis : Set (Set ℝ) :=
  {U | ∃ a b : ℝ, a < b ∧ U = Ioo a b}

/-- All nonempty lower-limit basic intervals. -/
def lowerLimitBasis : Set (Set ℝ) :=
  {U | ∃ a b : ℝ, a < b ∧ U = Ico a b}

/-- The canonical lower-limit topology, on the original underlying real type. -/
@[instance_reducible] def lowerLimitTopology : TopologicalSpace ℝ :=
  TopologicalSpace.generateFrom lowerLimitBasis

/-- The canonical cofinite topology on X, without a nonemptiness assumption. -/
@[instance_reducible] def cofiniteTopology (X : Type u) : TopologicalSpace X :=
  TopologicalSpace.cofinite

/-- The canonical cocountable topology on X. -/
@[instance_reducible] def cocountableTopology (X : Type u) : TopologicalSpace X where
  IsOpen U := U.Nonempty → Uᶜ.Countable
  isOpen_univ := by simp
  isOpen_inter U V hU hV h := by
    rw [compl_inter]
    exact (hU (h.mono inter_subset_left)).union (hV (h.mono inter_subset_right))
  isOpen_sUnion A hA h := by
    obtain ⟨x, U, hUA, hxU⟩ := h
    exact (hA U hUA ⟨x, hxU⟩).mono (compl_subset_compl.mpr (subset_sUnion_of_mem hUA))

-- Definition bindings check both the types and the values.
def intervalFamilyType := Set (Set ℝ)
def realIntervalBasisValue : intervalFamilyType :=
  {U | ∃ a b : ℝ, a < b ∧ U = Ioo a b}
def lowerLimitBasisValue : intervalFamilyType :=
  {U | ∃ a b : ℝ, a < b ∧ U = Ico a b}
def realTopologyType := TopologicalSpace ℝ
def lowerLimitTopologyValue : realTopologyType := TopologicalSpace.generateFrom lowerLimitBasis

def topologyOnType : Type (u + 1) := (X : Type u) → TopologicalSpace X
def cofiniteTopologyValue : topologyOnType := fun _ => TopologicalSpace.cofinite
def cocountableTopologyValue : topologyOnType := cocountableTopology

open _root_.Specs.D10Topology.Ch01.BasesAndNeighborhoods
open _root_.D10Topology.Ch01

def usual_intervals_basis : Prop := BasisFor inferInstance realIntervalBasis

def lowerLimit_basis_criterion : Prop := BasisCriterion lowerLimitBasis

def lowerLimit_basis : Prop := BasisFor lowerLimitTopology lowerLimitBasis

def lowerLimit_opens : Prop := ∀ U : Set ℝ,
  IsOpen[lowerLimitTopology] U ↔ ∃ A : Set (Set ℝ), A ⊆ lowerLimitBasis ∧ U = ⋃₀ A

def lowerLimit_strictly_finer : Prop :=
  openSets (inferInstance : TopologicalSpace ℝ) ⊂ openSets lowerLimitTopology

def lowerLimit_witness : Prop :=
  IsOpen[lowerLimitTopology] (Ico (0 : ℝ) 1) ∧ ¬ IsOpen (Ico (0 : ℝ) 1)

def cofinite_opens : Prop := ∀ (X : Type u) (U : Set X),
  IsOpen[cofiniteTopology X] U ↔ U = ∅ ∨ Uᶜ.Finite

def cocountable_opens : Prop := ∀ (X : Type u) (U : Set X),
  IsOpen[cocountableTopology X] U ↔ U = ∅ ∨ Uᶜ.Countable

def cofinite_topology_axioms : Prop := ∀ (X : Type u),
  OpenFamilyAxioms {U : Set X | U = ∅ ∨ Uᶜ.Finite}

def cocountable_topology_axioms : Prop := ∀ (X : Type u),
  OpenFamilyAxioms {U : Set X | U = ∅ ∨ Uᶜ.Countable}

/-- The closed-set characterization even holds without assuming X infinite. -/
def cofinite_closed : Prop := ∀ (X : Type u) (F : Set X),
  IsClosed[cofiniteTopology X] F ↔ F.Finite ∨ F = univ

def cofinite_infinite_dense : Prop := ∀ (X : Type u) (A : Set X),
  A.Infinite → @Dense X (cofiniteTopology X) A

/-- This stronger closed-set description includes the required countable case. -/
def cocountable_closed : Prop := ∀ (X : Type u) (F : Set X),
  IsClosed[cocountableTopology X] F ↔ F.Countable ∨ F = univ

def cocountable_countable_closed : Prop := ∀ (X : Type u) (A : Set X),
  A.Countable → IsClosed[cocountableTopology X] A

def cocountable_uncountable_dense : Prop := ∀ (X : Type u) (A : Set X),
  ¬ A.Countable → @Dense X (cocountableTopology X) A

end Specs.D10Topology.Ch01.ElementaryTopologies
