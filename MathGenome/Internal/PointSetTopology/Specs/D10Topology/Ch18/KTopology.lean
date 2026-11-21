import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.BasesAndNeighborhoods
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Metrizable.Basic

/-! Independent statements for paper.tex, Example d10:18:k-topology.
`n + 1` indexes exactly the positive integers. No topology on a different
underlying set is substituted for the real line. -/
open Set TopologicalSpace
open scoped Topology
namespace Specs.D10Topology.Ch18.KTopology

def K : Set ℝ := Set.range (fun n : ℕ => 1 / ((n : ℝ) + 1))
def basis : Set (Set ℝ) :=
  {U | ∃ a b : ℝ, a < b ∧ (U = Ioo a b ∨ U = Ioo a b \ K)}
@[instance_reducible] def topology : TopologicalSpace ℝ := generateFrom basis
def rationalBasis : Set (Set ℝ) :=
  {U | ∃ a b : ℚ, a < b ∧ (U = Ioo (a : ℝ) b ∨ U = Ioo (a : ℝ) b \ K)}

def kType := Set ℝ
def basisType := Set (Set ℝ)
def topologyType := TopologicalSpace ℝ

def mem_K : Prop := ∀ x : ℝ, x ∈ K ↔ ∃ n : ℕ, 1 ≤ n ∧ x = 1 / (n : ℝ)
def basis_criterion : Prop := Ch01.BasesAndNeighborhoods.BasisCriterion basis
def basis_for : Prop := Ch01.BasesAndNeighborhoods.BasisFor topology basis
def finer_than_usual : Prop := topology ≤ (inferInstance : TopologicalSpace ℝ)
def hausdorff : Prop := @T2Space ℝ topology
def rational_basis : Prop := Ch01.BasesAndNeighborhoods.BasisFor topology rationalBasis
def rational_basis_countable : Prop := rationalBasis.Countable
def second_countable : Prop := @SecondCountableTopology ℝ topology
def K_closed : Prop := IsClosed[topology] K
def zero_not_mem_K : Prop := (0 : ℝ) ∉ K
def neighborhood_closure_meets_K : Prop :=
  ∀ U : Set ℝ, U ∈ @nhds ℝ topology 0 →
    ((@closure ℝ topology U) ∩ K).Nonempty
def not_regular : Prop := ¬ @RegularSpace ℝ topology
def not_metrizable : Prop := ¬ @MetrizableSpace ℝ topology
end Specs.D10Topology.Ch18.KTopology
