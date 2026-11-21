import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions
import Mathlib.Data.PNat.Basic

/-!
The space in paper.tex, d10:08:fan. `none` is p and `some (n,k)`
is the point (n,k), with both coordinates positive natural numbers.
The tail threshold is quantified separately for each branch.
The canonical topology is constructed here without any assumed certificate.
-/

open Set
open scoped Topology

namespace Specs.D10Topology.Ch08.CountableFan

abbrev Fan := Option (ℕ+ × ℕ+)

def topology : TopologicalSpace Fan where
  IsOpen U := none ∈ U → ∀ n : ℕ+, ∃ K : ℕ+, ∀ k : ℕ+, K ≤ k → some (n,k) ∈ U
  isOpen_univ := fun _ _ => ⟨1, fun _ _ => mem_univ _⟩
  isOpen_inter := by
    intro U V hU hV hp n
    obtain ⟨a, ha⟩ := hU hp.1 n
    obtain ⟨b, hb⟩ := hV hp.2 n
    exact ⟨max a b, fun k hk => ⟨ha k (le_trans (le_max_left _ _) hk),
      hb k (le_trans (le_max_right _ _) hk)⟩⟩
  isOpen_sUnion := by
    intro S hS hp n
    obtain ⟨U, hUS, hpU⟩ := mem_sUnion.mp hp
    obtain ⟨K, hK⟩ := hS U hUS hpU n
    exact ⟨K, fun k hk => mem_sUnion.mpr ⟨U, hUS, hK k hk⟩⟩

def fanType := Type
def fanValue : Type := Option (ℕ+ × ℕ+)
def apexType := Fan
def apexValue : Fan := none
def pointType := ℕ+ → ℕ+ → Fan
def pointValue : pointType := fun n k => some (n,k)
def topologyType := TopologicalSpace Fan
def topologyValue : topologyType := topology

def open_iff : Prop :=
  ∀ U : Set Fan, IsOpen[topology] U ↔
    (none ∈ U → ∀ n : ℕ+, ∃ K : ℕ+, ∀ k : ℕ+, K ≤ k → some (n,k) ∈ U)

def isolated_pairs : Prop :=
  ∀ n k : ℕ+, IsOpen[topology] ({some (n,k)} : Set Fan)

def neighborhood_apex_iff : Prop :=
  ∀ N : Set Fan, Ch01.BasesAndNeighborhoods.Neighborhood topology none N ↔
    none ∈ N ∧ ∀ n : ℕ+, ∃ K : ℕ+, ∀ k : ℕ+, K ≤ k → some (n,k) ∈ N

def countable : Prop := Countable Fan
def t1 : Prop := @T1Space Fan topology
def singleton_gdelta : Prop := ∀ x : Fan, @IsGδ Fan topology ({x} : Set Fan)

def not_firstCountableAt_apex : Prop :=
  ¬ Ch04.FirstCountableSequences.FirstCountableAt topology (none : Fan)

def not_firstCountable : Prop :=
  ¬ CountabilityConventions.firstCountableValue topology

end Specs.D10Topology.Ch08.CountableFan
