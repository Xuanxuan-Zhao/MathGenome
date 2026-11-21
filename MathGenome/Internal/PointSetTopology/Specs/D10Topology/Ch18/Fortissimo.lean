import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions
import Mathlib.Data.Set.Countable

/-! Fortissimo (paper.tex, d10:18:fortissimo). `Option D` adjoins exactly one
point `none`; `some` identifies the original set D with its isolated copy.
No topology on D is assumed. The topology exists for every D; the three
negative conclusions require the original uncountability hypothesis. -/
open Set TopologicalSpace
open scoped Topology
universe u

namespace Specs.D10Topology.Ch18.Fortissimo

/-- All subsets avoiding the new point are open. At the new point the
complement must be countable (and necessarily consists of old points). -/
@[instance_reducible] def topology (D : Type u) : TopologicalSpace (Option D) where
  IsOpen U := none ∈ U → Uᶜ.Countable
  isOpen_univ := by simp
  isOpen_inter U V hU hV h := by
    simpa only [compl_inter] using (hU h.1).union (hV h.2)
  isOpen_sUnion S hS h := by
    obtain ⟨U, hUS, hpU⟩ := mem_sUnion.mp h
    exact (hS U hUS hpU).mono (compl_subset_compl.mpr (subset_sUnion_of_mem hUS))

def topologyType := (D : Type u) → TopologicalSpace (Option D)
def topologyValue : topologyType := topology

def open_characterization : Prop := ∀ (D : Type u) (U : Set (Option D)),
  IsOpen[topology D] U ↔ (none ∈ U → Uᶜ.Countable)

def isolated_clopen : Prop := ∀ (D : Type u) (d : D),
  @IsClopen (Option D) (topology D) {some d}

def clopen_basis : Prop := ∀ (D : Type u),
  letI := topology D
  TopologicalSpace.IsTopologicalBasis {U : Set (Option D) | IsClopen U}

def hausdorff : Prop := ∀ (D : Type u), @T2Space (Option D) (topology D)
def normal : Prop := ∀ (D : Type u), @NormalSpace (Option D) (topology D)
def lindelof : Prop := ∀ (D : Type u), @LindelofSpace (Option D) (topology D)

def not_compact : Prop := ∀ (D : Type u) [Uncountable D],
  ¬ @CompactSpace (Option D) (topology D)

/-- Uses arbitrary neighborhoods, rather than assuming the base is open. -/
def no_countable_localBase : Prop := ∀ (D : Type u) [Uncountable D]
    (L : Set (Set (Option D))), L.Countable →
  ¬ Ch01.BasesAndNeighborhoods.LocalBase (topology D) none L

def not_first_countable : Prop := ∀ (D : Type u) [Uncountable D],
  ¬ @FirstCountableTopology (Option D) (topology D)

def not_separable : Prop := ∀ (D : Type u) [Uncountable D],
  ¬ @SeparableSpace (Option D) (topology D)

end Specs.D10Topology.Ch18.Fortissimo
