import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Separation.Hausdorff

/-! Independent statements for paper.tex, d10:08:lindelof-subspace-failure.
`Option E` is the tagged disjoint union of E with one new point `none`.
No compactification theorem is used in the definition or the statements. -/

open Set TopologicalSpace
universe u

namespace Specs.D10Topology.Ch08.LindelofOpenSubspaceFailure

/-- All points `some e` are isolated; an open set containing `none` has
finite complement in E. This construction also makes sense for finite E. -/
@[instance_reducible] def topology (E : Type u) : TopologicalSpace (Option E) where
  IsOpen s := none ∈ s → (Option.some ⁻¹' sᶜ).Finite
  isOpen_univ := by simp
  isOpen_inter := by
    intro s t hs ht hn
    simpa only [compl_inter, preimage_union] using (hs hn.1).union (ht hn.2)
  isOpen_sUnion := by
    intro S hS hn
    obtain ⟨s, hs, hn⟩ := mem_sUnion.mp hn
    exact (hS s hs hn).subset (by
      intro e he hes
      exact he (mem_sUnion.mpr ⟨s, hs, hes⟩))

def topologyType := (E : Type u) → TopologicalSpace (Option E)
def topologyValue : topologyType := topology

def open_iff : Prop := ∀ (E : Type u) (s : Set (Option E)),
  @IsOpen _ (topology E) s ↔
    (none ∈ s → (Option.some ⁻¹' sᶜ).Finite)

def open_images : Prop := ∀ (E : Type u) (A : Set E),
  @IsOpen _ (topology E) (Option.some '' A)

def compact : Prop := ∀ (E : Type u), @CompactSpace (Option E) (topology E)
def hausdorff : Prop := ∀ (E : Type u), @T2Space (Option E) (topology E)
def lindelof : Prop := ∀ (E : Type u), @LindelofSpace (Option E) (topology E)

/-- The topology pulled back to the original copy of E is exactly discrete. -/
def induced_discrete : Prop := ∀ (E : Type u),
  (topology E).induced Option.some = (⊥ : TopologicalSpace E)

/-- The copy of E is open in the ambient space. -/
def open_copy : Prop := ∀ (E : Type u),
  @IsOpen _ (topology E) (range (Option.some : E → Option E))

/-- The actual open subspace, with its induced subtype topology, is discrete. -/
def subspace_discrete : Prop := ∀ (E : Type u),
  letI := topology E
  DiscreteTopology (range (Option.some : E → Option E))

/-- The fibers used below are literally singleton subsets of the open copy. -/
def singleton_fiber : Prop := ∀ (E : Type u) (e : E),
  {x : range (Option.some : E → Option E) | x.val = some e} =
    {⟨some e, mem_range_self e⟩}

/-- Its singleton family is an open cover with no countable subcover. -/
def singleton_cover : Prop := ∀ (E : Type u) [Uncountable E],
  letI := topology E
  let U : E → Set (range (Option.some : E → Option E)) :=
    fun e => {x | x.val = some e}
  (∀ e, IsOpen (U e)) ∧ (⋃ e, U e) = univ ∧
    ∀ J : Set E, J.Countable → (⋃ e ∈ J, U e) ≠ univ

def subspace_not_lindelof : Prop := ∀ (E : Type u) [Uncountable E],
  letI := topology E
  ¬ LindelofSpace (range (Option.some : E → Option E))

/-- Hence Lindelöfness fails to pass even to open subspaces, inside T2 compact spaces. -/
def failure_of_open_heredity : Prop := ∀ (E : Type u) [Uncountable E],
  letI := topology E
  CompactSpace (Option E) ∧ T2Space (Option E) ∧ LindelofSpace (Option E) ∧
    IsOpen (range (Option.some : E → Option E)) ∧
    DiscreteTopology (range (Option.some : E → Option E)) ∧
    ¬ LindelofSpace (range (Option.some : E → Option E))

end Specs.D10Topology.Ch08.LindelofOpenSubspaceFailure
