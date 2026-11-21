import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformTopology
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.BasesAndNeighborhoods
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.ShrinkingHierarchy

/-! The induced topology theorem (paper.tex, d10:12:uniform-topology).
The specification constructs the topology directly from entourage sections.
Equality of open predicates identifies it with the canonical UniformSpace
topology. Neighborhoods, Hausdorffness and regularity are transported only
after this equality has been proved. Empty spaces are allowed throughout.
-/

open Set Filter
open scoped Uniformity Topology
universe u

namespace D10Topology.Ch12

/-- Open sets are exactly those locally containing an entourage section. -/
@[instance_reducible]
def uniformTopology {X : Type u} [UniformSpace X] : TopologicalSpace X :=
  Specs.D10Topology.Ch12.UniformTopology.uniformTopology

theorem uniformTopology_isOpen {X : Type u} [UniformSpace X] (O : Set X) :
    IsOpen[uniformTopology] O ↔
      ∀ x ∈ O, ∃ U ∈ 𝓤 X, entourageBall U x ⊆ O := Iff.rfl

/-- The paper's open-set construction agrees with the topology carried by the
canonical uniform space; the library theorem uses the same section direction. -/
theorem uniformTopology_eq_canonical {X : Type u} [uX : UniformSpace X] :
    uniformTopology = uX.toTopologicalSpace := by
  apply TopologicalSpace.ext
  funext O
  exact propext isOpen_iff_ball_subset.symm

theorem uniformTopology_neighborhood_iff {X : Type u} [uX : UniformSpace X]
    (x : X) (N : Set X) :
    Ch01.Neighborhood uniformTopology x N ↔
      ∃ U ∈ 𝓤 X, entourageBall U x ⊆ N := by
  rw [uniformTopology_eq_canonical, Ch01.neighborhood_iff_mem_nhds]
  exact UniformSpace.mem_nhds_iff

/-- All sections are neighborhoods, and every neighborhood contains a section;
the sections themselves need not be open. -/
theorem uniformTopology_localBase {X : Type u} [UniformSpace X] (x : X) :
    Ch01.LocalBase uniformTopology x
      {N : Set X | ∃ U ∈ 𝓤 X, entourageBall U x = N} := by
  constructor
  · rintro N ⟨U, hU, rfl⟩
    exact (uniformTopology_neighborhood_iff x _).mpr ⟨U, hU, subset_rfl⟩
  · intro N hN
    obtain ⟨U, hU, hsub⟩ := (uniformTopology_neighborhood_iff x N).mp hN
    exact ⟨entourageBall U x, ⟨U, hU, rfl⟩, hsub⟩

theorem uniformTopology_nhds {X : Type u} [UniformSpace X] (x : X) :
    @nhds X uniformTopology x = (𝓤 X).comap (Prod.mk x) := by
  rw [uniformTopology_eq_canonical]
  exact nhds_eq_comap_uniformity

theorem uniformTopology_hausdorff_iff_separated {X : Type u} [UniformSpace X] :
    @T2Space X uniformTopology ↔ Separated (X := X) := by
  rw [uniformTopology_eq_canonical]
  constructor
  · intro h
    let := h
    exact separated_iff_mathlib.mpr inferInstance
  · intro h
    let : T0Space X := separated_iff_mathlib.mp h
    infer_instance

/-- Uniform-space regularity is unconditional, including nonseparated spaces. -/
theorem uniformTopology_regular {X : Type u} [UniformSpace X] :
    @RegularSpace X uniformTopology := by
  rw [uniformTopology_eq_canonical]
  infer_instance

theorem uniformTopology_shrinking {X : Type u} [UniformSpace X]
    (x : X) (O : Set X) (hO : IsOpen[uniformTopology] O) (hx : x ∈ O) :
    ∃ V : Set X, IsOpen[uniformTopology] V ∧ x ∈ V ∧
      V ⊆ @closure X uniformTopology V ∧ @closure X uniformTopology V ⊆ O := by
  exact (@Ch07.regular_iff_shrinking X uniformTopology).mp uniformTopology_regular x O hO hx

theorem uniformTopology_empty {X : Type u} [UniformSpace X] [IsEmpty X] (O : Set X) :
    IsOpen[uniformTopology] O := by
  intro x
  exact isEmptyElim x

end D10Topology.Ch12
