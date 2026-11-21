import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.ClosureCalculus
import Mathlib.Topology.Instances.Real.Lemmas

/-!
Independent statements for paper.tex, d10:03:subspace and
d10:03:interior-caution. A subset is represented by its canonical subtype,
with the induced topology. Preimages under `Subtype.val` represent relative
intersections; images identify subsets of the subtype with ambient subsets.
Both forms of the closure and interior formulas are specified below.
There are no separation or nonemptiness hypotheses in the general results.
-/

open Set Topology
universe u v

namespace Specs.D10Topology.Ch03.Subspaces
open _root_.Specs.D10Topology.Ch01.BasesAndNeighborhoods

def subspace_topology_induced : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    (inferInstance : TopologicalSpace A) = t.induced (Subtype.val : A → X)

/-- The canonical identification of a relative intersection with an ambient set. -/
def subspace_image_preimage : Prop :=
  ∀ {X : Type u} (A B : Set X),
    (Subtype.val : A → X) '' ((Subtype.val : A → X) ⁻¹' B) = A ∩ B

def subspace_preimage_image : Prop :=
  ∀ {X : Type u} (A : Set X) (B : Set A),
    (Subtype.val : A → X) ⁻¹' ((Subtype.val : A → X) '' B) = B

def subspace_open_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X) (V : Set A),
    IsOpen V ↔ ∃ U : Set X, IsOpen U ∧ (Subtype.val : A → X) ⁻¹' U = V

def subspace_closed_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X) (C : Set A),
    IsClosed C ↔ ∃ F : Set X, IsClosed F ∧ (Subtype.val : A → X) ⁻¹' F = C

def subspace_open_iff_image : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X) (V : Set A),
    IsOpen V ↔ ∃ U : Set X, IsOpen U ∧ (Subtype.val : A → X) '' V = A ∩ U

def subspace_closed_iff_image : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X) (C : Set A),
    IsClosed C ↔ ∃ F : Set X, IsClosed F ∧ (Subtype.val : A → X) '' C = A ∩ F

def subspace_closure : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X) (B : Set A),
    closure B = (Subtype.val : A → X) ⁻¹' closure ((Subtype.val : A → X) '' B)

def subspace_closure_ambient : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A B : Set X), B ⊆ A →
    (Subtype.val : A → X) '' closure ((Subtype.val : A → X) ⁻¹' B) = A ∩ closure B

def subspace_inclusion_embedding : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    IsEmbedding (Subtype.val : A → X)

def subspace_continuous_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {Z : Type v} [TopologicalSpace Z]
    (A : Set X) (g : Z → A),
    Continuous g ↔ Continuous ((Subtype.val : A → X) ∘ g)

def subspace_basis : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X) (B : Set (Set X)),
    BasisFor t B → BasisFor (inferInstance : TopologicalSpace A)
      ((fun U : Set X => (Subtype.val : A → X) ⁻¹' U) '' B)

/-- Preimages of ambient interiors are contained in relative interiors. -/
def subspace_interior_subset : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A B : Set X),
    (Subtype.val : A → X) ⁻¹' interior B ⊆
      interior ((Subtype.val : A → X) ⁻¹' B)

/-- The source's literal ambient-set form for B contained in A. -/
def subspace_interior_ambient_subset : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A B : Set X), B ⊆ A →
    A ∩ interior B ⊆
      (Subtype.val : A → X) '' interior ((Subtype.val : A → X) ⁻¹' B)

/-- A = B = {0} in the usual real line: both interiors and both boundaries,
including their canonical ambient identifications and closed/nonopen facts. -/
def singleton_interior_boundary_caution : Prop :=
  let A : Set ℝ := {0}
  IsClosed A ∧ ¬ IsOpen A ∧
    interior A = ∅ ∧ A ∩ interior A = ∅ ∧
    interior ((Subtype.val : A → ℝ) ⁻¹' A) = univ ∧
    (Subtype.val : A → ℝ) '' interior ((Subtype.val : A → ℝ) ⁻¹' A) = A ∧
    frontier ((Subtype.val : A → ℝ) ⁻¹' A) = ∅ ∧
    A ∩ frontier A = A

end Specs.D10Topology.Ch03.Subspaces
