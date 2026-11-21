import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.InitialTopologies
import Mathlib.Topology.Bases

/-! Dependent products and box topologies, `d10:03:product` and
`d10:03:product-universal`. No factor is required to be inhabited. -/

open Set
open scoped Topology
universe u v w

namespace D10Topology.Ch03
open D10Topology.Ch01

abbrev Product {I : Type u} (X : I → Type v) := ∀ i, X i

def projection {I : Type u} {X : I → Type v} (i : I) : Product X → X i :=
  fun x => x i

@[instance_reducible] def productTopology {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) : TopologicalSpace (Product X) :=
  initialTopology tX projection

/-- `F.pi U` is the intersection of the coordinate tests over F. -/
def productBasis {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) : Set (Set (Product X)) :=
  {S | ∃ (U : ∀ i, Set (X i)) (F : Finset I),
    (∀ i ∈ F, IsOpen[tX i] (U i)) ∧ S = (F : Set I).pi U}

/-- All open rectangles, with every coordinate allowed to be restricted. -/
def boxBasis {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) : Set (Set (Product X)) :=
  {S | ∃ U : ∀ i, Set (X i), (∀ i, IsOpen[tX i] (U i)) ∧ S = univ.pi U}

@[instance_reducible] def boxTopology {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) : TopologicalSpace (Product X) :=
  TopologicalSpace.generateFrom (boxBasis tX)

theorem product_initial {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) :
    productTopology tX = initialTopology tX projection := rfl

/-- Bridge to the library's canonical dependent product topology. -/
theorem productTopology_eq_pi {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) :
    productTopology tX = @Pi.topologicalSpace I X tX := by
  let := tX
  apply le_antisymm
  · change productTopology tX ≤ ⨅ i, TopologicalSpace.induced (projection i) (tX i)
    exact le_iInf fun i => continuous_iff_le_induced.mp
      (initial_maps_continuous tX projection i)
  · exact initial_coarsest tX projection _ (fun i => continuous_apply i)

theorem product_basis {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) :
    BasisFor (productTopology tX) (productBasis tX) := by
  rw [productTopology_eq_pi]
  let := tX
  apply (basis_iff_mathlib _ _).mpr
  exact isTopologicalBasis_pi
    (fun _ => TopologicalSpace.isTopologicalBasis_opens)

theorem productBasis_intersections {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (S : Set (Product X)) :
    S ∈ productBasis tX ↔ ∃ (U : ∀ i, Set (X i)) (F : Finset I),
      (∀ i ∈ F, IsOpen[tX i] (U i)) ∧
        S = ⋂ i ∈ F, projection i ⁻¹' U i := by
  simp only [productBasis, mem_ofPred_eq, Set.pi_def, Finset.mem_coe]
  rfl

theorem productBasis_empty {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) :
    univ ∈ productBasis tX := by
  exact ⟨fun _ => univ, ∅, by simp, by simp⟩

theorem product_opens {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (S : Set (Product X)) :
    IsOpen[productTopology tX] S ↔
      ∃ A : Set (Set (Product X)), A ⊆ productBasis tX ∧ S = ⋃₀ A :=
  basis_open_iff_union _ _ (product_basis tX) S

theorem box_basis {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) :
    BasisFor (boxTopology tX) (boxBasis tX) := by
  apply basis_generated
  constructor
  · apply eq_univ_of_univ_subset
    intro x _
    refine Set.mem_sUnion.mpr ⟨univ, ?_, Set.mem_univ x⟩
    exact ⟨fun _ => univ, fun _ => isOpen_univ, by simp⟩
  · rintro V ⟨U, hU, rfl⟩ W ⟨T, hT, rfl⟩ x hx
    refine ⟨univ.pi (fun i => U i ∩ T i), ?_, ?_, ?_⟩
    · exact ⟨fun i => U i ∩ T i, fun i => (hU i).inter (hT i), rfl⟩
    · simpa only [Set.pi_inter_distrib] using hx
    · rw [Set.pi_inter_distrib]

theorem box_opens {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (S : Set (Product X)) :
    IsOpen[boxTopology tX] S ↔
      ∃ A : Set (Set (Product X)), A ⊆ boxBasis tX ∧ S = ⋃₀ A :=
  basis_open_iff_union _ _ (box_basis tX) S

theorem continuous_product_iff {I : Type u} {X : I → Type v} {Z : Type w}
    (tX : ∀ i, TopologicalSpace (X i)) (tZ : TopologicalSpace Z)
    (g : Z → Product X) :
    Continuous[tZ, productTopology tX] g ↔
      ∀ i, Continuous[tZ, tX i] (projection i ∘ g) :=
  continuous_initial_iff tX projection tZ g

theorem projection_continuous {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (i : I) :
    Continuous[productTopology tX, tX i] (projection i) :=
  initial_maps_continuous tX projection i

theorem projection_open {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (i : I) :
    @IsOpenMap (Product X) (X i) (productTopology tX) (tX i) (projection i) := by
  rw [productTopology_eq_pi]
  let := tX
  exact isOpenMap_eval i

theorem projection_surjective {I : Type u} {X : I → Type v}
    (h : Nonempty (Product X)) (i : I) :
    Function.Surjective (projection (X := X) i) := by
  classical
  obtain ⟨x⟩ := h
  intro y
  exact ⟨Function.update x i y, by simp [projection]⟩

theorem box_eq_product_of_finite {I : Type u} {X : I → Type v} [Finite I]
    (tX : ∀ i, TopologicalSpace (X i)) :
    boxTopology tX = productTopology tX := by
  let := tX
  rw [productTopology_eq_pi]
  have hc : ∀ i, ⋃₀ {S : Set (X i) | IsOpen S} = univ := by
    intro i
    exact eq_univ_of_univ_subset (subset_sUnion_of_mem isOpen_univ)
  have heq := @pi_generateFrom_eq_finite I X
    (fun i => {S : Set (X i) | IsOpen S}) inferInstance hc
  have ht : (fun i => TopologicalSpace.generateFrom {S : Set (X i) | IsOpen S}) = tX := by
    funext i
    exact TopologicalSpace.generateFrom_setOfPred_isOpen (tX i)
  rw [ht] at heq
  exact heq.symm

theorem empty_product_singleton {I : Type u} {X : I → Type v} [IsEmpty I] :
    ∃! _x : Product X, True := by
  refine ⟨fun i => isEmptyElim i, trivial, ?_⟩
  intro y _
  funext i
  exact isEmptyElim i

theorem product_empty_of_factor {I : Type u} {X : I → Type v}
    (i : I) [IsEmpty (X i)] : IsEmpty (Product X) :=
  ⟨fun x => isEmptyElim (x i)⟩

end D10Topology.Ch03
