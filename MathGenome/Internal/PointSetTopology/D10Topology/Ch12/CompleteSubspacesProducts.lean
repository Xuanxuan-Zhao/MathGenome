import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.CompleteSubspacesProducts
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformConventions
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-! Completeness of uniform subspaces and products, paper.tex,
`d10:12:complete-subspace-product`. The previously proved bridges identify
the paper's completeness and separation predicates with Mathlib's interfaces.
For the product converse we use a uniformly continuous section of each
projection, rather than assuming that arbitrary uniformly continuous images
of complete spaces are complete.
-/

open Set Filter
open scoped Topology
universe u v

namespace D10Topology.Ch12

theorem closed_subspace_complete {X : Type u} [UniformSpace X] (A : Set X)
    (hX : Complete X) (hA : IsClosed A) : Complete A := by
  let : CompleteSpace X := complete_iff_mathlib.mp hX
  exact complete_iff_mathlib.mpr hA.isComplete.completeSpace_coe

theorem complete_subspace_closed {X : Type u} [UniformSpace X] (A : Set X)
    (hX : Separated (X := X)) (hA : Complete A) : IsClosed A := by
  let : T0Space X := separated_iff_mathlib.mp hX
  exact (completeSpace_coe_iff_isComplete.mp (complete_iff_mathlib.mp hA)).isClosed

theorem complete_product {I : Type u} {X : I → Type v}
    [∀ i, UniformSpace (X i)] (hX : ∀ i, Complete (X i)) :
    Complete (∀ i, X i) := by
  let : ∀ i, CompleteSpace (X i) := fun i => complete_iff_mathlib.mp (hX i)
  exact complete_iff_mathlib.mpr inferInstance

theorem complete_factors_of_nonempty_product {I : Type u} {X : I → Type v}
    [∀ i, UniformSpace (X i)] (hne : Nonempty (∀ i, X i))
    (hX : Complete (∀ i, X i)) (i : I) : Complete (X i) := by
  classical
  obtain ⟨a⟩ := hne
  let s : X i → ∀ j, X j := fun b => Function.update a i b
  have hs : UniformContinuous s := by
    apply uniformContinuous_pi.mpr
    intro j
    by_cases h : j = i
    · subst j
      simp only [s, Function.update_self]
      exact uniformContinuous_id
    · simpa [s, Function.update_of_ne h] using
        (uniformContinuous_const : UniformContinuous (fun _ : X i => a j))
  let : CompleteSpace (∀ i, X i) := complete_iff_mathlib.mp hX
  intro F hF
  obtain ⟨p, hp⟩ := CompleteSpace.complete ((cauchyFilter_iff_mathlib F).mp hF |>.map hs)
  refine ⟨p i, (Ch04.converges_iff_le_nhds F (p i)).mpr ?_⟩
  have hi := ((continuous_apply i).tendsto p).mono_left hp
  simpa [Tendsto, Filter.map_map, Function.comp_def, s] using hi

/-- An empty factor makes the product complete regardless of the other factors. -/
theorem empty_factor_product_complete {I : Type u} {X : I → Type v}
    [∀ i, UniformSpace (X i)] (i : I) [IsEmpty (X i)] :
    Complete (∀ i, X i) := by
  let : IsEmpty (∀ i, X i) := ⟨fun x => isEmptyElim (x i)⟩
  exact complete_empty

end D10Topology.Ch12
