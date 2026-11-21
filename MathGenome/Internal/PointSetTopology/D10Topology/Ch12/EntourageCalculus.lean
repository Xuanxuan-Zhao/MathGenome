import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.EntourageCalculus
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformConventions

open Set Filter
open scoped Uniformity SetRel
universe u

namespace D10Topology.Ch12

/-- Finite relational powers in the manuscript's composition convention. -/
def relationPower {X : Type u} (V : Set (X × X)) (n : ℕ) : Set (X × X) :=
  Specs.D10Topology.Ch12.EntourageCalculus.relationPower V n

/-- The uniformity base conditions, with no nonemptiness assumption on X. -/
def EntourageBasis {X : Type u} (B : Set (Set (X × X))) : Prop :=
  Specs.D10Topology.Ch12.EntourageCalculus.EntourageBasis B

theorem symmetric_entourage {X : Type u} [UniformSpace X]
    (U : Set (X × X)) (hU : U ∈ 𝓤 X) :
    ∃ V ∈ 𝓤 X, relationInverse V = V ∧ V ⊆ U := by
  obtain ⟨V, hV, hsym, hsub⟩ := symm_of_uniformity hU
  letI : SetRel.IsSymm V := hsym
  exact ⟨V, hV, SetRel.inv_eq_self V, hsub⟩

/-- A refinement with both a containment bound and a power bound. Induction
on the exponent uses one square root at each step. This also proves the zero
power case, since every entourage contains the diagonal. -/
theorem symmetric_power_refinement {X : Type u} [UniformSpace X] (m : ℕ)
    (U : Set (X × X)) (hU : U ∈ 𝓤 X) :
    ∃ V ∈ 𝓤 X, relationInverse V = V ∧ V ⊆ U ∧ relationPower V m ⊆ U := by
  induction m generalizing U with
  | zero =>
    obtain ⟨V, hV, hsym, hsub⟩ := symmetric_entourage U hU
    refine ⟨V, hV, hsym, hsub, ?_⟩
    rintro ⟨x, y⟩ (hxy : x = y)
    subst y
    exact refl_mem_uniformity hU
  | succ m ih =>
    obtain ⟨W, hW, _, hWW⟩ := comp_symm_mem_uniformity_sets hU
    have hWU : W ⊆ U := (subset_comp_self_of_mem_uniformity hW).trans hWW
    obtain ⟨V, hV, hsym, hVW, hpower⟩ := ih W hW
    refine ⟨V, hV, hsym, hVW.trans hWU, ?_⟩
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩
    exact hWW ⟨y, hpower hxy, hVW hyz⟩

theorem symmetric_power_entourage {X : Type u} [UniformSpace X]
    (U : Set (X × X)) (hU : U ∈ 𝓤 X) (m : ℕ) (_hm : 0 < m) :
    ∃ V ∈ 𝓤 X, relationInverse V = V ∧ relationPower V m ⊆ U := by
  obtain ⟨V, hV, hsym, _, hpower⟩ := symmetric_power_refinement m U hU
  exact ⟨V, hV, hsym, hpower⟩

theorem uniformity_base_criterion {X : Type u} (B : Set (Set (X × X)))
    (hB : EntourageBasis B) :
    ∃! uX : UniformSpace X, ∀ U : Set (X × X),
      U ∈ @uniformity X uX ↔ ∃ V ∈ B, V ⊆ U := by
  obtain ⟨hne, hrefl, hinter, hinv, hcomp⟩ := hB
  let basis : FilterBasis (X × X) := ⟨B, hne, fun hU hV => hinter _ hU _ hV⟩
  let core := UniformSpace.Core.mkOfBasis basis hrefl hinv hcomp
  refine ⟨UniformSpace.ofCore core, fun _ => Iff.rfl, ?_⟩
  intro uX hu
  apply UniformSpace.ext
  apply Filter.ext
  intro U
  exact hu U

theorem uniformity_base_proper {X : Type u} [Nonempty X]
    (B : Set (Set (X × X))) (hB : EntourageBasis B) :
    ∃ uX : UniformSpace X,
      (∀ U : Set (X × X), U ∈ @uniformity X uX ↔ ∃ V ∈ B, V ⊆ U) ∧
      (@uniformity X uX).NeBot := by
  obtain ⟨uX, hu, _⟩ := uniformity_base_criterion B hB
  letI : UniformSpace X := uX
  exact ⟨uX, hu, uniformity_proper⟩

theorem uniformity_base_empty {X : Type u} [IsEmpty X]
    (B : Set (Set (X × X))) (hB : EntourageBasis B) :
    ∃ uX : UniformSpace X,
      (∀ U : Set (X × X), U ∈ @uniformity X uX ↔ ∃ V ∈ B, V ⊆ U) ∧
      (@uniformity X uX).sets = {∅} ∧ ¬ (@uniformity X uX).NeBot := by
  obtain ⟨uX, hu, _⟩ := uniformity_base_criterion B hB
  letI : UniformSpace X := uX
  refine ⟨uX, hu, uniformity_empty, ?_⟩
  intro hne
  have hX := uniformity_proper_iff_nonempty.mp hne
  exact hX.elim isEmptyElim

end D10Topology.Ch12
