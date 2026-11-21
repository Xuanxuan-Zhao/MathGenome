import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.ClosedEntourages
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.EntourageCalculus
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformTopology

/-! Closed symmetric refinements of entourages (d10:12:closed-entourages).
All closures are in the canonical product topology, whose factor topology is
the paper's induced topology by `uniformTopology_eq_canonical`.
-/

open Set Filter
open scoped Uniformity Topology
universe u

namespace D10Topology.Ch12

/-- Swapping the coordinates commutes with product-topological closure. -/
theorem relationInverse_closure {X : Type u} [TopologicalSpace X]
    (V : Set (X × X)) :
    relationInverse (closure V) = closure (relationInverse V) :=
  (Homeomorph.prodComm X X).preimage_closure V

/-- Relational powers preserve containment, also for the zero power. -/
theorem relationPower_mono {X : Type u} {V W : Set (X × X)}
    (hVW : V ⊆ W) (n : ℕ) : relationPower V n ⊆ relationPower W n := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih =>
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩
    exact ⟨y, ih hxy, hVW hyz⟩

/-- The product neighborhood V[x] × V[y] of a closure point meets V.
Its witnessing pair supplies the three successive links in V. -/
theorem closure_symmetric_entourage_subset_cube {X : Type u} [UniformSpace X]
    (V : Set (X × X)) (hV : V ∈ 𝓤 X) (hsym : relationInverse V = V) :
    closure V ⊆ relationPower V 3 := by
  rintro ⟨x, y⟩ hxy
  have hN : entourageBall V x ×ˢ entourageBall V y ∈ 𝓝 (x, y) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (UniformSpace.ball_mem_nhds x hV)
      (UniformSpace.ball_mem_nhds y hV)
  obtain ⟨⟨a, b⟩, ⟨hxa, hyb⟩, hab⟩ := (mem_closure_iff_nhds.mp hxy) _ hN
  have hby : (b, y) ∈ V := by
    rw [← hsym]
    exact hyb
  exact ⟨b, ⟨a, ⟨x, rfl, hxa⟩, hab⟩, hby⟩

/-- Close a symmetric cube root of U. Its closure remains symmetric and is
an entourage because it contains that cube root. -/
theorem closed_symmetric_entourage {X : Type u} [UniformSpace X]
    (U : Set (X × X)) (hU : U ∈ 𝓤 X) :
    ∃ C ∈ 𝓤 X, IsClosed C ∧ relationInverse C = C ∧ C ⊆ U := by
  obtain ⟨V, hV, hsym, hcube⟩ := symmetric_power_entourage U hU 3 (by decide)
  refine ⟨closure V, mem_of_superset hV subset_closure, isClosed_closure, ?_,
    (closure_symmetric_entourage_subset_cube V hV hsym).trans hcube⟩
  rw [relationInverse_closure, hsym]

/-- First take a symmetric cube root T of U, then a closed symmetric
refinement C of T. Monotonicity of relational powers gives C³ ⊆ U. -/
theorem closed_symmetric_entourage_cube {X : Type u} [UniformSpace X]
    (U : Set (X × X)) (hU : U ∈ 𝓤 X) :
    ∃ C ∈ 𝓤 X, IsClosed C ∧ relationInverse C = C ∧
      C ⊆ U ∧ relationPower C 3 ⊆ U := by
  obtain ⟨T, hT, _, hTU, hcube⟩ := symmetric_power_refinement 3 U hU
  obtain ⟨C, hC, hclosed, hsym, hCT⟩ := closed_symmetric_entourage T hT
  exact ⟨C, hC, hclosed, hsym, hCT.trans hTU,
    (relationPower_mono hCT 3).trans hcube⟩

end D10Topology.Ch12
