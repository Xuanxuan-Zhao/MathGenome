import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.AscoliSufficiency
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.EquicontinuousClosure
import Mathlib.Topology.UniformSpace.Ascoli

/-! Ascoli sufficiency for an arbitrary topological domain and metric target.
Take the pointwise closure in the space of all maps. It is a closed subset
of the product of the compact pointwise closures. Equicontinuity ensures
that its maps are continuous and that its compact-open topology agrees
with its pointwise topology. It is therefore a compact, closed superset
of the original family in the Hausdorff continuous-map space. -/

noncomputable section
open Set Filter
open scoped Topology
universe u v

namespace D10Topology.Ch13

theorem ascoli_sufficiency
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (A : Set (ContinuousMaps X Y))
    (hA : Equicontinuous A) (hpoint : PointwiseRelativelyCompact A) :
    @IsCompact (ContinuousMaps X Y) compactOpenContinuousTopology
      (@closure (ContinuousMaps X Y) compactOpenContinuousTopology A) := by
  rw [compactOpenContinuousTopology_eq_mathlib]
  let H : Set (X → Y) := closure ((fun f : ContinuousMaps X Y => (f : X → Y)) '' A)
  have hHcompact : IsCompact H := by
    apply (isCompact_pi_infinite hpoint).of_isClosed_subset isClosed_closure
    intro g hg x
    have h := image_closure_subset_closure_image (continuous_apply x)
      (mem_image_of_mem (fun f : X → Y => f x) hg)
    simpa only [image_image, Function.comp_def] using h
  have hHcontinuous : ∀ g ∈ H, Continuous g :=
    pointwise_closure_continuous A hA
  let S : Set (ContinuousMaps X Y) := {f | (f : X → Y) ∈ H}
  have himage : ContinuousMap.toFun '' S = H := by
    apply Subset.antisymm
    · rintro _ ⟨f, hf, rfl⟩
      exact hf
    · intro g hg
      exact ⟨⟨g, hHcontinuous g hg⟩, hg, rfl⟩
  have hScont : Equicontinuous S := by
    intro x ε hε
    obtain ⟨U, hU, heq⟩ := pointwise_closure_equicontinuous A hA x ε hε
    exact ⟨U, hU, fun y hy f hf => heq y hy f hf⟩
  have hScompact : IsCompact S :=
    ArzelaAscoli.isCompact_of_equicontinuous S
      (himage.symm ▸ hHcompact) ((equicontinuous_iff_mathlib S).mp hScont)
  have hAS : A ⊆ S := by
    intro f hf
    exact subset_closure (mem_image_of_mem (fun f : ContinuousMaps X Y => (f : X → Y)) hf)
  exact hScompact.of_isClosed_subset isClosed_closure
    (closure_minimal hAS hScompact.isClosed)

end D10Topology.Ch13
