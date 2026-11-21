import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.EquicontinuousClosure
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctionTopologies
import Mathlib.Topology.UniformSpace.Ascoli

/-! Pointwise closure and relative topologies of equicontinuous families.
This proves paper.tex, d10:13:equicontinuous-closure, for arbitrary
topological domains and metric targets. -/
noncomputable section
open Set Filter
open scoped Topology
universe u v
namespace D10Topology.Ch13
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]

private theorem pointwiseClosure_equicontinuous_mathlib
    (A : Set (ContinuousMaps X Y)) (hA : Equicontinuous A) :
    (@closure (X → Y) pointwiseTopology
      ((fun f : ContinuousMaps X Y => (f : X → Y)) '' A)).Equicontinuous := by
  apply Set.Equicontinuous.closure
  rw [Set.image_eq_range]
  exact _root_.equicontinuous_iff_range.mp ((equicontinuous_iff_mathlib A).mp hA)

theorem pointwise_closure_equicontinuous
    (A : Set (ContinuousMaps X Y)) (hA : Equicontinuous A) :
    ∀ x : X, ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 x,
      ∀ y ∈ U, ∀ g ∈ @closure (X → Y) pointwiseTopology
        ((fun f : ContinuousMaps X Y => (f : X → Y)) '' A),
        dist (g y) (g x) < ε := by
  intro x ε hε
  have h := Metric.equicontinuousAt_iff_right.mp
    (pointwiseClosure_equicontinuous_mathlib A hA x) ε hε
  refine ⟨{y | ∀ g : @closure (X → Y) pointwiseTopology
    ((fun f : ContinuousMaps X Y => (f : X → Y)) '' A),
      dist (g.val x) (g.val y) < ε}, h, ?_⟩
  intro y hy g hg
  simpa only [dist_comm] using hy ⟨g, hg⟩

theorem pointwise_closure_continuous
    (A : Set (ContinuousMaps X Y)) (hA : Equicontinuous A) :
    ∀ g ∈ @closure (X → Y) pointwiseTopology
      ((fun f : ContinuousMaps X Y => (f : X → Y)) '' A), Continuous g := by
  intro g hg
  exact (pointwiseClosure_equicontinuous_mathlib A hA).continuous ⟨g, hg⟩

theorem equicontinuous_relative_topologies_eq
    (E : Set (ContinuousMaps X Y)) (hE : Equicontinuous E) :
    TopologicalSpace.induced (fun f : E => f.val) pointwiseContinuousTopology =
    TopologicalSpace.induced (fun f : E => f.val) compactConvergenceContinuousTopology := by
  let : TopologicalSpace E :=
    TopologicalSpace.induced (fun f : E => f.val) pointwiseContinuousTopology
  have hc : ⋃₀ {K : Set X | IsCompact K} = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_sUnion.mpr ⟨{x}, isCompact_singleton, mem_singleton x⟩
  have he := (equicontinuous_iff_mathlib E).mp hE
  have hp : Topology.IsInducing (fun f : E => (f.val : X → Y)) := by
    constructor
    exact induced_compose
      (f := fun f : E => f.val) (g := fun f : ContinuousMaps X Y => (f : X → Y))
  have hu := (EquicontinuousOn.isInducing_uniformOnFun_iff_pi
    hc (fun _ hK => hK) (fun K _ => he.equicontinuousOn K)).mpr hp
  rw [compactConvergenceContinuousTopology_eq_induced, induced_compose]
  change _ = TopologicalSpace.induced _ (UniformSpace.comap
    (UniformOnFun.ofFun {K : Set X | IsCompact K})
    (UniformOnFun.uniformSpace X Y {K : Set X | IsCompact K})).toTopologicalSpace
  rw [UniformSpace.toTopologicalSpace_comap, induced_compose]
  exact hu.eq_induced

end D10Topology.Ch13
