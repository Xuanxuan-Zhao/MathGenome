import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.TopologyComparison
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformContinuity
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! The topology comparisons in d10:13:topology-comparison. -/
noncomputable section
open Set Filter
open scoped Topology Uniformity
universe u v
namespace D10Topology.Ch13
variable {X : Type u} {Y : Type v}

section Comparisons
variable [TopologicalSpace X] [MetricSpace Y]

theorem compactConvergenceTopology_le_pointwiseTopology :
    compactConvergenceTopology (X := X) (Y := Y) ≤ pointwiseTopology := by
  apply continuous_id_iff_le.mp
  letI : UniformSpace (X → Y) := compactConvergenceUniformity
  have ho : UniformContinuous
      (UniformOnFun.ofFun {K : Set X | IsCompact K} : (X → Y) → _) :=
    uniformContinuous_comap
  have he (x : X) : @Continuous (X → Y) Y compactConvergenceTopology _ (fun f => f x) :=
    ((UniformOnFun.uniformContinuous_eval_of_mem Y {K : Set X | IsCompact K}
      (mem_singleton x) isCompact_singleton).comp ho).continuous
  exact @continuous_pi (X → Y) X (fun _ => Y) compactConvergenceTopology _ id he

theorem uniformTopology_le_compactConvergenceTopology :
    uniformTopology (X := X) (Y := Y) ≤ compactConvergenceTopology := by
  apply le_of_nhds_le_nhds
  intro f
  refine (uniform_nhds_hasBasis f).le_basis_iff (compactConvergence_nhds_hasBasis f) |>.mpr ?_
  rintro ⟨K, ε⟩ ⟨hK, hε⟩
  refine ⟨ε, hε, ?_⟩
  intro g hg
  exact lt_of_le_of_lt ((compactDistance_le K f g _ (uniformDistance_nonneg f g)).mpr
    fun x _ => boundedDistance_le_uniformDistance f g x) hg

theorem continuous_topology_comparisons :
    uniformContinuousTopology (X := X) (Y := Y) ≤ compactConvergenceContinuousTopology ∧
    compactConvergenceContinuousTopology (X := X) (Y := Y) ≤ pointwiseContinuousTopology := by
  rw [compactConvergenceContinuousTopology_eq_induced]
  exact ⟨induced_mono uniformTopology_le_compactConvergenceTopology,
    induced_mono compactConvergenceTopology_le_pointwiseTopology⟩

theorem compactConvergenceContinuousTopology_eq_compactOpen :
    compactConvergenceContinuousTopology (X := X) (Y := Y) = compactOpenContinuousTopology := by
  rw [compactOpenContinuousTopology_eq_mathlib]
  have h := ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
    (α := X) (β := Y) |>.isInducing.eq_induced
  rw [compactConvergenceContinuousTopology_eq_induced]
  change TopologicalSpace.induced _ (UniformSpace.comap _ _).toTopologicalSpace = _
  rw [UniformSpace.toTopologicalSpace_comap, induced_compose]
  exact h.symm

theorem compactDomain_compactConvergenceTopology_eq_uniform [CompactSpace X] :
    compactConvergenceTopology (X := X) (Y := Y) = uniformTopology := by
  apply le_antisymm _ uniformTopology_le_compactConvergenceTopology
  apply le_of_nhds_le_nhds
  intro f
  refine (compactConvergence_nhds_hasBasis f).le_basis_iff (uniform_nhds_hasBasis f) |>.mpr ?_
  intro ε hε
  refine ⟨(univ, ε), ⟨isCompact_univ, hε⟩, ?_⟩
  intro g hg
  have he : compactDistance univ f g = uniformDistance f g := by
    apply le_antisymm
    · exact (compactDistance_le _ _ _ _ (uniformDistance_nonneg f g)).mpr
        fun x _ => boundedDistance_le_uniformDistance f g x
    · exact (uniformDistance_le _ _ _ (compactDistance_nonneg univ f g)).mpr
        fun x => boundedDistance_le_compactDistance univ f g x (mem_univ x)
  simpa only [compactBall, Specs.D10Topology.Ch13.FunctionTopologies.compactBall,
    mem_ofPred_eq, he] using hg

theorem compactDomain_continuousTopologies_eq [CompactSpace X] :
    compactConvergenceContinuousTopology (X := X) (Y := Y) = uniformContinuousTopology ∧
    compactOpenContinuousTopology (X := X) (Y := Y) = uniformContinuousTopology := by
  have h : compactConvergenceContinuousTopology (X := X) (Y := Y) = uniformContinuousTopology := by
    rw [compactConvergenceContinuousTopology_eq_induced,
      compactDomain_compactConvergenceTopology_eq_uniform]
    rfl
  exact ⟨h, compactConvergenceContinuousTopology_eq_compactOpen.symm.trans h⟩

end Comparisons
/-- The compact-open topology uses only the fixed target topology. -/
theorem compactDomain_uniformTopology_eq_of_compatible
    [TopologicalSpace X] [CompactSpace X] (tY : TopologicalSpace Y) (m : MetricSpace Y)
    (hm : m.toUniformSpace.toTopologicalSpace = tY) :
    TopologicalSpace.induced (fun f : @ContinuousMap X Y _ tY => (f : X → Y))
      (@uniformTopology X Y m) =
    @compactOpenContinuousTopology X Y _ tY := by
  subst tY
  exact (@compactDomain_continuousTopologies_eq X Y _ m _).2.symm

theorem compactDomain_uniformTopology_metric_independent
    [TopologicalSpace X] [CompactSpace X] (tY : TopologicalSpace Y) (m₁ m₂ : MetricSpace Y)
    (h₁ : m₁.toUniformSpace.toTopologicalSpace = tY)
    (h₂ : m₂.toUniformSpace.toTopologicalSpace = tY) :
    TopologicalSpace.induced (fun f : @ContinuousMap X Y _ tY => (f : X → Y))
      (@uniformTopology X Y m₁) =
    TopologicalSpace.induced (fun f : @ContinuousMap X Y _ tY => (f : X → Y))
      (@uniformTopology X Y m₂) :=
  (compactDomain_uniformTopology_eq_of_compatible tY m₁ h₁).trans
    (compactDomain_uniformTopology_eq_of_compatible tY m₂ h₂).symm

/-- Constant maps from a singleton recover exactly the target uniformity. -/
theorem singleton_uniformity_comap [MetricSpace Y] :
    UniformSpace.comap (fun y : Y => fun _ : Unit => y)
      (uniformUniformity (X := Unit) (Y := Y)) = (inferInstance : UniformSpace Y) := by
  apply UniformSpace.ext
  change comap _ (comap _ (@uniformity (UniformFun Unit Y) _)) = _
  rw [Filter.comap_comap]
  have hb := (UniformFun.hasBasis_uniformity Unit Y).comap
    (fun p : Y × Y => (UniformFun.ofFun (fun _ : Unit => p.1),
      UniformFun.ofFun (fun _ : Unit => p.2)))
  have hh : (@uniformity Y inferInstance).HasBasis (fun V => V ∈ 𝓤 Y)
      (fun V => {p : Y × Y | ∀ _ : Unit, p ∈ V}) := by
    exact (𝓤 Y).basis_sets.congr (fun _ => Iff.rfl) (fun V _ => by
      ext p
      simp)
  exact hb.eq_of_same_basis hh

theorem targetMetric_uniformity_counterexample :
    Ch12.arctanMetric.toUniformSpace.toTopologicalSpace =
      Ch12.usualRealMetric.toUniformSpace.toTopologicalSpace ∧
    @uniformUniformity Unit ℝ Ch12.arctanMetric ≠
      @uniformUniformity Unit ℝ Ch12.usualRealMetric := by
  refine ⟨Ch12.arctanMetric_topology, ?_⟩
  intro heq
  apply Ch12.arctanMetric_uniformity_ne
  have h := congrArg (UniformSpace.comap (fun y : ℝ => fun _ : Unit => y)) heq
  simpa only [singleton_uniformity_comap] using h

end D10Topology.Ch13
