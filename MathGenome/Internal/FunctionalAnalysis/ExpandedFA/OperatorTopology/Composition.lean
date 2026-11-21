import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OperatorTopology.Composition
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.OperatorTopology.ContinuousDuals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import Mathlib.Analysis.Normed.Group.Bounded

/-! Composition in SOT and WOT, completing `fa2:p1:operator-topologies`.
Fixed factors act continuously by the defining vector and dual tests.
For varying factors, a full uniform bound on the outer operators controls
Tᵢ(Sᵢx − Sx), while strong convergence controls Tᵢ(Sx).
For sequences on a Banach intermediate space, Banach–Steinhaus supplies
that bound; neither endpoint space is assumed complete.
-/

namespace ExpandedFA.OperatorTopology
open scoped Topology
noncomputable section

theorem operator_topology_structure : CompositionSpec.Structure :=
  ⟨strong_hausdorff, weak_hausdorff, strong_vector_topology, weak_vector_topology,
    strong_locally_convex, weak_locally_convex, topology_comparison,
    strong_dual_finite_sum, weak_dual_finite_sum, operator_duals_equal,
    closed_convex_sets_equal⟩

theorem strong_comp_left_continuous : CompositionSpec.StrongLeft := by
  intro 𝕜 E F G _ _ _ _ _ _ _ A
  let : TopologicalSpace (E →L[𝕜] F) := strongTopology 𝕜 E F
  change @Continuous _ _ _ (TopologicalSpace.induced _ _) _
  rw [continuous_induced_rng, continuous_pi_iff]
  intro x
  exact A.continuous.comp ((continuous_pi_iff.mp continuous_induced_dom) x)

theorem strong_comp_right_continuous : CompositionSpec.StrongRight := by
  intro 𝕜 E F G _ _ _ _ _ _ _ B
  let : TopologicalSpace (F →L[𝕜] G) := strongTopology 𝕜 F G
  change @Continuous _ _ _ (TopologicalSpace.induced _ _) _
  rw [continuous_induced_rng, continuous_pi_iff]
  intro x
  exact (continuous_pi_iff.mp continuous_induced_dom) (B x)

theorem weak_comp_left_continuous : CompositionSpec.WeakLeft := by
  intro 𝕜 E F G _ _ _ _ _ _ _ A
  let : TopologicalSpace (E →L[𝕜] F) := weakTopology 𝕜 E F
  change @Continuous _ _ _ (TopologicalSpace.induced _ _) _
  rw [continuous_induced_rng, continuous_pi_iff]
  intro p
  exact (weak_coarsest 𝕜 E F _).mpr le_rfl p.1 (p.2.comp A)

theorem weak_comp_right_continuous : CompositionSpec.WeakRight := by
  intro 𝕜 E F G _ _ _ _ _ _ _ B
  let : TopologicalSpace (F →L[𝕜] G) := weakTopology 𝕜 F G
  change @Continuous _ _ _ (TopologicalSpace.induced _ _) _
  rw [continuous_induced_rng, continuous_pi_iff]
  intro p
  exact (weak_coarsest 𝕜 F G _).mpr le_rfl (B p.1) p.2

theorem bounded_strong_comp_tendsto : CompositionSpec.BoundedStrongComposition := by
  intro 𝕜 E F G _ _ _ _ _ _ _ ι l S T S₀ T₀ hS hT hbound
  obtain ⟨C, _, hC⟩ := hbound
  apply (strong_tendsto_iff 𝕜 E G ι l _ _).mpr
  intro x
  have hSx := (strong_tendsto_iff 𝕜 E F ι l S S₀).mp hS x
  have hTx := (strong_tendsto_iff 𝕜 F G ι l T T₀).mp hT (S₀ x)
  have hz : Filter.Tendsto (fun i => T i (S i x - S₀ x)) l (𝓝 0) := by
    refine squeeze_zero_norm (a := fun i => C * ‖S i x - S₀ x‖) ?_ ?_
    · intro i
      exact ((T i).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _))
    · have h := (tendsto_const_nhds (x := C)).mul ((hSx.sub_const (S₀ x)).norm)
      simpa only [sub_self, norm_zero, mul_zero] using h
  simpa only [map_sub, sub_add_cancel, zero_add, ContinuousLinearMap.comp_apply]
    using hz.add hTx

theorem strong_sequence_uniform_bound : CompositionSpec.StrongSequenceBound := by
  intro 𝕜 F G _ _ _ _ _ _ T T₀ hT
  apply ExpandedFA.P1.C07UniformBoundedness.uniform_boundedness 𝕜 F G ℕ T
  intro x
  have hx := (strong_tendsto_iff 𝕜 F G ℕ Filter.atTop T T₀).mp hT x
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto (fun n => T n x) hx))
  exact ⟨C, fun n => hC _ (Set.mem_range_self n)⟩

theorem strong_sequence_comp_tendsto : CompositionSpec.StrongSequenceComposition := by
  intro 𝕜 E F G _ _ _ _ _ _ _ _ S T S₀ T₀ hS hT
  exact bounded_strong_comp_tendsto 𝕜 E F G ℕ Filter.atTop S T S₀ T₀ hS hT
    (strong_sequence_uniform_bound 𝕜 F G T T₀ hT)

end
end ExpandedFA.OperatorTopology
