import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.KreinSmulian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BoundedWeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.LcsStrongSeparation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Metric
import Mathlib.Analysis.LocallyConvex.Separation

/-! Krein–Šmulian for Banach preduals, `fa2:p1:krein-smulian`.
A beta-closed convex set can be separated by beta-continuous functionals.
The accepted beta-dual identification makes each separator an evaluation,
so the same set is weak-star closed. -/

open Set Filter Topology
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ExpandedFA.P1.KreinSmulian

universe u v

section
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma weakStar_evaluation_continuous (x : E) :
    @Continuous (E →L[𝕜] 𝕜) 𝕜 (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      inferInstance (fun f => f x) := by
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  have he : IsInducing (StrongDual.toWeakDual : (E →L[𝕜] 𝕜) → WeakDual 𝕜 E) :=
    ⟨C12WeakStar.weakStarTopology_native 𝕜 E⟩
  exact (WeakDual.eval_continuous (𝕜 := 𝕜) x).comp he.continuous

lemma weakStar_ball_isClosed (r : ℝ) :
    @IsClosed (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ r} := by
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  have he : IsInducing (StrongDual.toWeakDual : (E →L[𝕜] 𝕜) → WeakDual 𝕜 E) :=
    ⟨C12WeakStar.weakStarTopology_native 𝕜 E⟩
  simpa only [Metric.closedBall, dist_zero_right, Set.preimage_ofPred_eq, StrongDual.toStrongDual_toWeakDual] using
    (WeakDual.isClosed_closedBall (𝕜 := 𝕜) (E := E) 0 r).preimage he.continuous

lemma weakStar_isClosed_of_beta [CompleteSpace E] (C : Set (E →L[𝕜] 𝕜))
    (hv : Convex ℝ C)
    (hc : @IsClosed _ (BoundedWeakstarTopology.Spec.TopologyValue 𝕜 E) C) :
    @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) C := by
  have hsep : ∀ f ∉ C, ∃ (x : E) (a : ℝ),
      (∀ g ∈ C, RCLike.re (g x) < a) ∧ a < RCLike.re (f x) := by
    intro f hf
    let : TopologicalSpace (E →L[𝕜] 𝕜) := BoundedWeakstarTopology.Spec.TopologyValue 𝕜 E
    obtain ⟨⟨⟨hadd, hsmul⟩, hlc⟩, ht2, _⟩ :=
      BoundedWeakstarTopology.topology_construction 𝕜 E
    let : IsTopologicalAddGroup (E →L[𝕜] 𝕜) := hadd
    let : ContinuousSMul 𝕜 (E →L[𝕜] 𝕜) := hsmul
    let : LocallyConvexSpace ℝ (E →L[𝕜] 𝕜) := hlc
    obtain ⟨L, a, hL, hfL⟩ :=
      RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) hv hc hf
    obtain ⟨x, hx, _⟩ :=
      (BoundedWeakstarDual.continuous_dual_identification 𝕜 E L.toLinearMap).mp L.continuous
    have hx' : ∀ g, L g = g x := hx
    exact ⟨x, a, fun g hg => by simpa only [← hx' g] using hL g hg,
      by simpa only [← hx' f] using hfL⟩
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro f hf
  obtain ⟨x, a, hx, ha⟩ := hsep f hf
  refine ⟨{g | a < RCLike.re (g x)}, ?_, ?_, ha⟩
  · intro g hg hgC
    exact (hx g hgC).not_gt hg
  · exact isOpen_lt continuous_const (RCLike.continuous_re.comp (weakStar_evaluation_continuous x))

lemma weakStar_const_smul_continuous (c : 𝕜) :
    @Continuous (E →L[𝕜] 𝕜) (E →L[𝕜] 𝕜)
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) (fun f => c • f) := by
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  have he : IsInducing (StrongDual.toWeakDual : (E →L[𝕜] 𝕜) → WeakDual 𝕜 E) :=
    ⟨C12WeakStar.weakStarTopology_native 𝕜 E⟩
  apply he.continuous_iff.mpr
  exact he.continuous.const_smul c

end

theorem convex_closed_criterion : Spec.ConvexClosedCriterion := by
  intro 𝕜 E _ _ _ _ C hv
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  constructor
  · intro hc r _
    exact hc.inter (weakStar_ball_isClosed r)
  · intro hc
    exact weakStar_isClosed_of_beta C hv
      ((BoundedWeakstarTopology.closed_criterion 𝕜 E C).mpr hc)

/-- Homogeneity reduces all positive-radius slices of a subspace to its unit slice. -/
theorem subspace_closed_criterion : Spec.SubspaceClosedCriterion := by
  intro 𝕜 E _ _ _ _ M
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  constructor
  · intro hc
    exact hc.inter (weakStar_ball_isClosed 1)
  · intro hc
    apply (convex_closed_criterion 𝕜 E (M : Set _) (M.restrictScalars ℝ).convex).mpr
    intro r hr
    have hne : (r : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hr.ne'
    have heq : (fun f : E →L[𝕜] 𝕜 => (r : 𝕜)⁻¹ • f) ⁻¹'
        ((M : Set _) ∩ {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ 1}) =
        (M : Set _) ∩ {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ r} := by
      ext f
      simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, SetLike.mem_coe,
        M.smul_mem_iff (inv_ne_zero hne), norm_smul, norm_inv,
        RCLike.norm_ofReal, abs_of_pos hr]
      rw [inv_mul_le_iff₀ hr, mul_one]
    rw [← heq]
    exact hc.preimage (weakStar_const_smul_continuous (r : 𝕜)⁻¹)

/-- Metrizability on each bounded dual ball turns sequential closedness into
relative closedness; Krein–Šmulian then gives ambient closedness. -/
theorem sequential_closed_criterion : Spec.SequentialClosedCriterion := by
  intro 𝕜 E _ _ _ _ _ C hv
  let : TopologicalSpace (E →L[𝕜] 𝕜) := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  constructor
  · exact IsClosed.isSeqClosed
  · intro hs
    apply (convex_closed_criterion 𝕜 E C hv).mpr
    intro r hr
    apply BoundedWeakstarTopology.weakstar_slice_closed_of_relative C r hr.le
    let A : Set (E →L[𝕜] 𝕜) := {f | ‖f‖ ≤ r}
    have hA : Bornology.IsBounded A := by
      simpa only [A, Metric.closedBall, dist_zero_right] using
        (Metric.isBounded_closedBall (x := (0 : E →L[𝕜] 𝕜)) (r := r))
    obtain ⟨x, hx⟩ := C13Metric.dense_tests_exist 𝕜 E
    obtain ⟨m, _, hm⟩ := C13Metric.bounded_weakStar_metric 𝕜 E x hx A hA
    have hseq : IsSeqClosed ((Subtype.val : A → (E →L[𝕜] 𝕜)) ⁻¹' C) :=
      hs.preimage continuous_subtype_val.seqContinuous
    change @IsSeqClosed A (TopologicalSpace.induced Subtype.val
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)) _ at hseq
    change @IsClosed A (TopologicalSpace.induced Subtype.val
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)) _
    rw [← hm] at hseq ⊢
    let : MetricSpace A := m
    let : PseudoMetricSpace A := m.toPseudoMetricSpace
    let : UniformSpace A := m.toUniformSpace
    let : TopologicalSpace A := m.toUniformSpace.toTopologicalSpace
    let : FirstCountableTopology A :=
      @UniformSpace.firstCountableTopology A m.toUniformSpace
        (@EMetric.instIsCountablyGeneratedUniformity A
          (@PseudoMetricSpace.toPseudoEMetricSpace A m.toPseudoMetricSpace))
    exact hseq.isClosed

end ExpandedFA.P1.KreinSmulian
