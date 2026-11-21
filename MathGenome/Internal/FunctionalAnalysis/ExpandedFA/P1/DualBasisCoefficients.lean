import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DualBasisCoefficients
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.DualBasisBasicity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry
import Mathlib.Analysis.Normed.Module.WeakDual

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.DualBasisCoefficients
open ExpandedFA.P1.DualBasisBasicity hiding dualSpan dualVector IsShrinking IsBoundedlyComplete tailSpace
open ExpandedFA.P1.DualBasisBasicity.Spec (dualSpan dualVector IsShrinking IsBoundedlyComplete)
open ExpandedFA.P1.DualBasisCoefficients.Spec (evaluation coefficients)
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- Use the native operator-norm structures explicitly for nested duals.
local instance : NormedAddCommGroup (E →L[𝕜] 𝕜) := inferInstance
local instance : NormedSpace 𝕜 (E →L[𝕜] 𝕜) := inferInstance
local instance (b : SchauderBasis 𝕜 E) : NormedAddCommGroup (dualSpan b →L[𝕜] 𝕜) := inferInstance
local instance (b : SchauderBasis 𝕜 E) : NormedSpace 𝕜 (dualSpan b →L[𝕜] 𝕜) := inferInstance
local instance (b : SchauderBasis 𝕜 E) : CompleteSpace (dualSpan b) :=
  Submodule.topologicalClosure.completeSpace _

@[simp] theorem evaluation_apply (b : SchauderBasis 𝕜 E) (x : E) (f : dualSpan b) :
    evaluation b x f = f.val x := rfl

@[simp] theorem coefficients_evaluation (b : SchauderBasis 𝕜 E) (x : E) :
    coefficients b (evaluation b x) = fun i => b.coord i x := rfl

theorem coefficients_injective [CompleteSpace E] (b : SchauderBasis 𝕜 E) :
    Function.Injective (coefficients b) := by
  obtain ⟨d, hd, hc⟩ := dual_basis_construction b
  intro Φ Ψ h
  apply ContinuousLinearMap.ext
  intro f
  have he (i : ℕ) : Φ (d i) = Ψ (d i) := by
    rw [hd]
    exact congrFun h i
  have ht := Φ.continuous.tendsto f |>.comp (d.tendsto_proj f)
  have hu := Ψ.continuous.tendsto f |>.comp (d.tendsto_proj f)
  have heq : (fun N => Φ (d.proj N f)) = (fun N => Ψ (d.proj N f)) := by
    funext N
    simp only [SchauderBasis.proj_apply, map_sum, map_smul, he]
  simp only [Function.comp_def] at ht hu
  rw [heq] at ht
  exact tendsto_nhds_unique ht hu

theorem coord_partial (b : SchauderBasis 𝕜 E) (a : ℕ → 𝕜) (N i : ℕ) :
    b.coord i (ExpandedFA.P1.C15Basis.Spec.orderedPartialSum b.basis a N) =
      if i < N then a i else 0 := by
  classical
  simp [ExpandedFA.P1.C15Basis.Spec.orderedPartialSum, b.ortho, Pi.single_apply]

/-- The coefficient sums of an arbitrary element of F' have the uniform
bound supplied by the primal basis constant. -/
theorem coefficient_sum_bound [CompleteSpace E] (b : SchauderBasis 𝕜 E)
    {C : ℝ} (hC : ∀ N, ‖b.proj N‖ ≤ C) (Φ : dualSpan b →L[𝕜] 𝕜) (N : ℕ) :
    ‖ExpandedFA.P1.C15Basis.Spec.orderedPartialSum b.basis (coefficients b Φ) N‖ ≤
      C * ‖Φ‖ := by
  let s := ExpandedFA.P1.C15Basis.Spec.orderedPartialSum b.basis (coefficients b Φ) N
  have hC0 : 0 ≤ C := (norm_nonneg (b.proj 0)).trans (hC 0)
  rw [(C05BidualIsometry.dual_norm_formula 𝕜 E s).1]
  apply csSup_le
  · exact ⟨0, 0, by simp, by simp⟩
  · rintro _ ⟨f, hf, rfl⟩
    let g : dualSpan b := ⟨dualProjection b N f, dualProjection_mem b N f⟩
    have he : f s = Φ g := by
      change f (∑ i ∈ Finset.range N, coefficients b Φ i • b i) = Φ g
      have hg : g = ∑ i ∈ Finset.range N, f (b i) • dualVector b i := by
        apply Subtype.ext
        simpa only [g, Submodule.coe_sum, Submodule.coe_smul,
          ExpandedFA.P1.DualBasisBasicity.Spec.dualVector] using dualProjection_eq_sum b N f
      rw [hg]
      simp [coefficients, mul_comm]
    change ‖f s‖ ≤ C * ‖Φ‖
    rw [he]
    calc
      ‖Φ g‖ ≤ ‖Φ‖ * ‖g‖ := Φ.le_opNorm g
      _ ≤ ‖Φ‖ * (‖f‖ * C) := by
        gcongr
        exact (f.opNorm_comp_le (b.proj N)).trans
          (mul_le_mul_of_nonneg_left (hC N) (norm_nonneg f))
      _ ≤ ‖Φ‖ * (1 * C) := by gcongr; exact hf
      _ = C * ‖Φ‖ := by ring

/-- The evaluation map is contractive, before using completeness. -/
theorem evaluation_norm_le (b : SchauderBasis 𝕜 E) (x : E) :
    ‖evaluation b x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
  intro f
  simpa only [evaluation_apply, Submodule.norm_coe, mul_comm] using f.val.le_opNorm x

/-- Existence uses a weak-star cluster point of the uniformly bounded
restricted evaluations of the primal partial sums. -/
theorem exists_of_bounded (b : SchauderBasis 𝕜 E) (a : ℕ → 𝕜)
    (ha : BddAbove (Set.range fun N =>
      ‖ExpandedFA.P1.C15Basis.Spec.orderedPartialSum b.basis a N‖)) :
    ∃ Φ : dualSpan b →L[𝕜] 𝕜, coefficients b Φ = a := by
  obtain ⟨M, hM⟩ := ha
  let s := ExpandedFA.P1.C15Basis.Spec.orderedPartialSum b.basis a
  let u : ℕ → WeakDual 𝕜 (dualSpan b) := fun N => StrongDual.toWeakDual (evaluation b (s N))
  have hu : ∀ N, u N ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : dualSpan b →L[𝕜] 𝕜) M := by
    intro N
    simpa only [u, Set.mem_preimage, Metric.mem_closedBall,
      StrongDual.toStrongDual_toWeakDual, dist_zero_right] using
      (evaluation_norm_le b (s N)).trans (hM (Set.mem_range_self N))
  obtain ⟨Φ, _, hΦ⟩ := (WeakDual.isCompact_closedBall
    (0 : dualSpan b →L[𝕜] 𝕜) M).exists_mapClusterPt (u := u) (f := atTop)
      (Filter.tendsto_principal.mpr (Eventually.of_forall hu))
  refine ⟨Φ.toStrongDual, funext fun i => ?_⟩
  have hclosed : IsClosed {Ψ : WeakDual 𝕜 (dualSpan b) | Ψ (dualVector b i) = a i} :=
    isClosed_eq (WeakDual.eval_continuous _) continuous_const
  apply hclosed.mem_of_mapClusterPt hΦ
  filter_upwards [eventually_gt_atTop i] with N hN
  change b.coord i (s N) = a i
  exact (coord_partial b a N i).trans (ite_eq_left hN)

theorem coefficient_representation : Spec.CoefficientRepresentation := by
  intro 𝕜 E _ _ _ _ b a
  constructor
  · rintro ⟨Φ, hΦ, _⟩
    obtain ⟨C, hC⟩ := b.exists_norm_proj_le
    refine ⟨C * ‖Φ‖, ?_⟩
    rintro _ ⟨N, rfl⟩
    rw [← hΦ]
    exact coefficient_sum_bound b hC Φ N
  · intro ha
    obtain ⟨Φ, hΦ⟩ := exists_of_bounded b a ha
    exact ⟨Φ, hΦ, fun Ψ hΨ => coefficients_injective b (hΨ.trans hΦ.symm)⟩

/-- Norm convergence of the primal series forces the prescribed coordinates. -/
theorem coordinates_of_converges (b : SchauderBasis 𝕜 E) (a : ℕ → 𝕜) {x : E}
    (hx : Tendsto (ExpandedFA.P1.C15Basis.Spec.orderedPartialSum b.basis a) atTop (𝓝 x)) :
    (fun i => b.coord i x) = a := by
  funext i
  have ht := (b.coord i).continuous.tendsto x |>.comp hx
  have he : Tendsto (fun N => b.coord i
      (ExpandedFA.P1.C15Basis.Spec.orderedPartialSum b.basis a N)) atTop (𝓝 (a i)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with N hN
    rw [coord_partial, ite_eq_left hN]
  exact tendsto_nhds_unique ht he

theorem evaluation_image : Spec.EvaluationImage := by
  intro 𝕜 E _ _ _ _ b Φ
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    change Tendsto (fun N => ∑ i ∈ Finset.range N, b.coord i x • b i) atTop (𝓝 x)
    simpa only [SchauderBasis.proj_apply] using b.tendsto_proj x
  · rintro ⟨x, hx⟩
    refine ⟨x, coefficients_injective b ?_⟩
    rw [coefficients_evaluation]
    exact coordinates_of_converges b _ hx

/-- F norms E up to the basis constant. Consequently the restricted canonical
image is closed in F', which is essential for the shrinking equivalence. -/
theorem evaluation_lower_bound [CompleteSpace E] (b : SchauderBasis 𝕜 E)
    {C : ℝ} (hC : ∀ N, ‖b.proj N‖ ≤ C) (x : E) :
    ‖x‖ ≤ C * ‖evaluation b x‖ := by
  apply le_of_tendsto (b.tendsto_proj x).norm
  apply Eventually.of_forall
  intro N
  simpa only [coefficients_evaluation, ExpandedFA.P1.C15Basis.Spec.orderedPartialSum,
    SchauderBasis.proj_apply] using coefficient_sum_bound b hC (evaluation b x) N

theorem evaluation_closed_range [CompleteSpace E] (b : SchauderBasis 𝕜 E) :
    IsClosed (Set.range (evaluation b)) := by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hC0 : 0 ≤ C := (norm_nonneg (b.proj 0)).trans (hC 0)
  exact ((evaluation b).antilipschitz_of_bound
    (K := ⟨C, hC0⟩) (evaluation_lower_bound b hC)).isClosed_range
      (evaluation b).uniformContinuous

/-- The coordinates of the dual basic sequence are restrictions of J_E(b_i). -/
theorem evaluation_basis (b : SchauderBasis 𝕜 E) (d : SchauderBasis 𝕜 (dualSpan b))
    (hc : ∀ i f, d.coord i f = f.val (b i)) (i : ℕ) :
    evaluation b (b i) = d.coord i := by
  ext f
  exact (hc i f).symm

theorem evaluation_closed_span : Spec.EvaluationClosedSpan := by
  intro 𝕜 E _ _ _ _ b d _ hc
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
      ((evaluation b).continuous.tendsto x |>.comp (b.tendsto_proj x))
    apply Eventually.of_forall
    intro N
    change evaluation b (b.proj N x) ∈ _
    rw [SchauderBasis.proj_apply, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul, evaluation_basis b d hc]
    exact Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _
      (Submodule.subset_span (Set.mem_range_self i)))
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨b i, evaluation_basis b d hc i⟩
    · exact evaluation_closed_range b

theorem evaluation_surjective_iff [CompleteSpace E] (b : SchauderBasis 𝕜 E) :
    Function.Surjective (evaluation b) ↔ IsBoundedlyComplete (𝕜 := 𝕜) b.basis := by
  constructor
  · intro h a ha
    obtain ⟨Φ, hΦ, _⟩ := (coefficient_representation b a).mpr ha
    obtain ⟨x, hx⟩ := h Φ
    have him := (evaluation_image b Φ).mp ⟨x, hx⟩
    rwa [hΦ] at him
  · intro h Φ
    obtain ⟨C, hC⟩ := b.exists_norm_proj_le
    have hb : BddAbove (Set.range fun N =>
        ‖ExpandedFA.P1.C15Basis.Spec.orderedPartialSum b.basis (coefficients b Φ) N‖) := by
      refine ⟨C * ‖Φ‖, ?_⟩
      rintro _ ⟨N, rfl⟩
      exact coefficient_sum_bound b hC Φ N
    exact (evaluation_image b Φ).mpr (h _ hb)

theorem shrinking_boundedly_complete : Spec.ShrinkingBoundedlyComplete := by
  intro 𝕜 E _ _ _ _ b d hd hc
  calc
    IsShrinking d ↔ dualSpan d = ⊤ := shrinking_iff_dualSpan d
    _ ↔ (evaluation b).range = ⊤ := by
      rw [evaluation_closed_span b d hd hc]
      rfl
    _ ↔ Function.Surjective (evaluation b) := LinearMap.range_eq_top
    _ ↔ IsBoundedlyComplete (𝕜 := 𝕜) b.basis := evaluation_surjective_iff b

theorem dual_shrinking_criterion : Spec.DualShrinkingCriterion := by
  intro 𝕜 E _ _ _ _ b
  obtain ⟨d, hd, hc⟩ := dual_basis_construction b
  exact ⟨d, hd, hc, shrinking_boundedly_complete b d hd hc⟩

theorem raw_dual_shrinking_criterion : Spec.RawDualShrinkingCriterion := by
  intro 𝕜 E _ _ _ _ e h
  obtain ⟨b, he, hc, _⟩ := ExpandedFA.P1.C15CoordinateContinuity.raw_native_basis h
  obtain ⟨d, hd, hdc, hiff⟩ := dual_shrinking_criterion b
  refine ⟨b, he, hc, d, hd, hdc, ?_⟩
  rwa [he] at hiff

/-- Finite coefficient synthesis also covers the zero-dimensional boundary. -/
theorem finite_coefficient_model : Spec.FiniteCoefficientModel := by
  intro 𝕜 E _ _ _ n b
  classical
  let F := (Submodule.span 𝕜 (Set.range b.coord)).topologicalClosure
  let e' : Fin n → F := fun i => ⟨b.coord i, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self i))⟩
  let ev : E →L[𝕜] (F →L[𝕜] 𝕜) := F.subtypeL.flip
  have hexp (x : E) : ∑ i, b.coord i x • b i = x :=
    (hasSum_fintype _).unique (b.expansion x)
  have hdual (f : E →L[𝕜] 𝕜) : ∑ i, f (b i) • b.coord i = f := by
    ext x
    simpa [map_sum, map_smul, mul_comm] using congrArg f (hexp x)
  have hF (f : F) : ∑ i, f.val (b i) • e' i = f := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hdual f.val
  have hev (Φ : F →L[𝕜] 𝕜) : ev (∑ i, Φ (e' i) • b i) = Φ := by
    ext f
    change f.val (∑ i, Φ (e' i) • b i) = Φ f
    calc
      _ = ∑ i, f.val (b i) • Φ (e' i) := by simp [map_sum, map_smul, mul_comm]
      _ = Φ (∑ i, f.val (b i) • e' i) := by simp only [map_sum, map_smul]
      _ = Φ f := congrArg Φ (hF f)
  have hinj (Φ Ψ : F →L[𝕜] 𝕜) (h : ∀ i, Φ (e' i) = Ψ (e' i)) : Φ = Ψ := by
    ext f
    rw [← hF f]
    simp only [map_sum, map_smul, h]
  refine ⟨?_, hev, ?_, ?_⟩
  · intro a
    refine ⟨ev (∑ i, a i • b i), ?_, ?_⟩
    · intro i
      change b.coord i (∑ j, a j • b j) = a i
      simp [map_sum, map_smul, b.ortho, Pi.single_apply]
    · intro Ψ hΨ
      apply hinj
      intro i
      rw [hΨ]
      change a i = b.coord i (∑ j, a j • b j)
      simp [map_sum, map_smul, b.ortho, Pi.single_apply]
  · intro Φ
    simpa only [map_sum, map_smul] using hev Φ
  · intro a
    constructor
    · refine ⟨∑ i, ‖a i • b i‖, ?_⟩
      rintro _ ⟨N, rfl⟩
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with N hN
      have hs : Finset.univ.filter (fun i : Fin n => i.val < N) = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro i _
        exact i.isLt.trans_le hN
      rw [hs]

end ExpandedFA.P1.DualBasisCoefficients
