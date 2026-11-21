import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DualBasisBasicity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15PartialSums
import Mathlib.Topology.UniformSpace.Equicontinuity

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.DualBasisBasicity
abbrev dualSpan := @Spec.dualSpan
abbrev dualVector := @Spec.dualVector
abbrev tailSpace := @Spec.tailSpace
abbrev IsShrinking := @Spec.IsShrinking
abbrev IsBoundedlyComplete := @Spec.IsBoundedlyComplete

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The transpose of an initial projection, on the normed continuous dual. -/
def dualProjection (b : SchauderBasis 𝕜 E) (N : ℕ) :
    (E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) :=
  (ContinuousLinearMap.compL 𝕜 E E 𝕜).flip (b.proj N)

@[simp] theorem dualProjection_apply (b : SchauderBasis 𝕜 E) (N : ℕ)
    (f : E →L[𝕜] 𝕜) : dualProjection b N f = f.comp (b.proj N) := rfl

/-- The transpose projection is exactly the finite dual coordinate expansion. -/
theorem dualProjection_eq_sum (b : SchauderBasis 𝕜 E) (N : ℕ)
    (f : E →L[𝕜] 𝕜) :
    dualProjection b N f = ∑ i ∈ Finset.range N, f (b i) • b.coord i := by
  ext x
  simp [SchauderBasis.proj_apply, mul_comm]

@[simp] theorem coord_projection (b : SchauderBasis 𝕜 E) (N i : ℕ) :
    (b.coord i).comp (b.proj N) = if i < N then b.coord i else 0 := by
  classical
  ext x
  by_cases hi : i < N <;> simp [SchauderBasis.proj_apply, b.ortho, Pi.single_apply, mul_comm, hi]

theorem dualProjection_mem (b : SchauderBasis 𝕜 E) (N : ℕ)
    (f : E →L[𝕜] 𝕜) : dualProjection b N f ∈ dualSpan b := by
  rw [dualProjection_eq_sum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (dualVector b i).property

/-- On the coordinate closed span the transposes converge in norm. -/
theorem mem_dualSpan_iff [CompleteSpace E] (b : SchauderBasis 𝕜 E)
    (f : E →L[𝕜] 𝕜) :
    f ∈ dualSpan b ↔ Tendsto (fun N => dualProjection b N f) atTop (𝓝 f) := by
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hC0 : 0 ≤ C := (norm_nonneg (b.proj 0)).trans (hC 0)
  have hb (N : ℕ) : ‖dualProjection b N‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC0
    intro g
    exact (g.opNorm_comp_le _).trans (by nlinarith [hC N, norm_nonneg g])
  let G : Submodule 𝕜 (E →L[𝕜] 𝕜) :=
    { carrier := {g | Tendsto (fun N => dualProjection b N g) atTop (𝓝 g)}
      zero_mem' := by simp
      add_mem' := by intro g h hg hh; simpa only [Set.mem_ofPred_eq, map_add] using hg.add hh
      smul_mem' := by intro c g hg; simpa only [Set.mem_ofPred_eq, map_smul] using hg.const_smul c }
  have hclosed : IsClosed (G : Set (E →L[𝕜] 𝕜)) := by
    have heq : Equicontinuous (fun N => fun g => dualProjection b N g) :=
      by
        have hbb : ∃ C, ∀ N, ‖dualProjection b N‖ ≤ C := ⟨C, hb⟩
        exact ((NormedSpace.equicontinuous_TFAE (dualProjection b)).out 6 2).mp hbb
    exact heq.isClosed_setOfPred_tendsto continuous_id
  constructor
  · intro hf
    apply (Submodule.topologicalClosure_minimal _ (t := G) ?_ hclosed) hf
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with N hN
    simp [hN]
  · intro hf
    exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hf
      (Eventually.of_forall (dualProjection_mem b · f))

/-- Construct the dual-coordinate basis with evaluation as its coordinates. -/
theorem dual_basis_construction : Spec.DualBasisConstruction := by
  intro 𝕜 E _ _ _ _ b
  classical
  let F := dualSpan b
  let ev (i : ℕ) : F →L[𝕜] 𝕜 :=
    (ContinuousLinearMap.apply 𝕜 𝕜 (b i)).comp F.subtypeL
  let d : SchauderBasis 𝕜 F :=
    { basis := dualVector b
      coord := ev
      ortho := by
        intro i j
        simp only [ev, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
          Submodule.subtypeL_apply, dualVector, Spec.dualVector]
        simp [b.ortho, Pi.single_apply, eq_comm]
      expansion := by
        intro f
        rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
        apply tendsto_subtype_rng.mpr
        have hf := (mem_dualSpan_iff b f.val).mp f.property
        simpa only [Function.comp_def, Submodule.coe_sum, Submodule.coe_smul,
          Spec.dualVector, dualVector, ev, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.apply_apply, Submodule.subtypeL_apply,
          dualProjection_eq_sum] using hf }
  exact ⟨d, rfl, fun _ _ => rfl⟩

/-- Native ordered Schauder bases retain the unique ordered expansion property. -/
theorem native_isRaw (b : SchauderBasis 𝕜 E) :
    ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) b.basis := by
  classical
  constructor
  · intro i hzero
    have h := b.ortho i i
    simp [hzero] at h
  · intro x
    refine ⟨fun i => b.coord i x, ?_, ?_⟩
    · change Tendsto (fun N => ∑ i ∈ Finset.range N, b.coord i x • b i) atTop (𝓝 x)
      simpa only [SchauderBasis.proj_apply] using b.tendsto_proj x
    · intro a ha
      funext i
      have hc := (b.coord i).continuous.tendsto x |>.comp ha
      have he : Tendsto (fun N => b.coord i
          (ExpandedFA.P1.C15Basis.Spec.orderedPartialSum b.basis a N)) atTop (𝓝 (a i)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop i] with N hN
        simp [ExpandedFA.P1.C15Basis.Spec.orderedPartialSum, b.ortho, Pi.single_apply, hN]
      exact tendsto_nhds_unique he hc

theorem dual_basicity : Spec.DualBasicity := by
  intro 𝕜 E _ _ _ _ b
  obtain ⟨d, hd, _⟩ := dual_basis_construction b
  rw [← hd]
  exact native_isRaw d

theorem raw_dual_basicity : Spec.RawDualBasicity := by
  intro 𝕜 E _ _ _ _ e h
  obtain ⟨b, he, hc, _⟩ := ExpandedFA.P1.C15CoordinateContinuity.raw_native_basis h
  exact ⟨b, he, hc, dual_basicity b⟩

/-- Shrinking is exactly exhaustion of the continuous dual by the closed span. -/
theorem shrinking_iff_dualSpan [CompleteSpace E] (b : SchauderBasis 𝕜 E) :
    IsShrinking b ↔ dualSpan b = ⊤ := by
  constructor
  · intro h
    apply eq_top_iff.mpr
    intro f _
    exact (mem_dualSpan_iff b f).mpr (h f)
  · intro h f
    exact (mem_dualSpan_iff b f).mp (h ▸ Submodule.mem_top)

/-- Every initial projection annihilates the corresponding closed tail. -/
theorem projection_tail_eq_zero (b : SchauderBasis 𝕜 E) (N : ℕ)
    {x : E} (hx : x ∈ tailSpace b N) : b.proj N x = 0 := by
  have hle : tailSpace b N ≤ (b.proj N).ker := by
    apply Submodule.topologicalClosure_minimal _ _ (b.proj N).isClosed_ker
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change b.proj N (b j) = 0
    rw [SchauderBasis.proj_apply_basis_mem]
    exact ite_eq_right (Nat.not_lt.mpr hj)
  exact hle hx

/-- The residual of an initial projection belongs to the actual closed tail. -/
theorem residual_mem_tail (b : SchauderBasis 𝕜 E) (N : ℕ) (x : E) :
    x - b.proj N x ∈ tailSpace b N := by
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (b.tendsto_proj (x - b.proj N x))
  apply Eventually.of_forall
  intro M
  rw [SchauderBasis.proj_apply]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i < N
  · have hc : b.coord i (x - b.proj N x) = 0 := by
      have h := congrArg (fun g : E →L[𝕜] 𝕜 => g x) (coord_projection b N i)
      simp only [ContinuousLinearMap.comp_apply, ite_eq_left hi] at h
      rw [map_sub, h, sub_self]
    simp only [hc, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨i, Nat.le_of_not_gt hi, rfl⟩))

/-- Tail restriction is bounded by the dual coordinate remainder. -/
theorem tail_norm_le_remainder (b : SchauderBasis 𝕜 E) (N : ℕ)
    (f : E →L[𝕜] 𝕜) :
    ‖f.comp (tailSpace b N).subtypeL‖ ≤ ‖f - dualProjection b N f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have he : f x = (f - dualProjection b N f) x := by
    simp [projection_tail_eq_zero b N x.property]
  change ‖f x‖ ≤ ‖f - dualProjection b N f‖ * ‖x‖
  rw [he]
  exact (f - dualProjection b N f).le_opNorm x

/-- The converse bound uses only the uniform bound on the primal projections. -/
theorem remainder_norm_le_tail (b : SchauderBasis 𝕜 E) {C : ℝ}
    (hC : ∀ N, ‖b.proj N‖ ≤ C) (N : ℕ) (f : E →L[𝕜] 𝕜) :
    ‖f - dualProjection b N f‖ ≤ ‖f.comp (tailSpace b N).subtypeL‖ * (1 + C) := by
  have hC0 : 0 ≤ C := (norm_nonneg (b.proj 0)).trans (hC 0)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  let y : tailSpace b N := ⟨x - b.proj N x, residual_mem_tail b N x⟩
  have he : (f - dualProjection b N f) x = f y := by simp [y]
  have hy : ‖y‖ ≤ (1 + C) * ‖x‖ := by
    change ‖x - b.proj N x‖ ≤ (1 + C) * ‖x‖
    calc
      _ ≤ ‖x‖ + ‖b.proj N x‖ := norm_sub_le _ _
      _ ≤ ‖x‖ + C * ‖x‖ := by
        gcongr
        exact ((b.proj N).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hC N) (norm_nonneg x))
      _ = (1 + C) * ‖x‖ := by ring
  rw [he]
  exact ((f.comp (tailSpace b N).subtypeL).le_opNorm y).trans
    ((mul_le_mul_of_nonneg_left hy (norm_nonneg _)).trans_eq (by ring))

theorem shrinking_characterization : Spec.ShrinkingCharacterization := by
  intro 𝕜 E _ _ _ _ b
  refine ⟨shrinking_iff_dualSpan b, ?_⟩
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  constructor
  · intro h f
    have hf : Tendsto (fun N => ‖f - dualProjection b N f‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero, dualProjection_apply] using
        ((tendsto_const_nhds (x := f)).sub (h f)).norm
    exact squeeze_zero (fun _ => norm_nonneg _) (tail_norm_le_remainder b · f) hf
  · intro h f
    have hf : Tendsto (fun N => ‖f - dualProjection b N f‖) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => norm_nonneg _) (remainder_norm_le_tail b hC · f)
      simpa using (h f).mul_const (1 + C)
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [norm_sub_rev, dualProjection_apply] using hf

/-- The full finite-list boundary case; no positive dimension is assumed. -/
theorem finite_dual_facts : Spec.FiniteDualFacts := by
  intro 𝕜 E _ _ _ d b
  classical
  let F := (Submodule.span 𝕜 (Set.range b.coord)).topologicalClosure
  let e' : Fin d → F := fun i => ⟨b.coord i, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self i))⟩
  have hexp (x : E) : ∑ i, b.coord i x • b i = x :=
    (hasSum_fintype _).unique (b.expansion x)
  have hdual (f : E →L[𝕜] 𝕜) : ∑ i, f (b i) • b.coord i = f := by
    ext x
    have hh := congrArg f (hexp x)
    simpa [map_sum, map_smul, mul_comm] using hh
  have hs (N : ℕ) (hN : d ≤ N) :
      Finset.univ.filter (fun i : Fin d => i.val < N) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    exact i.isLt.trans_le hN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro i hz
      have hh := congrArg (fun f : F => f.val (b i)) hz
      simp [b.ortho] at hh
    · intro f
      refine ⟨fun i => f.val (b i), ?_, ?_⟩
      · apply Subtype.ext
        simpa only [ExpandedFA.P1.C15Basis.Spec.finiteSynthesis,
          Submodule.coe_sum, Submodule.coe_smul] using hdual f.val
      · intro a ha
        funext i
        have hh := congrArg (fun f : F => f.val (b i)) ha
        simpa [ExpandedFA.P1.C15Basis.Spec.finiteSynthesis, e', b.ortho,
          Pi.single_apply] using hh
  · apply eq_top_iff.mpr
    intro f _
    rw [← hdual f]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (e' i).property)
  · intro f N hN
    rw [hs N hN]
    exact hdual f
  · intro f
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop d] with N hN
    have hempty : b '' {i : Fin d | N ≤ i.val} = ∅ := by
      apply Set.image_eq_empty.mpr
      exact Set.eq_empty_iff_forall_notMem.mpr fun i hi =>
        (Nat.not_le_of_gt (i.isLt.trans_le hN)) hi
    have hbot : (Submodule.span 𝕜 (b '' {i : Fin d | N ≤ i.val})).topologicalClosure = ⊥ := by
      rw [hempty, Submodule.span_empty]
      exact (isClosed_singleton : IsClosed ({0} : Set E)).submodule_topologicalClosure_eq
    have hz : f.comp
        ((Submodule.span 𝕜 (b '' {i : Fin d | N ≤ i.val})).topologicalClosure).subtypeL = 0 := by
      ext x
      have hx : x.val = 0 := by simpa only [hbot, Submodule.mem_bot] using x.property
      simp [hx]
    simp only [hz, norm_zero]
  · intro a
    refine ⟨∑ i, a i • b i, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop d] with N hN
    rw [hs N hN]

end ExpandedFA.P1.DualBasisBasicity
