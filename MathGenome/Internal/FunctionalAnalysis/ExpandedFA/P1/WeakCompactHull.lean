import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WeakCompactHull
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.EberleinSmulian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12ConvexClosure
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.Prokhorov

namespace ExpandedFA.P1.WeakCompactHull
universe u v
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology Pointwise BoundedContinuousFunction
noncomputable section

/-- The explicit hull agrees with the manuscript's convex balanced hull,
including its zero point in the empty case. -/
theorem absolutely_convex_hull_characterization :
    Spec.AbsolutelyConvexHullCharacterization.{u,v} := by
  intro 𝕜 E _ _ _ K
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  let D : Set E := insert 0 (Metric.closedBall (0 : 𝕜) 1 • K)
  change (0 ∈ convexHull ℝ D) ∧ (K ⊆ convexHull ℝ D) ∧
    Convex ℝ (convexHull ℝ D) ∧ Balanced 𝕜 (convexHull ℝ D) ∧ _
  have hD : Balanced 𝕜 D := by
    rw [balanced_iff_smul_mem]
    intro a ha z hz
    rcases hz with rfl | ⟨c, hc, x, hx, rfl⟩
    · exact Or.inl (smul_zero a)
    · apply Or.inr
      refine ⟨a * c, ?_, x, hx, mul_smul a c x⟩
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
      exact (mul_le_mul_of_nonneg_right ha (norm_nonneg c)).trans
        (by simpa only [one_mul, Metric.mem_closedBall, dist_zero_right] using hc)
  refine ⟨subset_convexHull ℝ D (mem_insert 0 _), ?_, convex_convexHull ℝ D, ?_, ?_⟩
  · intro x hx
    apply subset_convexHull ℝ D
    exact Or.inr ⟨1, by simp, x, hx, one_smul 𝕜 x⟩
  · rw [balanced_iff_smul_mem]
    intro a ha x hx
    have hc : Convex ℝ {z : E | a • z ∈ convexHull ℝ D} := by
      intro z hz w hw r t hr ht hrt
      change a • (r • z + t • w) ∈ convexHull ℝ D
      rw [smul_add, smul_comm a r z, smul_comm a t w]
      exact convex_convexHull ℝ D hz hw hr ht hrt
    apply convexHull_min (t := {z : E | a • z ∈ convexHull ℝ D}) ?_ hc hx
    intro z hz
    exact subset_convexHull ℝ D (hD.smul_mem ha hz)
  · intro A hA0 hAK hAc hAb
    apply convexHull_min _ hAc
    rintro z (rfl | ⟨a, ha, x, hx, rfl⟩)
    · exact hA0
    · exact hAb.smul_mem (by simpa only [Metric.mem_closedBall, dist_zero_right] using ha)
        (hAK hx)

/-- The closure assertion does not require completeness. -/
theorem hull_closure_equalities : Spec.HullClosureEqualities.{u,v} := by
  intro 𝕜 E _ _ _ K
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  exact ⟨C12ConvexClosure.weak_closure_eq_norm_closure 𝕜 E _ (convex_convexHull ℝ K),
    C12ConvexClosure.weak_closure_eq_norm_closure 𝕜 E _ (convex_convexHull ℝ _)⟩

/-- The canonical weak topology is the native weak-space topology transported
by the identity linear equivalence. -/
theorem weakTopology_eq (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Spec.weakTopology 𝕜 E =
      TopologicalSpace.induced (toWeakSpace 𝕜 E) inferInstance := rfl

/-- A real-convex norm-closed set has closed image in the native weak space. -/
theorem isClosed_weak_image {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (C : Set E) (hC : IsClosed C)
    (hc : letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E; Convex ℝ C) :
    IsClosed (toWeakSpace 𝕜 E '' C) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  letI : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
  rw [← closure_eq_iff_isClosed, ← hc.toWeakSpace_closure 𝕜, hC.closure_eq]

/-- In a norm-separable space the identity from the weak Borel structure to
its norm Borel structure is measurable. Closed balls are weakly closed. -/
theorem measurable_fromWeakSpace {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeparableSpace E] :
    @Measurable (WeakSpace 𝕜 E) E (borel (WeakSpace 𝕜 E)) (borel E)
      (toWeakSpace 𝕜 E).symm := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : MeasurableSpace (WeakSpace 𝕜 E) := borel (WeakSpace 𝕜 E)
  letI : BorelSpace (WeakSpace 𝕜 E) := ⟨rfl⟩
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  have hbasis : IsTopologicalBasis {s : Set E | ∃ x r, s = Metric.ball x r} := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨x, r, rfl⟩; exact Metric.isOpen_ball
    · intro x U hx hU
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
      exact ⟨Metric.ball x r, ⟨x, r, rfl⟩, Metric.mem_ball_self hr, hsub⟩
  rw [hbasis.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro _ ⟨x, r, rfl⟩
  have heq : (toWeakSpace 𝕜 E).symm ⁻¹' Metric.ball x r =
      ⋃ (q : ℚ) (_ : (q : ℝ) < r), toWeakSpace 𝕜 E '' Metric.closedBall x (q : ℝ) := by
    ext z
    simp only [mem_preimage, Metric.mem_ball, mem_iUnion, mem_image,
      Metric.mem_closedBall]
    constructor
    · intro hz
      obtain ⟨q, hq, hqr⟩ := exists_rat_btwn hz
      exact ⟨q, hqr, (toWeakSpace 𝕜 E).symm z, hq.le,
        (toWeakSpace 𝕜 E).apply_symm_apply z⟩
    · rintro ⟨q, hqr, y, hy, rfl⟩
      simpa using hy.trans_lt hqr
  rw [heq]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    (isClosed_weak_image (Metric.closedBall x (q : ℝ)) Metric.isClosed_closedBall
      (convex_closedBall x (q : ℝ))).measurableSet


/-- Compactness in the canonical topology can be tested on its native carrier. -/
theorem weak_isCompact_iff {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (K : Set E) :
    @IsCompact E (Spec.weakTopology 𝕜 E) K ↔
      IsCompact (toWeakSpace 𝕜 E '' K) := by
  change @IsCompact (WeakSpace 𝕜 E) (TopologicalSpace.induced id inferInstance) K ↔ _
  rw [induced_id]
  have heq : toWeakSpace 𝕜 E '' K = (K : Set (WeakSpace 𝕜 E)) := image_id K
  rw [heq]



/-- Weakly compact sets have a uniform bound in the original norm. -/
theorem weak_compact_norm_bound {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (K : Set E)
    (hK : @IsCompact E (Spec.weakTopology 𝕜 E) K) :
    ∃ C : ℝ, ∀ x ∈ K, ‖x‖ ≤ C := by
  apply isBounded_iff_forall_norm_le.mp
  apply (C07WeakBoundedness.weak_boundedness 𝕜 E K).mpr
  intro f
  have h := (weak_isCompact_iff K).mp hK
  have hh := h.image (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip f)
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hh.isBounded
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hC _ ⟨toWeakSpace 𝕜 E x, ⟨x, hx, rfl⟩, rfl⟩

/-- Separable Banach-space version: use the continuous weak barycenter map
on the compact space of probability measures on K. -/
theorem separable_convex_hull_compact {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [SeparableSpace E] (K : Set E)
    (hK : @IsCompact E (Spec.weakTopology 𝕜 E) K) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    @IsCompact E (Spec.weakTopology 𝕜 E) (closure (convexHull ℝ K)) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let L : Set (WeakSpace 𝕜 E) := toWeakSpace 𝕜 E '' K
  letI : CompactSpace L := isCompact_iff_compactSpace.mp ((weak_isCompact_iff K).mp hK)
  letI : MeasurableSpace L := borel L
  letI : BorelSpace L := ⟨rfl⟩
  letI : MeasurableSpace (WeakSpace 𝕜 E) := borel (WeakSpace 𝕜 E)
  letI : BorelSpace (WeakSpace 𝕜 E) := ⟨rfl⟩
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let j : L → E := fun z => (toWeakSpace 𝕜 E).symm z.val
  have hj : Measurable j := measurable_fromWeakSpace.comp continuous_subtype_val.measurable
  obtain ⟨C, hC⟩ := weak_compact_norm_bound K hK
  have hjK (z : L) : j z ∈ K := by
    obtain ⟨x, hx, hzx⟩ := z.property
    simpa [j, ← hzx] using hx
  have hint (μ : ProbabilityMeasure L) : Integrable j (μ : Measure L) :=
    Integrable.of_bound hj.aestronglyMeasurable C (ae_of_all _ fun z => hC _ (hjK z))
  let b : ProbabilityMeasure L → E := fun μ => ∫ z, j z ∂(μ : Measure L)
  have hb : Continuous (fun μ => toWeakSpace 𝕜 E (b μ)) := by
    apply WeakBilin.continuous_of_continuous_eval
    intro f
    let g : L →ᵇ 𝕜 := BoundedContinuousFunction.mkOfCompact
      ⟨fun z => f (j z),
        (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip f).comp continuous_subtype_val⟩
    have hg : Continuous (fun μ : ProbabilityMeasure L => ∫ z, g z ∂(μ : Measure L)) := by
      rw [continuous_iff_continuousAt]
      intro μ
      exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜).mp
        continuous_id.continuousAt g
    convert hg using 1
    ext μ
    exact (f.integral_comp_comm (hint μ)).symm
  have hcompact : IsCompact (toWeakSpace 𝕜 E '' range b) := by
    simpa only [image_univ, ← range_comp, Function.comp_def] using isCompact_univ.image hb
  have hclosed : IsClosed (range b) := by
    convert hcompact.isClosed.preimage (toWeakSpaceCLM 𝕜 E).continuous using 1
    exact ((toWeakSpace 𝕜 E).injective.preimage_image (range b)).symm
  have hconvex : Convex ℝ (range b) := by
    rintro _ ⟨μ, rfl⟩ _ ⟨ν, rfl⟩ a c ha hc hac
    let m : Measure L := ENNReal.ofReal a • (μ : Measure L) +
      ENNReal.ofReal c • (ν : Measure L)
    have hm : IsProbabilityMeasure m := by
      constructor
      simp only [m, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
        mul_one, ← ENNReal.ofReal_add ha hc, hac, ENNReal.ofReal_one]
    let ρ : ProbabilityMeasure L := ⟨m, hm⟩
    refine ⟨ρ, ?_⟩
    change (∫ z, j z ∂m) = _
    rw [show m = _ from rfl, integral_add_measure
      ((hint μ).smul_measure ENNReal.ofReal_ne_top)
      ((hint ν).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
      integral_smul_measure, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hc]
  have hcontains : K ⊆ range b := by
    intro x hx
    let z : L := ⟨toWeakSpace 𝕜 E x, ⟨x, hx, rfl⟩⟩
    refine ⟨⟨Measure.dirac z, inferInstance⟩, ?_⟩
    change (∫ t, j t ∂Measure.dirac z) = x
    simp [j, z]
  have heq : range b = closure (convexHull ℝ K) := by
    apply Subset.antisymm
    · rintro _ ⟨μ, rfl⟩
      exact (convex_convexHull ℝ K).closure.integral_mem isClosed_closure
        (ae_of_all _ fun z => subset_closure (subset_convexHull ℝ K (hjK z))) (hint μ)
    · exact closure_minimal (convexHull_min hcontains hconvex) hclosed
  exact (weak_isCompact_iff _).mpr (heq ▸ hcompact)


/-- Only countably many generating points are needed for any sequence in the
norm-closed convex hull. Both approximation indices are retained. -/
theorem countable_generators_for_sequence {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : Set E) (x : ℕ → E)
    (hx : letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E;
      ∀ n, x n ∈ closure (convexHull ℝ K)) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∃ S : Set E, S.Countable ∧ S ⊆ K ∧ ∀ n, x n ∈ closure (convexHull ℝ S) := by
  classical
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  choose y hy hlim using fun n => mem_closure_iff_seq_limit.mp (hx n)
  have hfinite : ∀ n m, ∃ t : Finset E, (t : Set E) ⊆ K ∧
      y n m ∈ convexHull ℝ (t : Set E) := by
    intro n m
    have h := hy n m
    rw [convexHull_eq_union_convexHull_finite_subsets] at h
    simpa only [mem_iUnion, exists_prop] using h
  choose t htK hty using hfinite
  let S : Set E := ⋃ n, ⋃ m, (t n m : Set E)
  refine ⟨S, ?_, ?_, ?_⟩
  · exact countable_iUnion fun n => countable_iUnion fun m => (t n m).countable_toSet
  · exact iUnion_subset fun n => iUnion_subset fun m => htK n m
  · intro n
    apply isClosed_closure.mem_of_tendsto (hlim n)
    apply Eventually.of_forall
    intro m
    apply subset_closure
    exact convexHull_mono (fun z hz => mem_iUnion.mpr ⟨n,
      mem_iUnion.mpr ⟨m, hz⟩⟩) (hty n m)


/-- Krein's theorem without a separability assumption. A given sequence in
its hull is supported by a separable closed subspace, where the probability
measure argument applies. Eberlein–Šmulian finishes the proof. -/
theorem convex_hull_compact : Spec.ConvexHullCompact.{u,v} := by
  intro 𝕜 E _ _ _ _ K hK
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  let C : Set E := closure (convexHull ℝ K)
  have hCclosed := C12ConvexClosure.isWeaklyClosed_of_isClosed_convex 𝕜 E C
    (convex_convexHull ℝ K).closure isClosed_closure
  have hCeq := @IsClosed.closure_eq E (Spec.weakTopology 𝕜 E) C hCclosed
  change @IsCompact E (Spec.weakTopology 𝕜 E) C
  rw [← hCeq]
  apply (EberleinSmulian.relative_equivalences 𝕜 E C).1.mpr
  intro x hx
  obtain ⟨S, hScount, hSK, hSx⟩ := countable_generators_for_sequence K x hx
  let Y : Submodule 𝕜 E := (Submodule.span 𝕜 S).topologicalClosure
  have hYS : S ⊆ (Y : Set E) := fun _ hz =>
    (Submodule.span 𝕜 S).le_topologicalClosure (Submodule.subset_span hz)
  have hYclosed : IsClosed (Y : Set E) := Submodule.isClosed_topologicalClosure _
  have hYsep : IsSeparable (Y : Set E) := by
    rw [show (Y : Set E) = closure (Submodule.span 𝕜 S : Set E) from
      Submodule.topologicalClosure_coe _]
    exact hScount.isSeparable.span.closure
  letI : SeparableSpace Y := hYsep.separableSpace
  letI : CompleteSpace Y := hYclosed.completeSpace_coe
  let L : Set Y := Subtype.val ⁻¹' K
  have hL : @IsCompact Y (Spec.weakTopology 𝕜 Y) L := by
    have hYweak := C12ConvexClosure.isWeaklyClosed_of_isClosed_submodule 𝕜 E Y hYclosed
    have htop := C12ConvexClosure.subspace_induced_weak_topology 𝕜 E Y
    letI : TopologicalSpace E := Spec.weakTopology 𝕜 E
    letI : TopologicalSpace Y := TopologicalSpace.induced (fun y : Y => (y : E))
      (Spec.weakTopology 𝕜 E)
    have hi : Topology.IsInducing (fun y : Y => (y : E)) := ⟨rfl⟩
    have hR : IsClosed (range (fun y : Y => (y : E))) := by simpa using hYweak
    have h : IsCompact L := hi.isCompact_preimage hR hK
    exact Eq.mp (congrArg (fun top => @IsCompact Y top L) htop) h

  let D : Set Y := closure (convexHull ℝ L)
  have hDcompact := separable_convex_hull_compact L hL
  have hDweak := C12ConvexClosure.isWeaklyClosed_of_isClosed_convex 𝕜 Y D
    (convex_convexHull ℝ L).closure isClosed_closure
  have hDimageclosed : IsClosed ((fun y : Y => (y : E)) '' D) :=
    hYclosed.isClosedEmbedding_subtypeVal.isClosedMap D isClosed_closure
  have hDimageconvex : Convex ℝ ((fun y : Y => (y : E)) '' D) :=
    (convex_convexHull ℝ L).closure.linear_image (Y.subtype.restrictScalars ℝ)
  have hSD : S ⊆ (fun y : Y => (y : E)) '' D := by
    intro z hz
    exact ⟨⟨z, hYS hz⟩, subset_closure (subset_convexHull ℝ L (hSK hz)), rfl⟩
  have hxD (n : ℕ) : x n ∈ (fun y : Y => (y : E)) '' D :=
    closure_minimal (convexHull_min hSD hDimageconvex) hDimageclosed (hSx n)
  choose t htD htx using hxD
  have hDeq := @IsClosed.closure_eq Y (Spec.weakTopology 𝕜 Y) D hDweak
  have hseq := EberleinSmulian.compact_implies_subsequences 𝕜 Y D
    (by rw [hDeq]; exact hDcompact)
  obtain ⟨y, r, hr, hlim⟩ := hseq t htD
  have hcont : @Continuous Y E (Spec.weakTopology 𝕜 Y)
      (Spec.weakTopology 𝕜 E) (fun y : Y => (y : E)) := by
    apply continuous_iff_le_induced.mpr
    exact le_of_eq (C12ConvexClosure.subspace_induced_weak_topology 𝕜 E Y).symm
  letI : TopologicalSpace E := Spec.weakTopology 𝕜 E
  letI : TopologicalSpace Y := Spec.weakTopology 𝕜 Y
  refine ⟨(y : E), r, hr, ?_⟩
  convert (hcont.tendsto y).comp hlim using 1
  all_goals exact funext fun n => (htx (r n)).symm


/-- Saturating by the scalar closed unit disk preserves weak compactness. -/
theorem weak_compact_disk_saturation {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (K : Set E)
    (hK : @IsCompact E (Spec.weakTopology 𝕜 E) K) :
    @IsCompact E (Spec.weakTopology 𝕜 E)
      (insert 0 (Metric.closedBall (0 : 𝕜) 1 • K)) := by
  have heq : toWeakSpace 𝕜 E '' (insert 0 (Metric.closedBall (0 : 𝕜) 1 • K)) =
      insert 0 (Metric.closedBall (0 : 𝕜) 1 • (toWeakSpace 𝕜 E '' K)) := by
    rw [image_insert_eq, map_zero]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨a, ha, x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, toWeakSpace 𝕜 E x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a • x, ⟨a, ha, x, hx, rfl⟩, rfl⟩
  apply (weak_isCompact_iff _).mpr
  rw [heq]
  exact ((isCompact_closedBall (0 : 𝕜) 1).smul_set ((weak_isCompact_iff K).mp hK)).insert 0

/-- The absolutely convex conclusion uses the disk saturation, including its
zero point when K is empty. -/
theorem absolutely_convex_hull_compact : Spec.AbsolutelyConvexHullCompact.{u,v} := by
  intro 𝕜 E _ _ _ _ K hK
  exact convex_hull_compact 𝕜 E _ (weak_compact_disk_saturation K hK)

end
end ExpandedFA.P1.WeakCompactHull
