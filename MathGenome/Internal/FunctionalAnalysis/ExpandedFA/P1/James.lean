import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.James
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesBalancedAttainment
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07WeakBoundedness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14BallCharacterization
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Topology.Order.Compact

universe u v
namespace ExpandedFA.P1.James
open Set TopologicalSpace
open scoped Topology
noncomputable section

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma weak_eval_continuous (f : E →L[𝕜] 𝕜) :
    @Continuous E 𝕜 (Spec.weakTopology 𝕜 E) inferInstance f :=
  (dualPairTopology_coarsest 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
    (Spec.weakTopology 𝕜 E)).mpr le_rfl f

lemma weak_continuous_of_tests {X : Type*} [TopologicalSpace X] (g : X → E)
    (hg : ∀ f : E →L[𝕜] 𝕜, Continuous (fun x => f (g x))) :
    @Continuous X E inferInstance (Spec.weakTopology 𝕜 E) g := by
  change @Continuous X E _
    (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) g
  rw [dualPairTopology_evaluation 𝕜 E, continuous_iInf_rng]
  intro f
  exact continuous_induced_rng.mpr (hg f)

lemma weak_smul_continuous (c : 𝕜) :
    @Continuous E E (Spec.weakTopology 𝕜 E) (Spec.weakTopology 𝕜 E)
      (fun x => c • x) := by
  letI : TopologicalSpace E := Spec.weakTopology 𝕜 E
  apply weak_continuous_of_tests
  intro f
  simpa only [map_smul, smul_eq_mul] using (weak_eval_continuous f).const_mul c

/-- Complex and real weak topologies agree, with the canonical real action. -/
lemma weakTopology_real [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    Spec.weakTopology 𝕜 E = Spec.weakTopology ℝ E := by
  apply le_antisymm
  · apply (dualPairTopology_coarsest ℝ E (E →L[ℝ] ℝ) (topDualPairing ℝ E) _).mp
    intro f
    have hg := weak_eval_continuous (StrongDual.extendRCLike (𝕜 := 𝕜) f)
    letI : TopologicalSpace E := Spec.weakTopology 𝕜 E
    have hc := RCLike.continuous_re.comp hg
    simpa only [Function.comp_def, StrongDual.re_extendRCLike_apply, topDualPairing_apply] using hc
  · apply (dualPairTopology_coarsest 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E) _).mp
    intro f
    let re : E →L[ℝ] ℝ := RCLike.reCLM.comp (f.restrictScalars ℝ)
    let im : E →L[ℝ] ℝ := RCLike.imCLM.comp (f.restrictScalars ℝ)
    have hr := weak_eval_continuous re
    have hi := weak_eval_continuous im
    letI : TopologicalSpace E := Spec.weakTopology ℝ E
    have hr' : Continuous (fun x : E => (RCLike.re (f x) : 𝕜)) :=
      RCLike.continuous_ofReal.comp hr
    have hi' : Continuous (fun x : E => (RCLike.im (f x) : 𝕜)) :=
      RCLike.continuous_ofReal.comp hi
    have hc := hr'.add (hi'.mul_const (RCLike.I : 𝕜))
    convert hc using 1
    funext x
    exact (RCLike.re_add_im (f x)).symm

/-- Compactness gives a maximum, hence a finite attained supremum. -/
lemma compact_absolute_attainment {A : Set E} (hne : A.Nonempty)
    (hc : @IsCompact E (Spec.weakTopology 𝕜 E) A) :
    Spec.AbsoluteAttainment 𝕜 E A := by
  intro f
  letI : TopologicalSpace E := Spec.weakTopology 𝕜 E
  exact hc.exists_isMaxOn hne (weak_eval_continuous f).norm.continuousOn

lemma absolute_attainment_bounded {A : Set E} (h : Spec.AbsoluteAttainment 𝕜 E A) :
    Bornology.IsBounded A := by
  apply (C07WeakBoundedness.weak_boundedness 𝕜 E A).mpr
  intro f
  obtain ⟨a, ha, hmax⟩ := h f
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨‖f a‖, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact hmax x hx


/-- Normalize the absolute polar of A. The scalar maxima on A also give all
real maxima on this balanced enlargement, by a scalar rotation. -/
lemma compact_of_absolute_attainment [CompleteSpace E] {A : Set E}
    (hclosed : @IsClosed E (Spec.weakTopology 𝕜 E) A)
    (hatt : Spec.AbsoluteAttainment 𝕜 E A) :
    @IsCompact E (Spec.weakTopology 𝕜 E) A := by
  classical
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨r, hr, hAr⟩ := (absolute_attainment_bounded hatt).exists_pos_norm_le
  choose a ha hmax using hatt
  let M : (E →L[𝕜] 𝕜) → ℝ := fun f => ‖f (a f)‖
  have hM (f : E →L[𝕜] 𝕜) : 0 ≤ M f := norm_nonneg _
  have hMr (f : E →L[𝕜] 𝕜) : M f ≤ ‖f‖ * r :=
    (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hAr _ (ha f)) (norm_nonneg _))
  let C : Set E := {x | ∀ f : E →L[𝕜] 𝕜, ‖f x‖ ≤ M f / r}
  have hCzero : (0 : E) ∈ C := by
    intro f
    simpa only [map_zero, norm_zero] using div_nonneg (hM f) hr.le
  have hCbal : Balanced 𝕜 C := by
    apply balanced_iff_smul_mem.mpr
    intro c hc x hx f
    calc
      ‖f (c • x)‖ = ‖c‖ * ‖f x‖ := by rw [map_smul, norm_smul]
      _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ M f / r := by simpa only [one_mul] using hx f
  have hCrealbal : Balanced ℝ C := by
    apply balanced_iff_smul_mem.mpr
    intro c hc x hx
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    apply hCbal.smul_mem _ hx
    simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using hc
  have hCunit : C ⊆ Metric.closedBall (0 : E) 1 := by
    intro x hx
    obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional 𝕜 E x
    have hle := hx f
    have hdiv : M f / r ≤ ‖f‖ := (div_le_iff₀ hr).mpr (hMr f)
    have hnx : ‖f x‖ = ‖x‖ := by rw [hfx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (hnx ▸ hle).trans (hdiv.trans hf)
  have hCclosed : @IsClosed E (Spec.weakTopology 𝕜 E) C := by
    have heq : C = ⋂ f : E →L[𝕜] 𝕜, {x | ‖f x‖ ≤ M f / r} := by
      ext x
      simp only [C, mem_ofPred_eq, mem_iInter]
    letI : TopologicalSpace E := Spec.weakTopology 𝕜 E
    rw [heq]
    exact isClosed_iInter fun f =>
      isClosed_le (weak_eval_continuous f).norm continuous_const
  have hscaled (x : E) (hx : x ∈ A) : (r⁻¹ : 𝕜) • x ∈ C := by
    intro f
    rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hr]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left (hmax f x hx) (inv_nonneg.mpr hr.le)
  have hCatt : ∀ u : E →L[ℝ] ℝ,
      BddAbove ((fun x => |u x|) '' C) ∧
      ∃ x ∈ C, |u x| = sSup ((fun y => |u y|) '' C) := by
    intro u
    let f : E →L[𝕜] 𝕜 := StrongDual.extendRCLike u
    let b : E := (r⁻¹ : 𝕜) • a f
    have hb : b ∈ C := hscaled _ (ha f)
    have hfb : ‖f b‖ = M f / r := by
      simp only [b, map_smul, norm_smul, norm_inv, RCLike.norm_ofReal,
        abs_of_pos hr, M, div_eq_mul_inv, mul_comm]
    obtain ⟨c, hc, hcf⟩ := RCLike.exists_norm_eq_mul_self (f b)
    have hcy : c • b ∈ C := hCbal.smul_mem hc.le hb
    have huy : |u (c • b)| = M f / r := by
      have heq : u (c • b) = ‖f b‖ := by
        have he := congrArg RCLike.re hcf
        simpa only [RCLike.ofReal_re, ← smul_eq_mul, ← map_smul,
          f, StrongDual.re_extendRCLike_apply] using he.symm
      rw [heq, abs_of_nonneg (norm_nonneg _), hfb]
    have hub (x : E) (hx : x ∈ C) : |u x| ≤ M f / r := by
      calc
        |u x| = |RCLike.re (f x)| := by simp [f]
        _ ≤ ‖f x‖ := RCLike.abs_re_le_norm _
        _ ≤ M f / r := hx f
    have hgreat : IsGreatest ((fun x => |u x|) '' C) (M f / r) := by
      refine ⟨⟨c • b, hcy, huy⟩, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      exact hub x hx
    exact ⟨hgreat.bddAbove, c • b, hcy, huy.trans hgreat.csSup_eq.symm⟩
  have hCclosedR : @IsClosed E (Spec.weakTopology ℝ E) C :=
    weakTopology_real (𝕜 := 𝕜) (E := E) ▸ hCclosed
  have hcompactR : @IsCompact E (Spec.weakTopology ℝ E) C :=
    JamesBalancedAttainment.balanced_attainment_compact E C
      ⟨0, hCzero⟩ hCrealbal hCunit hCclosedR hCatt
  have hcompact : @IsCompact E (Spec.weakTopology 𝕜 E) C :=
    (weakTopology_real (𝕜 := 𝕜) (E := E)).symm ▸ hcompactR
  have hsub : A ⊆ (fun x : E => (r : 𝕜) • x) '' C := by
    intro x hx
    refine ⟨(r⁻¹ : 𝕜) • x, hscaled x hx, ?_⟩
    change (r : 𝕜) • ((r : 𝕜)⁻¹ • x) = x
    exact smul_inv_smul₀ (RCLike.ofReal_ne_zero.mpr hr.ne') x
  letI : TopologicalSpace E := Spec.weakTopology 𝕜 E
  exact (hcompact.image (weak_smul_continuous (r : 𝕜))).of_isClosed_subset hclosed hsub


/-- Maxima for u and -u give a maximum for |u|, without any symmetry of A. -/
lemma real_supremum_absolute_attainment [NormedSpace ℝ E] {A : Set E}
    (h : Spec.RealSupremumAttainment E A) : Spec.AbsoluteAttainment ℝ E A := by
  intro f
  obtain ⟨a, ha, hmax⟩ := h f
  obtain ⟨b, hb, hnegmax⟩ := h (-f)
  have hmin (x : E) (hx : x ∈ A) : f b ≤ f x := by
    have hh := hnegmax x hx
    simpa only [neg_apply, neg_le_neg_iff] using hh
  simp only [Real.norm_eq_abs]
  by_cases hab : |f a| ≤ |f b|
  · refine ⟨b, hb, fun x hx => abs_le.mpr ⟨?_, ?_⟩⟩
    · exact (neg_abs_le (f b)).trans (hmin x hx)
    · exact (hmax x hx).trans ((le_abs_self _).trans hab)
  · refine ⟨a, ha, fun x hx => abs_le.mpr ⟨?_, ?_⟩⟩
    · exact (neg_le_neg (le_of_not_ge hab)).trans ((neg_abs_le (f b)).trans (hmin x hx))
    · exact (hmax x hx).trans (le_abs_self _)

/-- James's four equivalent conditions for arbitrary nonempty weakly closed sets. -/
theorem attainment_equivalences : Spec.AttainmentEquivalences.{u, v} := by
  intro 𝕜 E _ _ _ _ A hne hclosed
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have ht : Spec.weakTopology 𝕜 E = Spec.weakTopology ℝ E := weakTopology_real
  have hclosedR : @IsClosed E (Spec.weakTopology ℝ E) A := ht ▸ hclosed
  refine ⟨⟨compact_absolute_attainment hne, compact_of_absolute_attainment hclosed⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hc
    exact compact_absolute_attainment hne (ht ▸ hc)
  · intro ha
    exact ht.symm ▸ compact_of_absolute_attainment hclosedR ha
  · intro hc f
    have hcR : @IsCompact E (Spec.weakTopology ℝ E) A := ht ▸ hc
    letI : TopologicalSpace E := Spec.weakTopology ℝ E
    exact hcR.exists_isMaxOn hne (weak_eval_continuous f).continuousOn
  · intro ha
    exact ht.symm ▸ compact_of_absolute_attainment hclosedR
      (real_supremum_absolute_attainment ha)

/-- On the closed unit ball, an absolute maximum has value the operator norm. -/
lemma unitBall_absolute_attainment_iff :
    Spec.AbsoluteAttainment 𝕜 E {x : E | ‖x‖ ≤ 1} ↔
      ∀ f : E →L[𝕜] 𝕜, ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖ := by
  constructor
  · intro h f
    obtain ⟨x, hx, hmax⟩ := h f
    refine ⟨x, hx, le_antisymm (f.unit_le_opNorm x hx) ?_⟩
    exact ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun y hy =>
      hmax y hy.le
  · intro h f
    obtain ⟨x, hx, hfx⟩ := h f
    refine ⟨x, hx, fun y hy => ?_⟩
    rw [hfx]
    exact f.unit_le_opNorm y hy

/-- Reflexivity is equivalent to norm attainment by every scalar-linear functional. -/
theorem reflexive_iff_norm_attainment : Spec.ReflexiveIffNormAttainment.{u, v} := by
  intro 𝕜 E _ _ _ _
  have hne : ({x : E | ‖x‖ ≤ 1} : Set E).Nonempty := ⟨0, by simp⟩
  have hclosed : @IsClosed E (Spec.weakTopology 𝕜 E) {x : E | ‖x‖ ≤ 1} := by
    simpa only [sub_zero] using C12NormLsc.weak_closed_balls 𝕜 E 0 1
  exact (C14BallCharacterization.reflexive_iff_weakCompact_unitBall 𝕜 E).trans
    (((attainment_equivalences 𝕜 E _ hne hclosed).1).trans unitBall_absolute_attainment_iff)

end
end ExpandedFA.P1.James
