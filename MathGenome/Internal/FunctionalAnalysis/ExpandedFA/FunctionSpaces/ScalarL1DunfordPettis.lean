import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarL1DunfordPettis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.WeakL1UniformIntegrability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.EberleinSmulian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.RadonNikodym

open MeasureTheory Filter Set
open scoped ENNReal Topology Function
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
attribute [local instance] Classical.propDecidable
namespace ExpandedFA.FunctionSpaces
open WeakL1UniformIntegrabilitySpec ScalarL1DunfordPettisSpec

/-- Both integral controls give uniform continuity on decreasing measurable
sets whose intersection is null, including on infinite-measure spaces. -/
theorem l1_controls_uniform_decreasing_sets {X : Type u} {ι : Type v} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} {f : ι → X → 𝕜}
    (hi : ∀ i, Integrable (f i) μ) (hc : Controls μ f)
    (B : ℕ → Set X) (hB : ∀ n, MeasurableSet (B n))
    (hanti : Antitone B) (hnull : μ (⋂ n, B n) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ i, (∫ x in B N, ‖f i x‖ ∂μ) < ε := by
  obtain ⟨F, hF, hμF, ht⟩ := hc.2 (ε / 2) (by positivity)
  obtain ⟨δ, hδ, hs⟩ := hc.1 (ε / 2) (by positivity)
  have hlim : Tendsto (fun n => μ (B n ∩ F)) atTop (𝓝 0) := by
    have hm := tendsto_measure_iInter_atTop
      (fun n => ((hB n).inter hF).nullMeasurableSet)
      (fun n m hnm => inter_subset_inter_left F (hanti hnm))
      (show ∃ n, μ (B n ∩ F) ≠ ∞ from
        ⟨0, ne_of_lt ((measure_mono inter_subset_right).trans_lt hμF)⟩)
    have hn : μ (⋂ n, B n ∩ F) = 0 := by
      apply measure_mono_null _ hnull
      exact iInter_mono fun n => inter_subset_left
    simpa only [Function.comp_def, hn] using hm
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds
    (show (0 : ℝ≥0∞) < ENNReal.ofReal δ by positivity))).exists
  refine ⟨N, fun i => ?_⟩
  have hsplit : B N = (B N ∩ F) ∪ (B N \ F) := by ext x; simp
  have htail : (∫ x in B N \ F, ‖f i x‖ ∂μ) ≤ ∫ x in Fᶜ, ‖f i x‖ ∂μ :=
    setIntegral_mono_set (hi i).norm.integrableOn
      (ae_of_all _ (fun _ => norm_nonneg _))
      (ae_of_all _ (fun _ hx => hx.2))
  rw [hsplit, setIntegral_union (disjoint_of_subset_left inter_subset_right
    disjoint_sdiff_self_right) ((hB N).diff hF)
      (hi i).norm.integrableOn (hi i).norm.integrableOn]
  have hsmall := hs (B N ∩ F) ((hB N).inter hF) hN i
  have ht' := ht i
  linarith

/-- Compactness supplies weakly convergent subsequences in the native weak space. -/
private theorem l1_compact_subsequence {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} {A : Set (Lp 𝕜 1 μ)}
    (hA : RelativelyWeaklyCompact μ A) (s : ℕ → Lp 𝕜 1 μ) (hs : ∀ n, s n ∈ A) :
    ∃ g r, StrictMono r ∧ WeaklyConverges μ (s ∘ r) g := by
  obtain ⟨g, r, hr, hg⟩ :=
    ExpandedFA.P1.EberleinSmulian.compact_implies_subsequences 𝕜 (Lp 𝕜 1 μ) A hA s hs
  exact ⟨g, r, hr, fun L => ExpandedFA.P1.C12BoundedSequences.weak_evaluation_tendsto
    𝕜 (Lp 𝕜 1 μ) (s ∘ r) g hg L⟩

/-- Weak compactness forces small-set control, without assuming finite total mass. -/
theorem weak_l1_compact_small_sets {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) [SigmaFinite μ]
    (A : Set (Lp 𝕜 1 μ)) (hA : RelativelyWeaklyCompact μ A) :
    SmallSetControl μ (fun f : A => (f.val : X → 𝕜)) := by
  classical
  by_contra hf
  change ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ E : Set X, MeasurableSet E → μ E < ENNReal.ofReal δ →
      ∀ f : A, (∫ x in E, ‖f.val x‖ ∂μ) < ε) at hf
  push Not at hf
  obtain ⟨ε, hε, hfail⟩ := hf
  have hchoose (n : ℕ) : ∃ E : Set X, MeasurableSet E ∧
      μ E < ENNReal.ofReal ((1/2 : ℝ)^n) ∧
      ∃ f : A, ε ≤ ∫ x in E, ‖f.val x‖ ∂μ :=
    hfail ((1/2 : ℝ)^n) (by positivity)
  choose E hEm hEμ f hbad using hchoose
  obtain ⟨g, r, hr, hg⟩ := l1_compact_subsequence hA (fun n => (f n).val)
    (fun n => (f n).property)
  obtain ⟨δ, hδ, hsmall⟩ := (weak_l1_convergent_controls μ _ g hg).1.1 ε hε
  have hlim : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨n, hn⟩ := ((hlim.comp hr.tendsto_atTop).eventually (gt_mem_nhds hδ)).exists
  have hm := (hEμ (r n)).trans (ENNReal.ofReal_lt_ofReal_iff hδ |>.mpr hn)
  exact (not_lt_of_ge (hbad (r n))) (hsmall (E (r n)) (hEm (r n)) hm n)

/-- Weak compactness also forces tightness outside a finite-measure set. -/
theorem weak_l1_compact_tails {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) [SigmaFinite μ]
    (A : Set (Lp 𝕜 1 μ)) (hA : RelativelyWeaklyCompact μ A) :
    TailControl μ (fun f : A => (f.val : X → 𝕜)) := by
  classical
  by_contra hf
  change ¬ (∀ ε : ℝ, 0 < ε → ∃ F : Set X, MeasurableSet F ∧ μ F < ∞ ∧
    ∀ f : A, (∫ x in Fᶜ, ‖f.val x‖ ∂μ) < ε) at hf
  push Not at hf
  obtain ⟨ε, hε, hfail⟩ := hf
  have hchoose (n : ℕ) : ∃ f : A,
      ε ≤ ∫ x in (spanningSets μ n)ᶜ, ‖f.val x‖ ∂μ :=
    hfail (spanningSets μ n) (measurableSet_spanningSets μ n)
      (measure_spanningSets_lt_top μ n)
  choose f hbad using hchoose
  obtain ⟨g, r, hr, hg⟩ := l1_compact_subsequence hA (fun n => (f n).val)
    (fun n => (f n).property)
  have hc := (weak_l1_convergent_controls μ _ g hg).1
  obtain ⟨N, hN⟩ := l1_controls_uniform_decreasing_sets
    (fun n => memLp_one_iff_integrable.mp (Lp.memLp ((f (r n)).val))) hc
    (fun k => (spanningSets μ k)ᶜ)
    (fun k => (measurableSet_spanningSets μ k).compl)
    (fun _ _ h => compl_subset_compl.mpr (monotone_spanningSets μ h))
    (by simp only [← compl_iUnion, iUnion_spanningSets, compl_univ, measure_empty]) hε
  have hmono : (∫ x in (spanningSets μ (r N))ᶜ, ‖(f (r N)).val x‖ ∂μ) ≤
      ∫ x in (spanningSets μ N)ᶜ, ‖(f (r N)).val x‖ ∂μ :=
    setIntegral_mono_set
      (memLp_one_iff_integrable.mp (Lp.memLp (f (r N)).val)).norm.integrableOn
      (ae_of_all _ (fun _ => norm_nonneg _))
      (ae_of_all _ (fun _ hx => compl_subset_compl.mpr
        (monotone_spanningSets μ (hr.id_le N)) hx))
  exact (not_lt_of_ge ((hbad (r N)).trans hmono)) (hN N)

/-- Necessity in the scalar Dunford–Pettis theorem, with both controls. -/
theorem scalar_l1_dunford_pettis_necessity : Necessity.{u} := by
  intro X 𝕜 _ _ μ _ A hA
  have hs := ExpandedFA.P1.EberleinSmulian.compact_implies_subsequences
    𝕜 (Lp 𝕜 1 μ) A hA
  obtain ⟨C, _, hC⟩ := ExpandedFA.P1.WeakSequentialRelativeCompact.sequential_norm_bounded
    𝕜 (Lp 𝕜 1 μ) A hs
  exact ⟨isBounded_iff_forall_norm_le.mpr ⟨C, hC⟩,
    weak_l1_compact_small_sets μ A hA, weak_l1_compact_tails μ A hA⟩

/-- The integral pairing is symmetric in its two scalar arguments. -/
theorem l1_integrationEmbedding_apply {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (f : Lp 𝕜 1 μ) (h : Lp 𝕜 ∞ μ) :
    integrationEmbedding μ f h = ScalarLpIntegralPairingSpec.IntegralPairingValue μ 1 ∞ h f := by
  rw [(lp_pairing_integral μ ∞ 1 f h).2, (lp_pairing_integral μ 1 ∞ h f).2]
  exact integral_congr_ae (ae_of_all _ (fun _ => mul_comm _ _))

/-- Endpoint duality makes the integration embedding induce precisely the
weak topology of L¹, including on nonseparable sigma-finite spaces. -/
theorem l1_integrationEmbedding_inducing {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) [SigmaFinite μ] :
    @Topology.IsInducing (Lp 𝕜 1 μ) ((Lp 𝕜 ∞ μ) →L[𝕜] 𝕜)
      (weakTopology μ)
      (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ))
      (integrationEmbedding (𝕜 := 𝕜) μ) := by
  refine @Topology.IsInducing.mk (Lp 𝕜 1 μ) ((Lp 𝕜 ∞ μ) →L[𝕜] 𝕜)
    (weakTopology μ)
    (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ))
    (integrationEmbedding μ) ?_
  refine (ExpandedFA.P1.dualPairTopology_evaluation 𝕜 (Lp 𝕜 1 μ)).trans ?_
  apply Eq.symm
  calc
    TopologicalSpace.induced (integrationEmbedding μ)
        (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ)) =
        TopologicalSpace.induced (integrationEmbedding μ)
          (⨅ h : Lp 𝕜 ∞ μ, TopologicalSpace.induced
            (fun L : Lp 𝕜 ∞ μ →L[𝕜] 𝕜 => L h) inferInstance) :=
      congrArg (TopologicalSpace.induced (integrationEmbedding μ))
        (ExpandedFA.P1.C12WeakStar.weakStarTopology_evaluations 𝕜 (Lp 𝕜 ∞ μ))
    _ = ⨅ h : Lp 𝕜 ∞ μ, TopologicalSpace.induced
        (fun f : Lp 𝕜 1 μ => ScalarLpIntegralPairingSpec.IntegralPairingValue μ 1 ∞ h f)
        inferInstance := by
      rw [induced_iInf]
      simp only [induced_compose, Function.comp_def, l1_integrationEmbedding_apply]
    _ = ⨅ L : Lp 𝕜 1 μ →L[𝕜] 𝕜, TopologicalSpace.induced
        (fun f : Lp 𝕜 1 μ => L f) inferInstance := by
      have hsurj : Function.Surjective
          (ScalarLpIntegralPairingSpec.IntegralPairingValue (𝕜 := 𝕜) μ 1 ∞) :=
        (lp_pairing_sigmaFinite_isometric_bijective (𝕜 := 𝕜) μ 1 ∞ (by simp)).2.2
      apply le_antisymm
      · refine le_iInf fun L => ?_
        obtain ⟨h, rfl⟩ := hsurj L
        exact iInf_le _ h
      · exact le_iInf fun h => iInf_le _
          (ScalarLpIntegralPairingSpec.IntegralPairingValue μ 1 ∞ h)

/-- Alaoglu gives compactness of the full weak-star closure in (L∞)′. -/
theorem l1_integrationEmbedding_closure_compact {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (A : Set (Lp 𝕜 1 μ)) (hA : Bornology.IsBounded A) :
    @IsCompact _
      (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ))
      (@closure _
        (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ))
        (integrationEmbedding μ '' A)) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hA
  letI : TopologicalSpace ((Lp 𝕜 ∞ μ) →L[𝕜] 𝕜) :=
    ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ)
  letI : T2Space ((Lp 𝕜 ∞ μ) →L[𝕜] 𝕜) :=
    (show Topology.IsEmbedding (StrongDual.toWeakDual (𝕜 := 𝕜) (E := Lp 𝕜 ∞ μ))
      from ⟨⟨rfl⟩, StrongDual.toWeakDual.injective⟩).t2Space
  have hb := ExpandedFA.P1.C13Alaoglu.weakStar_closedBall_isCompact
    𝕜 (Lp 𝕜 ∞ μ) 0 (max C 0) (le_max_right _ _)
  apply hb.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hb.isClosed
  rintro _ ⟨f, hf, rfl⟩
  simp only [sub_zero, Set.mem_ofPred_eq]
  exact (lp_pairing_norm_bound μ ∞ 1 f).trans ((hC f hf).trans (le_max_left _ _))

/-- Weak-star closure density identification, inducing topology and Alaoglu
give relative weak compactness. -/
theorem l1_compact_of_closure_densities {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) [SigmaFinite μ]
    (A : Set (Lp 𝕜 1 μ)) (hA : Bornology.IsBounded A)
    (hd : @closure _
      (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ))
      (integrationEmbedding μ '' A) ⊆ Set.range (integrationEmbedding μ)) :
    RelativelyWeaklyCompact μ A := by
  have he := l1_integrationEmbedding_inducing (𝕜 := 𝕜) μ
  letI : TopologicalSpace (Lp 𝕜 1 μ) := weakTopology μ
  letI : TopologicalSpace ((Lp 𝕜 ∞ μ) →L[𝕜] 𝕜) :=
    ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ)
  change IsCompact (closure A)
  rw [he.closure_eq_preimage_closure_image]
  exact he.isCompact_preimage' (l1_integrationEmbedding_closure_compact μ A hA) hd

/-- The canonical L∞ indicator has the expected ordinary a.e. values. -/
theorem unitIndicator_coeFn {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (E : Set X) (hE : MeasurableSet E) :
    (unitIndicator (𝕜 := 𝕜) μ E hE : X → 𝕜) =ᵐ[μ] E.indicator (fun _ => 1) :=
  MemLp.coeFn_toLp _

/-- A unit-bounded test supported in E is bounded by the norm integral on E. -/
theorem l1_integral_supported_test_bound {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (f : Lp 𝕜 1 μ) (h : Lp 𝕜 ∞ μ) (E : Set X) (hE : MeasurableSet E)
    (hb : ∀ᵐ x ∂μ, ‖h x‖ ≤ 1) (hz : ∀ᵐ x ∂μ, x ∉ E → h x = 0) :
    ‖integrationEmbedding μ f h‖ ≤ ∫ x in E, ‖f x‖ ∂μ := by
  rw [(lp_pairing_integral μ ∞ 1 f h).2]
  have hfi := memLp_one_iff_integrable.mp (Lp.memLp f)
  have hbound : ∀ᵐ x ∂μ, ‖h x * f x‖ ≤ E.indicator (fun x => ‖f x‖) x := by
    filter_upwards [hb, hz] with x hbx hzx
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx, norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hbx (norm_nonneg (f x))
    · simp only [Set.indicator_of_notMem hx, hzx hx, zero_mul, norm_zero, le_refl]
  simpa only [integral_indicator hE] using
    norm_integral_le_of_norm_le (hfi.norm.indicator hE) hbound

/-- Every uniform test bound survives weak-star closure. -/
theorem l1_weakStar_closure_test_bound {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (A : Set (Lp 𝕜 1 μ)) (h : Lp 𝕜 ∞ μ) (C : ℝ)
    (hb : ∀ f ∈ A, ‖integrationEmbedding μ f h‖ ≤ C)
    (L : Lp 𝕜 ∞ μ →L[𝕜] 𝕜)
    (hL : L ∈ @closure _
      (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ))
      (integrationEmbedding μ '' A)) : ‖L h‖ ≤ C := by
  letI : TopologicalSpace ((Lp 𝕜 ∞ μ) →L[𝕜] 𝕜) :=
    ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ)
  have he : Continuous (fun M : (Lp 𝕜 ∞ μ) →L[𝕜] 𝕜 => M h) := by
    let e : ((Lp 𝕜 ∞ μ) →L[𝕜] 𝕜) ≃ₗ[𝕜] WeakDual 𝕜 (Lp 𝕜 ∞ μ) :=
      StrongDual.toWeakDual
    have he' : Continuous e := continuous_induced_dom
    exact (WeakDual.eval_continuous h).comp he'
  exact (closure_minimal (by
    rintro _ ⟨f, hf, rfl⟩
    exact hb f hf) (isClosed_le he.norm continuous_const)) hL

/-- Both integral controls force order continuity on indicators for every
weak-star closure point; this is the countable-additivity input. -/
theorem l1_weakStar_closure_indicator_order_continuous {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (A : Set (Lp 𝕜 1 μ)) (hc : UniformIntegralControls μ A)
    (L : Lp 𝕜 ∞ μ →L[𝕜] 𝕜)
    (hL : L ∈ @closure _
      (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ))
      (integrationEmbedding μ '' A)) : IndicatorOrderContinuous μ L := by
  intro E hE hanti hnull
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := l1_controls_uniform_decreasing_sets
    (fun f : A => memLp_one_iff_integrable.mp (Lp.memLp f.val)) hc
    E hE hanti hnull (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hb : ∀ f ∈ A,
      ‖integrationEmbedding μ f (unitIndicator μ (E n) (hE n))‖ ≤ ε / 2 := by
    intro f hf
    have hi := unitIndicator_coeFn (𝕜 := 𝕜) μ (E n) (hE n)
    have ht := l1_integral_supported_test_bound μ f (unitIndicator μ (E n) (hE n))
      (E n) (hE n) (hi.mono fun x hx => by
        rw [hx]; by_cases hxE : x ∈ E n <;> simp [hxE])
      (hi.mono fun x hx hxE => by rw [hx]; simp [hxE])
    have hm : (∫ x in E n, ‖f x‖ ∂μ) ≤ ∫ x in E N, ‖f x‖ ∂μ :=
      setIntegral_mono_set (memLp_one_iff_integrable.mp (Lp.memLp f)).norm.integrableOn
        (ae_of_all _ (fun _ => norm_nonneg _))
        (ae_of_all _ (fun _ hx => hanti hn hx))
    exact ht.trans (hm.trans (hN ⟨f, hf⟩).le)
  have ht := l1_weakStar_closure_test_bound μ A (unitIndicator μ (E n) (hE n))
    (ε / 2) hb L hL
  simpa only [Real.dist_eq, sub_zero, abs_norm] using ht.trans_lt (half_lt_self hε)

/-- A measurable null set is the zero L∞ indicator. -/
theorem unitIndicator_eq_zero_of_null {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (E : Set X) (hE : MeasurableSet E) (hn : μ E = 0) :
    unitIndicator (𝕜 := 𝕜) μ E hE = 0 := by
  apply Lp.ext
  apply (unitIndicator_coeFn μ E hE).trans
  apply (indicator_ae_eq_zero.mpr (measure_mono_null inter_subset_left hn)).trans
  exact (Lp.coeFn_zero (E := 𝕜) (p := ∞) (μ := μ)).symm

/-- Disjoint finite unions of canonical indicators add in L∞. -/
theorem unitIndicator_finset_union {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (E : ℕ → Set X) (hE : ∀ i, MeasurableSet (E i))
    (hd : Pairwise (Disjoint on E)) (s : Finset ℕ) :
    unitIndicator (𝕜 := 𝕜) μ (⋃ i ∈ s, E i)
        (MeasurableSet.biUnion s.countable_toSet (fun i _ => hE i)) =
      ∑ i ∈ s, unitIndicator μ (E i) (hE i) := by
  apply Lp.ext
  have hs := ae_all_iff.mpr (fun i => unitIndicator_coeFn (𝕜 := 𝕜) μ (E i) (hE i))
  filter_upwards [unitIndicator_coeFn (𝕜 := 𝕜) μ (⋃ i ∈ s, E i)
      (MeasurableSet.biUnion s.countable_toSet (fun i _ => hE i)),
    Lp.coeFn_fun_finsetSum s (fun i => unitIndicator (𝕜 := 𝕜) μ (E i) (hE i)), hs]
      with x hx hy hz
  rw [hx, hy, Finset.indicator_biUnion_apply s E (fun i _ j _ hij => hd hij)]
  exact Finset.sum_congr rfl (fun i _ => (hz i).symm)

/-- The entire remainder after a finite partial union is one supported test.
Uniform control of the tail unions proves unconditional countable additivity. -/
theorem l1_weakStar_closure_hasSum_indicators {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (A : Set (Lp 𝕜 1 μ)) (hc : UniformIntegralControls μ A)
    (L : Lp 𝕜 ∞ μ →L[𝕜] 𝕜)
    (hL : L ∈ @closure _
      (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ))
      (integrationEmbedding μ '' A))
    (E : ℕ → Set X) (hE : ∀ n, MeasurableSet (E n))
    (hd : Pairwise (Disjoint on E)) :
    HasSum (fun n => L (unitIndicator μ (E n) (hE n)))
      (L (unitIndicator μ (⋃ n, E n) (MeasurableSet.iUnion hE))) := by
  classical
  let T : ℕ → Set X := fun n => ⋃ i, ⋃ (_ : n ≤ i), E i
  have hT (n : ℕ) : MeasurableSet (T n) :=
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hE i
  have hanti : Antitone T := fun n m hnm =>
    biUnion_mono (fun _ hi => hnm.trans hi) (fun _ _ => Subset.rfl)
  have hnull : μ (⋂ n, T n) = 0 := by
    have hn : (⋂ n, T n) = ∅ := by
      apply subset_antisymm _ (empty_subset _)
      intro x hx
      simp only [T, mem_iInter, mem_iUnion, exists_prop] at hx
      obtain ⟨j, _, hj⟩ := hx 0
      obtain ⟨k, hk, hkx⟩ := hx (j+1)
      exact (hd (by omega : j ≠ k)).ne_of_mem hj hkx rfl
    rw [hn, measure_empty]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := l1_controls_uniform_decreasing_sets
    (fun f : A => memLp_one_iff_integrable.mp (Lp.memLp f.val)) hc
    T hT hanti hnull (half_pos hε)
  refine ⟨Finset.range N, fun s hs => ?_⟩
  let U := ⋃ i ∈ s, E i
  have hU : MeasurableSet U := MeasurableSet.biUnion s.countable_toSet (fun i _ => hE i)
  have hsub : U ⊆ ⋃ i, E i := iUnion_subset fun i => iUnion_subset fun _ => subset_iUnion E i
  let D := (⋃ i, E i) \ U
  have hD : MeasurableSet D := (MeasurableSet.iUnion hE).diff hU
  have hDT : D ⊆ T N := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx.1
    have hNi : N ≤ i := by
      by_contra! h
      exact hx.2 (mem_iUnion_of_mem i (mem_iUnion_of_mem (hs (Finset.mem_range.mpr h)) hi))
    exact mem_iUnion_of_mem i (mem_iUnion_of_mem hNi hi)
  have heq : unitIndicator (𝕜 := 𝕜) μ D hD =
      unitIndicator μ (⋃ i, E i) (MeasurableSet.iUnion hE) -
        ∑ i ∈ s, unitIndicator μ (E i) (hE i) := by
    rw [← unitIndicator_finset_union μ E hE hd s]
    apply Lp.ext
    filter_upwards [unitIndicator_coeFn (𝕜 := 𝕜) μ D hD,
      unitIndicator_coeFn (𝕜 := 𝕜) μ (⋃ i, E i) (MeasurableSet.iUnion hE),
      unitIndicator_coeFn (𝕜 := 𝕜) μ U hU,
      Lp.coeFn_sub (unitIndicator (𝕜 := 𝕜) μ (⋃ i, E i) (MeasurableSet.iUnion hE))
        (unitIndicator μ U hU)] with x hx hy hz hw
    rw [hx, hw, Pi.sub_apply, hy, hz]
    exact congrFun (Set.indicator_sdiff hsub (fun _ => (1 : 𝕜))) x
  have hi := unitIndicator_coeFn (𝕜 := 𝕜) μ D hD
  have hb : ∀ f ∈ A, ‖integrationEmbedding μ f (unitIndicator μ D hD)‖ ≤ ε / 2 := by
    intro f hf
    have ht := l1_integral_supported_test_bound μ f (unitIndicator μ D hD) (T N) (hT N)
      (hi.mono fun x hx => by rw [hx]; by_cases hxD : x ∈ D <;> simp [hxD])
      (hi.mono fun x hx hxT => by rw [hx]; exact indicator_of_notMem (fun hxD => hxT (hDT hxD)) _)
    exact ht.trans (hN ⟨f,hf⟩).le
  have hbound := l1_weakStar_closure_test_bound μ A (unitIndicator μ D hD) (ε/2) hb L hL
  rw [dist_eq_norm, norm_sub_rev, ← map_sum, ← map_sub, ← heq]
  exact hbound.trans_lt (half_lt_self hε)

/-- Countable additivity supplies a genuine scalar vector measure associated
with a weak-star limit. -/
def weakStarClosureScalarMeasure {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (A : Set (Lp 𝕜 1 μ)) (hc : UniformIntegralControls μ A)
    (L : Lp 𝕜 ∞ μ →L[𝕜] 𝕜)
    (hL : L ∈ @closure _
      (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ))
      (integrationEmbedding μ '' A)) : VectorMeasure X 𝕜 where
  measureOf' E := if hE : MeasurableSet E then L (unitIndicator μ E hE) else 0
  empty' := by
    rw [dite_eq_left MeasurableSet.empty, unitIndicator_eq_zero_of_null μ ∅ _ (measure_empty), map_zero]
  not_measurable' := by intro E hE; exact dite_eq_right hE
  m_iUnion' := by
    intro E hE hd
    simpa only [dite_eq_left (MeasurableSet.iUnion hE), dite_eq_left (hE _)] using
      l1_weakStar_closure_hasSum_indicators μ A hc L hL _ hE hd

/-- The scalar measure vanishes on every μ-null measurable set. -/
theorem weakStarClosureScalarMeasure_absolutelyContinuous {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (A : Set (Lp 𝕜 1 μ)) (hc : UniformIntegralControls μ A)
    (L : Lp 𝕜 ∞ μ →L[𝕜] 𝕜) (hL) :
    weakStarClosureScalarMeasure μ A hc L hL ≪ᵥ μ.toENNRealVectorMeasure := by
  intro E hn
  by_cases hE : MeasurableSet E
  · rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at hn
    change (if h : MeasurableSet E then L (unitIndicator μ E h) else 0) = 0
    rw [dite_eq_left hE, unitIndicator_eq_zero_of_null μ E hE hn, map_zero]
  · exact VectorMeasure.not_measurable _ hE

/-- Applying signed Radon–Nikodym to the real and imaginary parts works
uniformly for either scalar field, with the manuscript's bilinear pairing. -/
theorem l1_weakStar_closure_density_on_indicators {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) [SigmaFinite μ]
    (A : Set (Lp 𝕜 1 μ)) (hc : UniformIntegralControls μ A)
    (L : Lp 𝕜 ∞ μ →L[𝕜] 𝕜)
    (hL : L ∈ @closure _
      (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (Lp 𝕜 ∞ μ))
      (integrationEmbedding μ '' A)) :
    ∃ g : X → 𝕜, Integrable g μ ∧
      ∀ (E : Set X) (hE : MeasurableSet E), L (unitIndicator μ E hE) = ∫ x in E, g x ∂μ := by
  let ν := weakStarClosureScalarMeasure μ A hc L hL
  have hν := weakStarClosureScalarMeasure_absolutelyContinuous μ A hc L hL
  let νr : SignedMeasure X := ν.mapRange (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).toAddMonoidHom
    RCLike.continuous_re
  let νi : SignedMeasure X := ν.mapRange (RCLike.imCLM : 𝕜 →L[ℝ] ℝ).toAddMonoidHom
    RCLike.continuous_im
  have hνr : νr ≪ᵥ μ.toENNRealVectorMeasure := by
    intro E hE
    change RCLike.re (ν E) = 0
    rw [hν hE, map_zero]
  have hνi : νi ≪ᵥ μ.toENNRealVectorMeasure := by
    intro E hE
    change RCLike.im (ν E) = 0
    rw [hν hE, map_zero]
  obtain ⟨gr, _, hgr, hr, _⟩ := signed_radon_nikodym μ νr hνr
  obtain ⟨gi, _, hgi, hi, _⟩ := signed_radon_nikodym μ νi hνi
  let g : X → 𝕜 := fun x => (gr x : 𝕜) + (gi x : 𝕜) * RCLike.I
  have hgr' : Integrable (fun x => (gr x : 𝕜)) μ := hgr.ofReal
  have hgi' : Integrable (fun x => (gi x : 𝕜) * RCLike.I) μ := hgi.ofReal.mul_const _
  have hg : Integrable g μ := hgr'.add hgi'
  refine ⟨g, hg, fun E hE => ?_⟩
  change L (unitIndicator μ E hE) = ∫ x in E, (gr x : 𝕜) + (gi x : 𝕜) * RCLike.I ∂μ
  rw [integral_add hgr'.integrableOn hgi'.integrableOn,
    integral_mul_const, integral_ofReal, integral_ofReal, ← hr E hE, ← hi E hE]
  change L (unitIndicator μ E hE) = (RCLike.re (ν E) : 𝕜) + (RCLike.im (ν E) : 𝕜) * RCLike.I
  rw [RCLike.re_add_im]
  change L (unitIndicator μ E hE) = (if h : MeasurableSet E then L (unitIndicator μ E h) else 0)
  rw [dite_eq_left hE]

/-- An L∞ a.e. bound controls its norm on an arbitrary measure space. -/
theorem linfinity_norm_le_of_ae_bound {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} (f : Lp 𝕜 ∞ μ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound hf)).trans_eq (ENNReal.toReal_ofReal hC)

/-- Scalar simple functions approximate any L∞ class in norm. Compactness
of bounded scalar balls makes nearest-point approximation uniform. -/
theorem linfinity_simple_approximation {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) (f : Lp 𝕜 ∞ μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : SimpleFunc X 𝕜, ‖f - (s.memLp_top μ).toLp s‖ < ε := by
  classical
  borelize 𝕜
  have htop : eLpNormEssSup (f : X → 𝕜) μ < ∞ := by
    simpa only [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] using Lp.eLpNorm_lt_top f
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp htop
  let e : ℕ → 𝕜 := TopologicalSpace.denseSeq 𝕜
  have hd : DenseRange e := TopologicalSpace.denseRange_denseSeq 𝕜
  have hcover : Metric.closedBall (0 : 𝕜) (C : ℝ) ⊆
      ⋃ n : ℕ, Metric.ball (e n) (ε / 2) := by
    intro z _
    obtain ⟨n, hn⟩ := hd.exists_dist_lt z (half_pos hε)
    exact mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : 𝕜) (C : ℝ)).elim_finite_subcover
    (fun n => Metric.ball (e n) (ε / 2)) (fun _ => Metric.isOpen_ball) hcover
  let N := t.sup id
  let s : SimpleFunc X 𝕜 := (SimpleFunc.nearestPt e N).comp f (Lp.stronglyMeasurable f).measurable
  have hclose : ∀ᵐ x ∂μ, ‖f x - s x‖ ≤ ε / 2 := by
    filter_upwards [hC] with x hx
    have hxball : f x ∈ Metric.closedBall (0 : 𝕜) (C : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (show ‖f x‖ ≤ (C : ℝ) from hx)
    obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp (ht hxball)
    have hdist := SimpleFunc.edist_nearestPt_le e (f x) (show n ≤ N from Finset.le_sup (f := fun i : ℕ => i) hn)
    have hlt : edist (SimpleFunc.nearestPt e N (f x)) (f x) < ENNReal.ofReal (ε/2) :=
      hdist.trans_lt (by
        rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (half_pos hε)]
        simpa only [Metric.mem_ball, dist_comm] using hxn)
    have hr := (ENNReal.ofReal_lt_ofReal_iff (half_pos hε)).mp
      (show ENNReal.ofReal (dist (SimpleFunc.nearestPt e N (f x)) (f x)) < _ by
        simpa only [edist_dist] using hlt)
    change ‖f x - SimpleFunc.nearestPt e N (f x)‖ ≤ ε / 2
    simpa only [dist_eq_norm, norm_sub_rev] using hr.le
  refine ⟨s, (linfinity_norm_le_of_ae_bound (f - (s.memLp_top μ).toLp s)
    (le_of_lt (half_pos hε)) ?_).trans_lt (half_lt_self hε)⟩
  filter_upwards [Lp.coeFn_sub f ((s.memLp_top μ).toLp s),
    (s.memLp_top μ).coeFn_toLp, hclose] with x hx hy hz
  simpa only [Pi.sub_apply, hx, hy] using hz

/-- Bounded scalar-linear functionals agreeing on measurable indicators agree
on all of L∞. This uses ordinary a.e. classes and no finite-mass hypothesis. -/
theorem linfinity_functional_ext_indicators {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (L M : Lp 𝕜 ∞ μ →L[𝕜] 𝕜)
    (h : ∀ (E : Set X) (hE : MeasurableSet E),
      L (unitIndicator μ E hE) = M (unitIndicator μ E hE)) : L = M := by
  classical
  let D := L - M
  have hzero (E : Set X) (hE : MeasurableSet E) : D (unitIndicator μ E hE) = 0 :=
    sub_eq_zero.mpr (h E hE)
  have hsimple (s : SimpleFunc X 𝕜) : D ((s.memLp_top μ).toLp s) = 0 := by
    induction s using SimpleFunc.induction with
    | @const c E hE =>
      have heq : ((SimpleFunc.piecewise E hE (SimpleFunc.const X c) (SimpleFunc.const X 0)).memLp_top μ).toLp _ =
          c • unitIndicator μ E hE := by
        apply Lp.ext
        filter_upwards [((SimpleFunc.piecewise E hE (SimpleFunc.const X c) (SimpleFunc.const X (0 : 𝕜))).memLp_top μ).coeFn_toLp,
          unitIndicator_coeFn (𝕜 := 𝕜) μ E hE,
          Lp.coeFn_smul c (unitIndicator (𝕜 := 𝕜) μ E hE)] with x hx hy hz
        rw [hx, hz, Pi.smul_apply, hy]
        by_cases hxE : x ∈ E <;> simp [SimpleFunc.coe_piecewise, hxE]
      rw [heq, map_smul, hzero, smul_zero]
    | @add f g _ hf hg =>
      have heq : ((f + g).memLp_top μ).toLp (f+g) =
          (f.memLp_top μ).toLp f + (g.memLp_top μ).toLp g := by
        simpa only [SimpleFunc.coe_add] using MemLp.toLp_add (f.memLp_top μ) (g.memLp_top μ)
      rw [heq, map_add, hf, hg, add_zero]
  apply ContinuousLinearMap.ext
  intro f
  apply sub_eq_zero.mp
  change D f = 0
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨s, hs⟩ := linfinity_simple_approximation μ f
    (show 0 < ε / (‖D‖ + 1) by positivity)
  have hb := D.le_opNorm (f - (s.memLp_top μ).toLp s)
  rw [map_sub, hsimple, sub_zero] at hb
  have hn : ‖D‖ * ‖f - (s.memLp_top μ).toLp s‖ < ε := by
    have hc := (mul_lt_mul_of_pos_left hs (by positivity : 0 < ‖D‖ + 1))
    rw [mul_div_cancel₀ ε (by positivity : ‖D‖ + 1 ≠ 0)] at hc
    nlinarith [norm_nonneg (f - (s.memLp_top μ).toLp s)]
  simpa only [zero_add] using (hb.trans_lt hn).le

/-- Every weak-star closure point has a genuine ordinary L¹ density. -/
theorem scalar_l1_weakStar_closure_densities : WeakStarClosureDensities.{u} := by
  intro X 𝕜 _ _ μ _ A hA L hL
  obtain ⟨g, hg, hsets⟩ := l1_weakStar_closure_density_on_indicators μ A hA.2 L hL
  let gLp : Lp 𝕜 1 μ := (memLp_one_iff_integrable.mpr hg).toLp g
  have hgeq : (gLp : X → 𝕜) =ᵐ[μ] g := (memLp_one_iff_integrable.mpr hg).coeFn_toLp
  have hrep : L = integrationEmbedding μ gLp := by
    apply linfinity_functional_ext_indicators μ L (integrationEmbedding μ gLp)
    intro E hE
    rw [hsets E hE, (lp_pairing_integral μ ∞ 1 gLp (unitIndicator μ E hE)).2]
    rw [← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards [unitIndicator_coeFn (𝕜 := 𝕜) μ E hE, hgeq] with x hx hy
    rw [hx, hy]
    by_cases hxE : x ∈ E <;> simp [hxE]
  refine ⟨gLp, fun h => ?_⟩
  rw [hrep, (lp_pairing_integral μ ∞ 1 gLp h).2]

/-- Sufficiency includes the identification of the whole compact closure. -/
theorem scalar_l1_dunford_pettis_sufficiency : Sufficiency.{u} := by
  intro X 𝕜 _ _ μ _ A hA
  apply l1_compact_of_closure_densities μ A hA.1
  intro L hL
  obtain ⟨g, hg⟩ := scalar_l1_weakStar_closure_densities μ A hA L hL
  refine ⟨g, ?_⟩
  ext h
  exact (lp_pairing_integral μ ∞ 1 g h).2.trans (hg h).symm

/-- Dunford–Pettis in scalar L¹ on any sigma-finite measure space. -/
theorem scalar_l1_dunford_pettis : DunfordPettis.{u} := by
  intro X 𝕜 _ _ μ _ A
  exact ⟨scalar_l1_dunford_pettis_necessity μ A,
    scalar_l1_dunford_pettis_sufficiency μ A⟩

end ExpandedFA.FunctionSpaces
