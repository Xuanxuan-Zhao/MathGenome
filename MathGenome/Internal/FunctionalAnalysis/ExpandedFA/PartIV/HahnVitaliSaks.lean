import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HahnVitaliSaks
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SetwiseUniformIntegrability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarL1DunfordPettis
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Batteries.Tactic.OpenPrivate

open MeasureTheory Filter Set
open scoped ENNReal Topology
universe u
noncomputable section

namespace ExpandedFA.PartIV.HahnVitaliSaks

open ExpandedFA.FunctionSpaces
open ExpandedFA.FunctionSpaces.WeakL1UniformIntegrabilitySpec
open ExpandedFA.FunctionSpaces.ScalarL1DunfordPettisSpec
open private l1_compact_subsequence from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarL1DunfordPettis

/-- Indicator tests are continuous linear functionals on L¹ even for infinite sets. -/
theorem pairing_unitIndicator {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X)
    (f : Lp 𝕜 1 μ) (A : Set X) (hA : MeasurableSet A) :
    lpIntegralPairing μ 1 ∞ (unitIndicator μ A hA) f = ∫ x in A, f x ∂μ := by
  change ScalarLpIntegralPairingSpec.IntegralPairingValue μ 1 ∞
    (unitIndicator μ A hA) f = _
  rw [(lp_pairing_integral μ 1 ∞ (unitIndicator μ A hA) f).2]
  calc
    (∫ x, f x * unitIndicator μ A hA x ∂μ) =
        ∫ x, A.indicator (fun x => f x) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [unitIndicator_coeFn (𝕜 := 𝕜) μ A hA] with x hx
      rw [hx]
      by_cases ha : x ∈ A <;> simp [ha]
    _ = _ := integral_indicator hA

/-- Two weak subsequential limits have the same prescribed setwise integrals. -/
theorem setwise_subsequence_limit_unique {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) [SigmaFinite μ]
    (f : ℕ → Lp 𝕜 1 μ)
    (hf : SetwiseUniformIntegrability.Spec.SetwiseConvergent μ (fun n => (f n : X → 𝕜)))
    (g h : Lp 𝕜 1 μ) (r s : ℕ → ℕ)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    (hg : WeaklyConverges μ (f ∘ r) g) (hh : WeaklyConverges μ (f ∘ s) h) : g = h := by
  apply Lp.ext
  apply Integrable.ae_eq_of_forall_setIntegral_eq (g : X → 𝕜) (h : X → 𝕜)
    (L1.integrable_coeFn g) (L1.integrable_coeFn h)
  intro A hA _
  obtain ⟨z, hz⟩ := hf A hA
  have hgA := hg (lpIntegralPairing μ 1 ∞ (unitIndicator μ A hA))
  have hhA := hh (lpIntegralPairing μ 1 ∞ (unitIndicator μ A hA))
  simp only [pairing_unitIndicator, Function.comp_apply] at hgA hhA
  exact (tendsto_nhds_unique hgA (hz.comp hr)).trans
    (tendsto_nhds_unique (hz.comp hs) hhA)

/-- The accepted uniform controls give relative weak compactness of the range. -/
theorem setwise_range_relativelyWeaklyCompact {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) [SigmaFinite μ]
    (f : ℕ → Lp 𝕜 1 μ)
    (hf : SetwiseUniformIntegrability.Spec.SetwiseConvergent μ (fun n => (f n : X → 𝕜))) :
    RelativelyWeaklyCompact μ (range f) := by
  obtain ⟨⟨C, hC, hb⟩, hs, ht⟩ :=
    SetwiseUniformIntegrability.setwise_uniform_integrability X 𝕜 μ
      (fun n => (f n : X → 𝕜)) (fun n => L1.integrable_coeFn (f n)) hf
  apply scalar_l1_dunford_pettis_sufficiency μ (range f)
  constructor
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [Lp.norm_def, eLpNorm_one_eq_ofReal_integral_norm (L1.integrable_coeFn (f n)),
      ENNReal.toReal_ofReal (integral_nonneg (fun _ => norm_nonneg _))]
    exact hb n
  · constructor
    · intro ε hε
      obtain ⟨δ, hδ, h⟩ := hs ε hε
      exact ⟨δ, hδ, fun A hA hμ i => by
        obtain ⟨n, hn⟩ := i.property
        simpa only [hn] using h A hA hμ n⟩
    · intro ε hε
      obtain ⟨F, hF, hμF, h⟩ := ht ε hε
      exact ⟨F, hF, hμF, fun i => by
        obtain ⟨n, hn⟩ := i.property
        simpa only [hn] using h n⟩

/-- Sequential compactness and uniqueness give convergence of the entire sequence. -/
theorem hahn_vitali_saks : Spec.MainStatement.{u} := by
  intro X 𝕜 _ _ μ _ f hf
  have hc := SetwiseUniformIntegrability.setwise_uniform_integrability X 𝕜 μ
    (fun n => (f n : X → 𝕜)) (fun n => L1.integrable_coeFn (f n)) hf
  have hcompact := setwise_range_relativelyWeaklyCompact μ f hf
  obtain ⟨g, r, hr, hg⟩ := l1_compact_subsequence hcompact f (fun n => mem_range_self n)
  have hfull : WeaklyConverges μ f g := by
    intro L
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨h, s, hs, hh⟩ := l1_compact_subsequence hcompact (f ∘ ns)
      (fun n => mem_range_self (ns n))
    have heq : g = h := setwise_subsequence_limit_unique μ f hf g h r (ns ∘ s)
      hr.tendsto_atTop (hns.comp hs.tendsto_atTop) hg hh
    exact ⟨s, by simpa only [Function.comp_apply, heq] using hh L⟩
  exact ⟨hc, g, hfull, (weak_l1_convergence_tests μ f g).mp hfull⟩

/-- Weak Cauchyness implies setwise convergence, so the limit remains in L¹. -/
theorem l1_weak_sequentially_complete : Spec.WeakSequentialCompleteness.{u} := by
  intro X 𝕜 _ _ μ _ f hf
  have hs : SetwiseUniformIntegrability.Spec.SetwiseConvergent μ (fun n => (f n : X → 𝕜)) := by
    intro A hA
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete
      (hf (lpIntegralPairing μ 1 ∞ (unitIndicator μ A hA)))
    exact ⟨z, by simpa only [pairing_unitIndicator] using hz⟩
  obtain ⟨_, g, hg, _⟩ := hahn_vitali_saks μ f hs
  exact ⟨g, hg⟩

/-- Translate the source's small-set integrals to Mathlib's L¹ uniform
integrability. The half-threshold accommodates its non-strict measure bound. -/
theorem smallSetControl_unifIntegrable {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} (f : ℕ → X → 𝕜)
    (hi : ∀ n, Integrable (f n) μ) (hs : SmallSetControl μ f) :
    UnifIntegrable f 1 μ := by
  apply unifIntegrable_iff'.mpr
  intro ε hε
  rcases eq_top_or_lt_top ε with rfl | htop
  · exact ⟨1, zero_lt_one, fun _ _ _ _ => le_top⟩
  obtain ⟨δ, hδ, h⟩ := hs ε.toReal (ENNReal.toReal_pos hε.ne' htop.ne)
  refine ⟨ENNReal.ofReal (δ / 2), ENNReal.ofReal_pos.mpr (half_pos hδ), ?_⟩
  intro n A hA hμA
  have hsmall : μ A < ENNReal.ofReal δ :=
    hμA.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδ).mpr (half_lt_self hδ))
  rw [eLpNorm_one_eq_ofReal_integral_norm (hi n).integrableOn]
  exact (ENNReal.ofReal_le_ofReal (h A hA hsmall n).le).trans
    (ENNReal.ofReal_toReal htop.ne).le

/-- The finite-measure tail requirement matches the non-finite-space Vitali theorem. -/
theorem tailControl_unifTight {X : Type u} {𝕜 : Type}
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X} (f : ℕ → X → 𝕜)
    (hi : ∀ n, Integrable (f n) μ) (ht : TailControl μ f) :
    UnifTight f 1 μ := by
  apply (unifTight_iff_real f 1 μ).mpr
  intro ε hε
  obtain ⟨F, hF, hμF, h⟩ := ht ε hε
  refine ⟨F, hμF.ne, fun n => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hF.compl.nullMeasurableSet,
    eLpNorm_one_eq_ofReal_integral_norm (hi n).integrableOn]
  exact ENNReal.ofReal_le_ofReal (h n).le

/-- Vitali convergence also identifies an arbitrary a.e. limit with the weak limit. -/
theorem weak_ae_l1_norm_convergence : Spec.VitaliConsequence.{u} := by
  intro X 𝕜 _ _ μ _ f g a hw ha
  have hi : ∀ n, Integrable (f n : X → 𝕜) μ := fun n => L1.integrable_coeFn (f n)
  obtain ⟨hs, ht⟩ := (weak_l1_convergent_controls μ f g hw).1
  have hui := smallSetControl_unifIntegrable (fun n => (f n : X → 𝕜)) hi hs
  have hut := tailControl_unifTight (fun n => (f n : X → 𝕜)) hi ht
  obtain ⟨C, hC, hb⟩ := ExpandedFA.P1.C12BoundedSequences.norm_bound_of_scalar_bounds
    𝕜 (Lp 𝕜 1 μ) ℕ f (by
      intro L
      obtain ⟨B, hB⟩ := (hw L).norm.bddAbove_range
      exact ⟨B, fun n => hB (mem_range_self n)⟩)
  have hUI : UniformIntegrable (fun n => (f n : X → 𝕜)) 1 μ := by
    refine ⟨hui, ⟨⟨C, hC⟩, fun n => ?_⟩⟩
    rw [← Lp.enorm_def, enorm_eq_nnnorm]
    exact ENNReal.coe_le_coe.mpr (show ‖f n‖₊ ≤ ⟨C, hC⟩ from hb n)
  have haLp : MemLp a 1 μ := hUI.memLp_of_ae_tendsto ha
  have hn : Tendsto f atTop (𝓝 (haLp.toLp a)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm f a haLp).mpr
      (tendsto_Lp_of_tendsto_ae (by rfl) (by simp)
        (fun n => (Lp.aestronglyMeasurable (f n))) haLp hui hut ha)
  have heq : haLp.toLp a = g := by
    apply Lp.ext
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
      (L1.integrable_coeFn _) (L1.integrable_coeFn _)
    intro A hA _
    let L := lpIntegralPairing (𝕜 := 𝕜) μ 1 ∞ (unitIndicator μ A hA)
    have h1 := L.continuous.tendsto (haLp.toLp a) |>.comp hn
    have h2 := hw L
    simpa only [L, pairing_unitIndicator] using tendsto_nhds_unique h1 h2
  exact ⟨(haLp.coeFn_toLp).symm.trans (by rw [heq]), heq ▸ hn⟩

end ExpandedFA.PartIV.HahnVitaliSaks
