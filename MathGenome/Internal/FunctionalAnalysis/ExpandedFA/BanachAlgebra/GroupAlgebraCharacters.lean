import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.BanachAlgebra.GroupAlgebraCharacters



universe u
variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

abbrev L1 (μ : Measure G) := _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.L1 μ

section Translations
variable (μ : Measure G) [μ.IsMulLeftInvariant]

abbrev translate : _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.TranslateType μ := _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.translateValue μ

abbrev convolution : _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.ConvolutionType μ := _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.convolutionValue μ

/-- Translation preserves the native L¹ norm, with no finiteness hypothesis. -/
@[simp] theorem norm_translate (x : G) (f : L1 μ) : ‖translate μ x f‖ = ‖f‖ :=
  (translate μ x).norm_map f

theorem translate_ae (x : G) (f : L1 μ) :
    translate μ x f =ᵐ[μ] fun t => f (x⁻¹ * t) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_left μ x⁻¹)

@[simp] theorem translate_one (f : L1 μ) : translate μ 1 f = f := by
  apply Lp.ext
  simpa only [inv_one, one_mul] using translate_ae μ 1 f

theorem translate_mul (x y : G) (f : L1 μ) :
    translate μ (x * y) f = translate μ x (translate μ y f) := by
  change Lp.compMeasurePreserving _ _ f = Lp.compMeasurePreserving _ _
    (Lp.compMeasurePreserving _ _ f)
  rw [← Lp.compMeasurePreserving_comp_apply]
  have heq : (fun t : G => (x * y)⁻¹ * t) =
      ((fun t : G => y⁻¹ * t) ∘ fun t => x⁻¹ * t) := by
    funext t
    simp [mul_assoc]
  simp only [heq]

/-- The Bochner formula has the correct Young estimate, even before its
integrability is established. This estimate alone is not the algebra theorem. -/
theorem convolution_norm_le (f g : L1 μ) : ‖convolution μ f g‖ ≤ ‖f‖ * ‖g‖ := by
  calc
    ‖convolution μ f g‖ ≤ ∫ x, ‖f x • translate μ x g‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = (∫ x, ‖f x‖ ∂μ) * ‖g‖ := by
      simp_rw [norm_smul, norm_translate, integral_mul_const]
    _ = ‖f‖ * ‖g‖ := by
      congr 1
      rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
      exact (MeasureTheory.L1.norm_def f).symm

end Translations

/-- Inner regularity on finite-measure sets gives a countable compact cover
up to a null set. No normality assumption on the ambient space is needed. -/
theorem finite_measure_compact_cover (μ : Measure G) [μ.InnerRegularCompactLTTop]
    {s : Set G} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    ∃ K : ℕ → Set G, (∀ n, IsCompact (K n)) ∧ μ (s \ ⋃ n, K n) = 0 := by
  have hε (n : ℕ) : ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  choose K hKsub hKcomp hKerror using fun n => hs.exists_isCompact_sdiff_lt hμs (hε n)
  refine ⟨K, hKcomp, le_antisymm ?_ bot_le⟩
  have hlim : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr ENNReal.tendsto_inv_nat_nhds_zero
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun n =>
    (measure_mono (Set.sdiff_subset_sdiff_right (Set.subset_iUnion K n))).trans (hKerror n).le

/-- Localization to countably many compact sets establishes strong
measurability of the weighted continuous orbit, without a separable target. -/
theorem integrable_smul_continuous_bounded {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (μ : Measure G) [μ.InnerRegularCompactLTTop]
    {f : G → ℂ} (hf : Integrable f μ) (hfm : Measurable f) {v : G → E}
    (hv : Continuous v) {C : ℝ} (hC : ∀ x, ‖v x‖ ≤ C) :
    Integrable (fun x => f x • v x) μ := by
  let s : ℕ → Set G := fun m => {x | ((m + 1 : ℕ) : ℝ)⁻¹ ≤ ‖f x‖}
  have hs (m : ℕ) : MeasurableSet (s m) := measurableSet_le measurable_const hfm.norm
  have hfinite (m : ℕ) : μ (s m) ≠ ∞ :=
    (hf.measure_norm_ge_lt_top (by positivity : 0 < ((m + 1 : ℕ) : ℝ)⁻¹)).ne
  choose K hKcomp hKnull using fun m => finite_measure_compact_cover μ (hs m) (hfinite m)
  let U : Set G := ⋃ m, ⋃ n, K m n
  have hU : MeasurableSet U := .iUnion fun m => .iUnion fun n => (hKcomp m n).measurableSet
  have hvU : AEStronglyMeasurable v (μ.restrict U) := by
    apply aestronglyMeasurable_iUnion_iff.mpr
    intro m
    apply aestronglyMeasurable_iUnion_iff.mpr
    intro n
    exact hv.continuousOn.aestronglyMeasurable_of_isCompact (hKcomp m n)
      (hKcomp m n).measurableSet
  have hmeas : AEStronglyMeasurable (fun x => f x • v x) μ := by
    have hprod := hf.aestronglyMeasurable.smul ((aestronglyMeasurable_indicator_iff hU).mpr hvU)
    apply hprod.congr
    have hae : ∀ᵐ x ∂μ, ∀ m, x ∉ s m \ ⋃ n, K m n := by
      apply ae_all_iff.mpr
      intro m
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_mem_eq] using hKnull m
    filter_upwards [hae] with x hx
    by_cases hxu : x ∈ U
    · simp [Set.indicator_of_mem hxu]
    · have hfx : f x = 0 := by
        by_contra hne
        have hp : 0 < ‖f x‖ := norm_pos_iff.mpr hne
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hp
        have hxs : x ∈ s m := by
          simpa only [s, Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one, one_div] using hm.le
        have hxK : x ∈ ⋃ n, K m n := by
          by_contra hn
          exact hx m ⟨hxs, hn⟩
        exact hxu (Set.mem_iUnion.mpr ⟨m, hxK⟩)
      simp [hfx]
  apply (hf.norm.mul_const C).mono' hmeas
  exact Eventually.of_forall fun x => by
    simpa only [norm_smul] using mul_le_mul_of_nonneg_left (hC x) (norm_nonneg (f x))

section CompactApproximation
open Set TopologicalSpace

variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [MeasurableSpace α] [BorelSpace α]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ : Measure α} {p : ℝ≥0∞}

/-- A local compact cutoff approximates a compact indicator in Lᵖ.
This uses the locally compact Urysohn lemma, without global normality. -/
theorem compact_cutoff_approximation [μ.Regular] (hp : p ≠ ∞) {s u : Set α}
    (s_compact : IsCompact s) (u_open : IsOpen u) (hsu : s ⊆ u) (hs : μ s ≠ ∞) (c : E)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ f : α → E, Continuous f ∧
      eLpNorm (fun x => f x - s.indicator (fun _ => c) x) p μ ≤ ε ∧
      (∀ x, ‖f x‖ ≤ ‖c‖) ∧ Function.support f ⊆ u ∧ MemLp f p μ := by
  obtain ⟨η, η_pos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → NullMeasurableSet s μ →
          eLpNorm (s.indicator fun _x => c) p μ ≤ ε :=
    exists_eLpNorm_indicator_le hp c hε
  have ηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_lt_coe.2 η_pos
  obtain ⟨V, sV, V_open, h'V, hV⟩ :=
    s_compact.measurableSet.exists_isOpen_sdiff_lt hs ηpos.ne'
  let v := u ∩ V
  have hsv : s ⊆ v := subset_inter hsu sV
  have hμv : μ v < ∞ := (measure_mono inter_subset_right).trans_lt h'V
  obtain ⟨g, hgs, hgcompact, hgv, hg_range⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen s_compact
      (u_open.inter V_open) hsv
  have hgvzero : ∀ x, x ∉ v → g x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hgv h))
  have g_norm : ∀ x, ‖g x‖ = g x := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_range x).1]
  have gc_bd0 : ∀ x, ‖g x • c‖ ≤ ‖c‖ := by
    intro x
    simp only [norm_smul, g_norm x]
    exact mul_le_of_le_one_left (norm_nonneg _) (hg_range x).2
  have gc_bd : ∀ x,
      ‖g x • c - s.indicator (fun _ => c) x‖ ≤ ‖(v \ s).indicator (fun _ => c) x‖ := by
    intro x
    by_cases hv : x ∈ v
    · rw [← Set.sdiff_union_of_subset hsv] at hv
      rcases hv with hsv | hs
      · simpa only [hsv.2, Set.indicator_of_notMem, not_false_iff, sub_zero, hsv,
          Set.indicator_of_mem] using gc_bd0 x
      · simp [hgs hs, hs]
    · simp [hgvzero x hv, show x ∉ s from fun h => hv (hsv h)]
  have gc_support : (Function.support fun x : α => g x • c) ⊆ v := by
    refine Function.support_subset_iff'.2 fun x hx => ?_
    simp [hgvzero x hx]
  have gc_mem : MemLp (fun x => g x • c) p μ := by
    refine MemLp.smul ?_ (memLp_top_const _) (p := p) (q := ∞)
    have hv : MeasurableSet v := u_open.measurableSet.inter V_open.measurableSet
    have : eLpNorm (v.indicator fun _x => (1 : ℝ)) p μ < ∞ :=
      (eLpNorm_indicator_const_le _ _ hv.nullMeasurableSet).trans_lt <| by
        simp [lt_top_iff_ne_top, hμv.ne]
    refine (eLpNorm_mono g.continuous.aestronglyMeasurable fun x => ?_).trans_lt this
    by_cases hx : x ∈ v
    · simp only [hx, abs_of_nonneg (hg_range x).1, (hg_range x).2, Real.norm_eq_abs,
        indicator_of_mem, CStarRing.norm_one]
    · simp [hgvzero x hx]
  refine ⟨fun x => g x • c, by fun_prop,
    (eLpNorm_mono (gc_mem.aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator s_compact.measurableSet)) gc_bd).trans ?_,
    gc_bd0, gc_support.trans inter_subset_left, gc_mem⟩
  exact hη _ ((measure_mono (sdiff_subset_sdiff inter_subset_right Subset.rfl)).trans hV.le)
    ((u_open.measurableSet.inter V_open.measurableSet).diff
      s_compact.measurableSet).nullMeasurableSet

/-- Compactly supported continuous functions are dense for a regular measure
on a locally compact Hausdorff space, with no normality assumption. -/
theorem exists_compact_continuous_approximation
    [μ.Regular]
    (hp : p ≠ ∞) {f : α → E} (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α → E, HasCompactSupport g ∧ eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ := by
  suffices H :
      ∃ g : α → E, eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ ∧ HasCompactSupport g by
    rcases H with ⟨g, hg, g_cont, g_mem, g_support⟩
    exact ⟨g, g_support, hg, g_cont, g_mem⟩
  -- It suffices to check that the set of functions we consider approximates characteristic
  -- functions, is stable under addition and consists of ae strongly measurable functions.
  -- First check the latter easy facts.
  apply hf.induction_dense hp _ _ _ hε
  rotate_left
  -- stability under addition
  · rintro f g ⟨f_cont, f_mem, hf⟩ ⟨g_cont, g_mem, hg⟩
    exact ⟨f_cont.add g_cont, f_mem.add g_mem, hf.add hg⟩
  -- We are left with approximating characteristic functions.
  -- Approximate a finite-measure set from inside by a compact set, then use a local cutoff.
  intro c t ht htμ ε hε
  rcases exists_Lp_half E μ p hε with ⟨δ, δpos, hδ⟩
  obtain ⟨η, ηpos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → NullMeasurableSet s μ →
          eLpNorm (s.indicator fun _x => c) p μ ≤ δ :=
    exists_eLpNorm_indicator_le hp c δpos.ne'
  have hη_pos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
  obtain ⟨s, st, s_compact, s_closed, μs⟩ :
      ∃ s, s ⊆ t ∧ IsCompact s ∧ IsClosed s ∧ μ (t \ s) < η :=
    ht.exists_isCompact_isClosed_sdiff_lt htμ.ne hη_pos'.ne'
  have hsμ : μ s < ∞ := (measure_mono st).trans_lt htμ
  have I1 : eLpNorm ((s.indicator fun _y => c) - t.indicator fun _y => c) p μ ≤ δ := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
    exact hη _ μs.le (ht.diff s_closed.measurableSet).nullMeasurableSet
  obtain ⟨k, k_compact, sk⟩ : ∃ k : Set α, IsCompact k ∧ s ⊆ interior k :=
    exists_compact_superset s_compact
  rcases compact_cutoff_approximation hp s_compact isOpen_interior sk hsμ.ne c δpos.ne'
    with ⟨f, f_cont, I2, _f_bound, f_support, f_mem⟩
  have I3 : eLpNorm (f - t.indicator fun _y => c) p μ ≤ ε := by
    convert (hδ _ _ I2 I1).le using 2
    ext x
    simp
  refine ⟨f, I3, f_cont, f_mem, HasCompactSupport.intro k_compact fun x hx => ?_⟩
  rw [← Function.notMem_support]
  contrapose hx
  exact interior_subset (f_support hx)




end CompactApproximation

section HaarTranslations
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Joint continuity in the translating group element and the L¹ vector.
This library theorem uses local finiteness and inner regularity, not SFinite. -/
theorem continuous_translate :
    Continuous (fun xf : G × L1 μ => translate μ xf.1 xf.2) := by
  let : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  let a : G × L1 μ → Gᵈᵐᵃ × L1 μ :=
    fun xf => (DomMulAct.mk (xf.1⁻¹), xf.2)
  have ha : Continuous a :=
    (DomMulAct.continuous_mk.comp continuous_fst.inv).prodMk continuous_snd
  exact continuous_smul.comp ha

/-- The L¹-valued convolution integrand is Bochner integrable for arbitrary
regular Haar measure, including Haar measures that are not σ-finite. -/
theorem convolution_integrable (f g : L1 μ) :
    Integrable (fun x => f x • translate μ x g) μ := by
  apply integrable_smul_continuous_bounded μ (L1.integrable_coeFn f)
    (Lp.stronglyMeasurable f).measurable (continuous_translate μ |>.comp (continuous_id.prodMk continuous_const))
  intro x
  exact (norm_translate μ x g).le

theorem convolution_add_left (f g h : L1 μ) :
    convolution μ (f + g) h = convolution μ f h + convolution μ g h := by
  change (∫ x, (f + g) x • translate μ x h ∂μ) = _
  rw [integral_congr_ae (EventuallyEq.smul (Lp.coeFn_add f g) EventuallyEq.rfl)]
  simp_rw [Pi.add_apply, add_smul]
  exact integral_add (convolution_integrable μ f h) (convolution_integrable μ g h)

theorem convolution_add_right (f g h : L1 μ) :
    convolution μ f (g + h) = convolution μ f g + convolution μ f h := by
  change (∫ x, f x • translate μ x (g + h) ∂μ) = _
  simp_rw [map_add, smul_add]
  exact integral_add (convolution_integrable μ f g) (convolution_integrable μ f h)

theorem convolution_smul_left (c : ℂ) (f g : L1 μ) :
    convolution μ (c • f) g = c • convolution μ f g := by
  change (∫ x, (c • f) x • translate μ x g ∂μ) = _
  rw [integral_congr_ae (EventuallyEq.smul (Lp.coeFn_smul c f) EventuallyEq.rfl)]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, integral_smul]
  rfl

theorem convolution_smul_right (c : ℂ) (f g : L1 μ) :
    convolution μ f (c • g) = c • convolution μ f g := by
  change (∫ x, f x • translate μ x (c • g) ∂μ) = _
  simp_rw [map_smul, smul_comm (f _) c, integral_smul]
  rfl

@[simp] theorem convolution_zero_left (f : L1 μ) : convolution μ 0 f = 0 := by
  change (∫ x, (0 : L1 μ) x • translate μ x f ∂μ) = 0
  rw [integral_congr_ae (EventuallyEq.smul (Lp.coeFn_zero ℂ 1 μ) EventuallyEq.rfl)]
  simp

@[simp] theorem convolution_zero_right (f : L1 μ) : convolution μ f 0 = 0 := by
  change (∫ x, f x • translate μ x 0 ∂μ) = 0
  simp

/-- Translation may be passed through the L¹-valued integral. -/
theorem translate_convolution_right (x : G) (f g : L1 μ) :
    translate μ x (convolution μ f g) = convolution μ f (translate μ x g) := by
  change (translate μ x).toContinuousLinearMap (∫ y, f y • translate μ y g ∂μ) = _
  rw [← (translate μ x).toContinuousLinearMap.integral_comp_comm (convolution_integrable μ f g)]
  simp only [LinearIsometry.coe_toContinuousLinearMap, map_smul]
  congr 1
  funext y
  rw [← translate_mul, mul_comm x y, translate_mul]

/-- Change of variables in a single Haar integral gives covariance in the
first argument too, without any product-measure hypothesis. -/
theorem convolution_translate_left (x : G) (f g : L1 μ) :
    convolution μ (translate μ x f) g = translate μ x (convolution μ f g) := by
  change (∫ t, (translate μ x f) t • translate μ t g ∂μ) = _
  have heq : (fun t => (translate μ x f) t • translate μ t g) =ᵐ[μ]
      (fun t => f (x⁻¹ * t) • translate μ t g) := by
    filter_upwards [translate_ae μ x f] with t ht
    rw [ht]
  rw [integral_congr_ae heq]
  rw [← integral_mul_left_eq_self (fun t => f (x⁻¹ * t) • translate μ t g) x]
  simp only [inv_mul_cancel_left, translate_mul]
  simpa only [map_smul, LinearIsometry.coe_toContinuousLinearMap, convolution,
    _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.convolutionValue] using
    (translate μ x).toContinuousLinearMap.integral_comp_comm (convolution_integrable μ f g)

/-- Convolution by a fixed vector is a bounded complex-linear operator. -/
def convolutionRightLinear (f : L1 μ) : L1 μ →L[ℂ] L1 μ :=
  ({ toFun := convolution μ f
     map_add' := convolution_add_right μ f
     map_smul' := fun c g => convolution_smul_right μ c f g } : L1 μ →ₗ[ℂ] L1 μ).mkContinuous
    ‖f‖ (convolution_norm_le μ f)

@[simp] theorem convolutionRightLinear_apply (f g : L1 μ) :
    convolutionRightLinear μ f g = convolution μ f g := rfl

/-- The first-variable operator uses the same native norm estimate. -/
def convolutionLeftLinear (g : L1 μ) : L1 μ →L[ℂ] L1 μ :=
  ({ toFun := fun f => convolution μ f g
     map_add' := fun f h => convolution_add_left μ f h g
     map_smul' := fun c f => convolution_smul_left μ c f g } : L1 μ →ₗ[ℂ] L1 μ).mkContinuous
    ‖g‖ (fun f => by
      change ‖convolution μ f g‖ ≤ ‖g‖ * ‖f‖
      rw [mul_comm]
      exact convolution_norm_le μ f g)

@[simp] theorem convolutionLeftLinear_apply (g f : L1 μ) :
    convolutionLeftLinear μ g f = convolution μ f g := rfl

/-- Passing a bounded multiplication map through the Bochner integral and
using translation covariance proves associativity without product Fubini. -/
theorem convolution_assoc (f g h : L1 μ) :
    convolution μ (convolution μ f g) h = convolution μ f (convolution μ g h) := by
  change convolutionLeftLinear μ h (∫ x, f x • translate μ x g ∂μ) = _
  rw [← (convolutionLeftLinear μ h).integral_comp_comm (convolution_integrable μ f g)]
  simp only [map_smul, convolutionLeftLinear_apply, convolution_translate_left]
  rfl

/-- Native nonunital Banach-ring structure, with exactly the original
L¹ additive group and metric. Its commutative refinement is constructed below. -/
abbrev convolutionRing : NonUnitalNormedRing (L1 μ) :=
  { (inferInstance : NormedAddCommGroup (L1 μ)) with
    mul := convolution μ
    mul_assoc := convolution_assoc μ
    left_distrib := convolution_add_right μ
    right_distrib := convolution_add_left μ
    zero_mul := convolution_zero_left μ
    mul_zero := convolution_zero_right μ
    norm_mul_le := convolution_norm_le μ
    dist_eq := dist_eq_norm_neg_add }

/-- Scalar compatibility for the concrete native multiplication. -/
theorem convolutionScalarTower :
    let := convolutionRing μ
    IsScalarTower ℂ (L1 μ) (L1 μ) := by
  let := convolutionRing μ
  exact ⟨convolution_smul_left μ⟩

theorem convolutionSMulComm :
    let := convolutionRing μ
    SMulCommClass ℂ (L1 μ) (L1 μ) := by
  let := convolutionRing μ
  exact ⟨fun c f g => (convolution_smul_right μ c f g).symm⟩

/-- The algebraic character predicate is precisely the accepted convention,
once the actual convolution multiplication is installed. -/
theorem character_convention (χ : L1 μ →ₗ[ℂ] ℂ) :
    let := convolutionRing μ
    χ ∈ _root_.Specs.ExpandedFA.BanachAlgebra.Conventions.CharacterSpaceValue ℂ (L1 μ) ↔
      _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.IsCharacter μ χ := by
  rfl

theorem translation_properties : _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.TranslationProperties μ :=
  ⟨translate_ae μ, translate_one μ, translate_mul μ, continuous_translate μ⟩

theorem convolution_basic_properties :
    _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.ConvolutionBasicProperties μ :=
  ⟨inferInstance, convolution_integrable μ, convolution_norm_le μ, convolution_assoc μ,
    convolution_add_left μ, convolution_add_right μ,
    fun f => ⟨convolution_zero_left μ f, convolution_zero_right μ f⟩,
    fun c f g => ⟨convolution_smul_left μ c f g, convolution_smul_right μ c f g⟩⟩

end HaarTranslations

section CompactSeries
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

set_option maxHeartbeats 1200000

/-- Native L¹ approximation by a continuous compactly supported representative. -/
lemma exists_compact_approximation_L1 (f : L1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : L1 μ) (φ : G → ℂ), Continuous φ ∧ HasCompactSupport φ ∧
      a =ᵐ[μ] φ ∧ dist f a ≤ ε := by
  obtain ⟨φ, hφc, hφerr, hφ, hφmem⟩ := exists_compact_continuous_approximation
    ENNReal.one_ne_top (Lp.memLp f) (ENNReal.ofReal_ne_zero_iff.mpr hε)
  refine ⟨hφmem.toLp φ, φ, hφ, hφc, hφmem.coeFn_toLp, ?_⟩
  rw [Lp.dist_def, eLpNorm_congr_ae ((Filter.EventuallyEq.rfl : (⇑f : G → ℂ) =ᵐ[μ] ⇑f).sub hφmem.coeFn_toLp)]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hφerr).trans_eq (ENNReal.toReal_ofReal hε.le)

/-- Every L¹ vector is an absolutely summable series of vectors with
continuous compactly supported representatives. -/
lemma exists_compact_series (f : L1 μ) :
    ∃ (F : ℕ → L1 μ) (φ : ℕ → G → ℂ),
      (∀ n, Continuous (φ n) ∧ HasCompactSupport (φ n) ∧ F n =ᵐ[μ] φ n) ∧
      Summable (fun n => ‖F n‖) ∧ HasSum F f := by
  let e : ℕ → ℝ := fun n => (1/2 : ℝ)^n
  have he : ∀ n, 0 < e n := fun n => pow_pos (by norm_num) _
  choose a φ hφ hφc harep ha using fun n => exists_compact_approximation_L1 μ f (he n)
  let F : ℕ → L1 μ := fun n => match n with
    | 0 => a 0
    | n+1 => a (n+1) - a n
  let ψ : ℕ → G → ℂ := fun n => match n with
    | 0 => φ 0
    | n+1 => φ (n+1) - φ n
  have hFrep (n : ℕ) : F n =ᵐ[μ] ψ n := by
    cases n with
    | zero => exact harep 0
    | succ n => exact (Lp.coeFn_sub _ _).trans ((harep _).sub (harep _))
  have hFbound (n : ℕ) : ‖F (n+1)‖ ≤ e (n+1) + e n := by
    change ‖a (n+1) - a n‖ ≤ _
    rw [← dist_eq_norm]
    exact (dist_triangle (a (n+1)) f (a n)).trans (add_le_add (by simpa [dist_comm] using ha (n+1)) (ha n))
  have heS : Summable e := summable_geometric_of_abs_lt_one (by norm_num)
  have hFs : Summable (fun n => ‖F n‖) := by
    apply (summable_nat_add_iff 1).mp
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      hFbound ((heS.comp_injective (fun a b h => Nat.add_right_cancel h)).add heS)
  have halim : Tendsto a atTop (𝓝 f) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have helim : Tendsto e atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact squeeze_zero (fun n => dist_nonneg) (fun n => by simpa [dist_comm] using ha n) helim
  refine ⟨F, ψ, ?_, hFs, ?_⟩
  · intro n
    cases n with
    | zero => exact ⟨hφ 0, hφc 0, hFrep 0⟩
    | succ n => exact ⟨(hφ _).sub (hφ _), (hφc _).sub (hφc _), hFrep (n+1)⟩
  · apply (hasSum_iff_tendsto_nat_of_summable_norm hFs).mpr
    have htel (n : ℕ) : ∑ k ∈ Finset.range (n+1), F k = a n := by
      induction n with
      | zero => simp [F]
      | succ n ih => rw [Finset.sum_range_succ, ih]; simp [F]
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [htel] using halim


end CompactSeries

section KernelEvaluation
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def setIntegralL1 (ν : Measure Y) (s : Set Y) : Lp ℂ 1 ν →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ (μ := ν.restrict s)).comp (LpToLpRestrictCLM Y ℂ ℂ ν 1 s)

lemma setIntegralL1_apply (ν : Measure Y) (s : Set Y) (f : Lp ℂ 1 ν) :
    setIntegralL1 ν s f = ∫ y in s, f y ∂ν := by
  change L1.integralCLM' ℂ _ = _
  rw [← L1.integral_eq', L1.integral_eq_integral]
  exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℂ s f)

lemma integral_L1_kernel (μ : Measure X) (ν : Measure Y)
    {U : Set X} {V : Set Y} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hμU : μ U < ∞) (hνV : ν V < ∞) {k : X × Y → ℂ}
    (hk : StronglyMeasurable k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)
    (hkU : ∀ x y, x ∉ U → k (x,y) = 0)
    (hkV : ∀ x y, y ∉ V → k (x,y) = 0)
    {v : X → Lp ℂ 1 ν} (hv : Integrable v μ)
    (hvrep : ∀ᵐ x ∂μ, v x =ᵐ[ν] fun y => k (x,y)) :
    (∀ y, Integrable (fun x => k (x,y)) μ) ∧
    Integrable (fun y => ∫ x, k (x,y) ∂μ) ν ∧
    (∫ x, v x ∂μ) =ᵐ[ν] fun y => ∫ x, k (x,y) ∂μ := by
  letI : Fact (μ U < ∞) := ⟨hμU⟩
  letI : Fact (ν V < ∞) := ⟨hνV⟩
  have hset (y : Y) : ∫ x in U, k (x,y) ∂μ = ∫ x, k (x,y) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hkU x y hx)
  have hki : Integrable k ((μ.restrict U).prod (ν.restrict V)) :=
    ⟨hk.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C) (.of_forall hC)⟩
  have hsec (y : Y) : Integrable (fun x => k (x,y)) μ := by
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp
      (show Integrable (fun x => k (x,y)) (μ.restrict U) from
        ⟨(hk.comp_measurable measurable_prodMk_right).aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (C := C) (.of_forall fun x => hC (x,y))⟩)
    intro x hx
    by_contra hn
    exact hx (hkU x y hn)
  have hhi : Integrable (fun y => ∫ x, k (x,y) ∂μ) ν := by
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    · change Integrable (fun y => ∫ x, k (x,y) ∂μ) (ν.restrict V)
      simpa only [hset] using hki.integral_prod_right
    · intro y hy
      by_contra hn
      apply hy
      simp [hkV, hn]
  refine ⟨hsec, hhi, ?_⟩
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L1.integrable_coeFn _) hhi
  intro s hs hνs
  letI : Fact (ν s < ∞) := ⟨hνs⟩
  have hkis : Integrable k ((μ.restrict U).prod (ν.restrict s)) :=
    ⟨hk.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C) (.of_forall hC)⟩
  calc
    ∫ y in s, (∫ x, v x ∂μ) y ∂ν = setIntegralL1 ν s (∫ x, v x ∂μ) :=
      (setIntegralL1_apply ν s _).symm
    _ = ∫ x, setIntegralL1 ν s (v x) ∂μ :=
      ((setIntegralL1 ν s).integral_comp_comm hv).symm
    _ = ∫ x, ∫ y in s, k (x,y) ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [hvrep] with x hx
      exact (setIntegralL1_apply ν s _).trans
        (integral_congr_ae (ae_restrict_of_ae hx))
    _ = ∫ x in U, ∫ y in s, k (x,y) ∂ν ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp [hkU, hx]
    _ = ∫ y in s, ∫ x in U, k (x,y) ∂μ ∂ν := integral_integral_swap hkis
    _ = ∫ y in s, ∫ x, k (x,y) ∂μ ∂ν := by simp only [hset]
end KernelEvaluation

section KernelEvaluation
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y] [MeasurableSpace X] [MeasurableSpace Y]
  [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
lemma integral_L1_compact_kernel (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {k : X × Y → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k)
    {v : X → Lp ℂ 1 ν} (hv : Integrable v μ)
    (hvrep : ∀ᵐ x ∂μ, v x =ᵐ[ν] fun y => k (x,y)) :
    (∀ y, Integrable (fun x => k (x,y)) μ) ∧
    Integrable (fun y => ∫ x, k (x,y) ∂μ) ν ∧
    (∫ x, v x ∂μ) =ᵐ[ν] fun y => ∫ x, k (x,y) ∂μ := by
  let U := Prod.fst '' (tsupport k)
  let V := Prod.snd '' (tsupport k)
  have hU : IsCompact U := hkc.image continuous_fst
  have hV : IsCompact V := hkc.image continuous_snd
  obtain ⟨C,hC⟩ := hk.bounded_above_of_compact_support hkc
  apply integral_L1_kernel μ ν hU.measurableSet hV.measurableSet
    hU.measure_lt_top hV.measure_lt_top (hkc.stronglyMeasurable_of_prod hk) hC
    ?_ ?_ hv hvrep
  · intro x y hx
    by_contra hn
    exact hx (Set.mem_image_of_mem _ (subset_tsupport k hn))
  · intro x y hy
    by_contra hn
    exact hy (Set.mem_image_of_mem _ (subset_tsupport k hn))
end KernelEvaluation

section KernelEvaluation
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

lemma convolution_kernel_hasCompactSupport {f g : G → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (fun z : G × G => f z.1 * g (z.1⁻¹ * z.2)) := by
  let K := (fun p : G × G => (p.1, p.1 * p.2)) '' (tsupport f ×ˢ tsupport g)
  have hK : IsCompact K := (hf.prod hg).image
    (continuous_fst.prodMk (continuous_fst.mul continuous_snd))
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz

  refine ⟨(z.1, z.1⁻¹ * z.2), ⟨?_, ?_⟩, ?_⟩
  · exact subset_tsupport f (mul_ne_zero_iff.mp hz).1
  · exact subset_tsupport g (mul_ne_zero_iff.mp hz).2
  · simp

lemma convolution_ae_of_continuous_compact {f g : G → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    convolution μ ((hf.integrable_of_hasCompactSupport hfc).toL1 f)
      ((hg.integrable_of_hasCompactSupport hgc).toL1 g) =ᵐ[μ]
        fun t => ∫ x, f x * g (x⁻¹ * t) ∂μ := by
  let fi := hf.integrable_of_hasCompactSupport hfc (μ := μ)
  let gi := hg.integrable_of_hasCompactSupport hgc (μ := μ)
  let f1 := fi.toL1 f
  let g1 := gi.toL1 g
  have hkernel : Continuous (fun z : G × G => f z.1 * g (z.1⁻¹ * z.2)) :=
    (hf.comp continuous_fst).mul (hg.comp (continuous_fst.inv.mul continuous_snd))
  apply (integral_L1_compact_kernel μ μ hkernel
    (convolution_kernel_hasCompactSupport hfc hgc) (convolution_integrable μ f1 g1) ?_).2.2
  filter_upwards [fi.coeFn_toL1] with x hx
  have hg1 : translate μ x g1 =ᵐ[μ] fun t => g (x⁻¹ * t) :=
    (translate_ae μ x g1).trans
      (gi.coeFn_toL1.comp_tendsto (measurePreserving_mul_left μ x⁻¹).quasiMeasurePreserving.tendsto_ae)
  filter_upwards [Lp.coeFn_smul (f1 x) (translate μ x g1), hg1] with t ht hgt
  rw [ht, Pi.smul_apply, smul_eq_mul, hx, hgt]

lemma integrable_convolution_of_continuous_compact {f g : G → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (t : G) :
    Integrable (fun x => f x * g (x⁻¹ * t)) μ := by
  have hc : Continuous (fun x => f x * g (x⁻¹ * t)) :=
    hf.mul (hg.comp (continuous_inv.mul_const t))
  apply hc.integrable_of_hasCompactSupport
  exact hfc.mul_right
end KernelEvaluation

section CompactLeftConvolution
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

lemma scalar_convolution_integrable_of_bounded_left {f g : G → ℂ}
    (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (hg : Integrable g μ) (t : G) :
    Integrable (fun x => f x * g (x⁻¹ * t)) μ := by
  have hgt : Integrable (fun x => g (x⁻¹ * t)) μ := by
    simpa only [mul_comm] using (hg.comp_mul_left t).comp_inv
  exact hgt.bdd_mul hf (.of_forall hC)

lemma scalar_convolution_norm_le_of_bounded_left {f g : G → ℂ}
    (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (hg : Integrable g μ) (t : G) :
    ‖∫ x, f x * g (x⁻¹ * t) ∂μ‖ ≤ C * ∫ x, ‖g x‖ ∂μ := by
  calc
    _ ≤ ∫ x, ‖f x * g (x⁻¹ * t)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C * ‖g (x⁻¹ * t)‖ ∂μ := by
      apply integral_mono_of_nonneg
      · exact .of_forall (fun _ => norm_nonneg _)
      · simpa only [mul_comm] using (((hg.norm.comp_mul_left t).comp_inv).const_mul C)
      · exact .of_forall fun x => by dsimp only; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
    _ = C * ∫ x, ‖g x‖ ∂μ := by
      rw [integral_const_mul]
      congr 1
      simpa only [mul_comm] using (integral_inv_eq_self (fun x => ‖g (t * x)‖) μ).trans (integral_mul_left_eq_self (fun x => ‖g x‖) t)





def scalarConvolutionLeftLinear {φ : G → ℂ} (hφ : AEStronglyMeasurable φ μ)
    {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (t : G) : L1 μ →L[ℂ] ℂ :=
  ({ toFun := fun g => ∫ x, φ x * g (x⁻¹ * t) ∂μ
     map_add' := by
       intro g h
       have ha := (Measure.measurePreserving_div_left μ t).quasiMeasurePreserving.ae (Lp.coeFn_add g h)
       have ha' : ∀ᵐ x ∂μ, (g + h) (x⁻¹ * t) = g (x⁻¹ * t) + h (x⁻¹ * t) := by
         simpa only [div_eq_mul_inv, mul_comm, Pi.add_apply] using ha
       rw [integral_congr_ae (ha'.mono fun x hx => congrArg (φ x * ·) hx)]
       simp_rw [mul_add]
       exact integral_add
         (scalar_convolution_integrable_of_bounded_left μ hφ hC (L1.integrable_coeFn g) t)
         (scalar_convolution_integrable_of_bounded_left μ hφ hC (L1.integrable_coeFn h) t)
     map_smul' := by
       intro c g
       have ha := (Measure.measurePreserving_div_left μ t).quasiMeasurePreserving.ae (Lp.coeFn_smul c g)
       have ha' : ∀ᵐ x ∂μ, (c • g) (x⁻¹ * t) = c * g (x⁻¹ * t) := by
         simpa only [div_eq_mul_inv, mul_comm, Pi.smul_apply, smul_eq_mul] using ha
       rw [integral_congr_ae (ha'.mono fun x hx => congrArg (φ x * ·) hx)]
       simp only [mul_left_comm (φ _), integral_const_mul, RingHom.id_apply, smul_eq_mul] } : L1 μ →ₗ[ℂ] ℂ).mkContinuous C
    (fun g => by
      change ‖∫ x, φ x * g (x⁻¹ * t) ∂μ‖ ≤ C * ‖g‖
      rw [L1.norm_eq_integral_norm]
      exact scalar_convolution_norm_le_of_bounded_left μ hφ hC (L1.integrable_coeFn g) t)

@[simp] lemma scalarConvolutionLeftLinear_apply {φ : G → ℂ}
    (hφ : AEStronglyMeasurable φ μ) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (t : G) (g : L1 μ) :
    scalarConvolutionLeftLinear μ hφ hC t g = ∫ x, φ x * g (x⁻¹ * t) ∂μ := rfl


lemma convolution_ae_of_compact_left {φ : G → ℂ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (g : L1 μ) :
    convolution μ ((hφ.integrable_of_hasCompactSupport hφc).toL1 φ) g =ᵐ[μ]
      fun t => ∫ x, φ x * g (x⁻¹ * t) ∂μ := by
  let f1 : L1 μ := (hφ.integrable_of_hasCompactSupport hφc).toL1 φ
  let e : ℕ → ℝ := fun n => (1 / 2 : ℝ)^n
  have he : ∀ n, 0 < e n := fun n => pow_pos (by norm_num) _
  choose a ψ hψ hψc harep ha using fun n => exists_compact_approximation_L1 μ g (he n)
  have halim : Tendsto a atTop (𝓝 g) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have helim : Tendsto e atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact squeeze_zero (fun n => dist_nonneg)
      (fun n => by simpa [dist_comm] using ha n) helim
  have hBlim : Tendsto (fun n => convolution μ f1 (a n)) atTop (𝓝 (convolution μ f1 g)) :=
    (convolutionRightLinear μ f1).continuous.tendsto g |>.comp halim
  obtain ⟨ns, hns, hBlimae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hBlim).exists_seq_tendsto_ae
  obtain ⟨C, hC⟩ := (hφc.isCompact_range hφ).isBounded.exists_norm_le
  have hC' : ∀ x, ‖φ x‖ ≤ C := fun x => hC _ (Set.mem_range_self x)
  let S : G → L1 μ →L[ℂ] ℂ := scalarConvolutionLeftLinear μ hφ.aestronglyMeasurable hC'
  have hSlim (t : G) : Tendsto (fun n => S t (a n)) atTop (𝓝 (S t g)) :=
    (S t).continuous.tendsto g |>.comp halim
  have heq (n : ℕ) : convolution μ f1 (a n) =ᵐ[μ] fun t => S t (a n) := by
    have haeq : a n = ((hψ n).integrable_of_hasCompactSupport (hψc n)).toL1 (ψ n) := by
      apply Lp.ext
      exact (harep n).trans (((hψ n).integrable_of_hasCompactSupport (hψc n)).coeFn_toL1.symm)
    have hcc := convolution_ae_of_continuous_compact μ hφ hφc (hψ n) (hψc n)
    rw [← haeq] at hcc
    filter_upwards [hcc] with t ht
    change convolution μ f1 (a n) t = ∫ x, φ x * a n (x⁻¹ * t) ∂μ
    rw [ht]
    apply integral_congr_ae
    have hrept := (Measure.measurePreserving_div_left μ t).quasiMeasurePreserving.ae (harep n)
    filter_upwards [hrept] with x hx
    have hx' : a n (x⁻¹ * t) = ψ n (x⁻¹ * t) := by
      simpa only [div_eq_mul_inv, mul_comm] using hx
    rw [hx']
  filter_upwards [hBlimae, ae_all_iff.mpr heq] with t ht hteq
  have hs : Tendsto (fun n => convolution μ f1 (a (ns n)) t) atTop (𝓝 (S t g)) := by
    convert (hSlim t).comp hns.tendsto_atTop using 1
    funext n
    exact hteq (ns n)
  exact tendsto_nhds_unique ht hs


lemma convolution_ae_of_compact_left_rep {φ : G → ℂ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (F g : L1 μ) (hF : F =ᵐ[μ] φ) :
    convolution μ F g =ᵐ[μ] fun t => ∫ x, φ x * g (x⁻¹ * t) ∂μ := by
  have hF' : F = (hφ.integrable_of_hasCompactSupport hφc).toL1 φ :=
    Lp.ext (hF.trans (hφ.integrable_of_hasCompactSupport hφc).coeFn_toL1.symm)
  rw [hF']
  exact convolution_ae_of_compact_left μ hφ hφc g

lemma compact_left_absolute_kernel {φ : G → ℂ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (F g : L1 μ) (hF : F =ᵐ[μ] φ) :
    Integrable (fun t => ∫ x, ‖φ x * g (x⁻¹ * t)‖ ∂μ) μ ∧
    (∫ t, ‖∫ x, ‖φ x * g (x⁻¹ * t)‖ ∂μ‖ ∂μ) ≤ ‖F‖ * ‖g‖ := by
  let φA : G → ℂ := fun x => (‖φ x‖ : ℂ)
  have hφA : Continuous φA := Complex.continuous_ofReal.comp hφ.norm
  have hφAc : HasCompactSupport φA := hφc.norm.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  let fiA := hφA.integrable_of_hasCompactSupport hφAc (μ := μ)
  let giA : Integrable (fun x => (‖g x‖ : ℂ)) μ := (L1.integrable_coeFn g).norm.ofReal
  let FA : L1 μ := fiA.toL1 φA
  let gA : L1 μ := giA.toL1 (fun x => (‖g x‖ : ℂ))
  let B : L1 μ := convolution μ FA gA
  let K : G → ℝ := fun t => ∫ x, ‖φ x * g (x⁻¹ * t)‖ ∂μ
  have hBA : B =ᵐ[μ] fun t => (K t : ℂ) := by
    have hbridge := convolution_ae_of_compact_left μ hφA hφAc gA
    filter_upwards [hbridge] with t ht
    rw [ht]
    calc
      _ = ∫ x, ((‖φ x‖ * ‖g (x⁻¹ * t)‖ : ℝ) : ℂ) ∂μ := by
        apply integral_congr_ae
        have hrept := (Measure.measurePreserving_div_left μ t).quasiMeasurePreserving.ae giA.coeFn_toL1
        filter_upwards [hrept] with x hx
        have hx' : gA (x⁻¹ * t) = (‖g (x⁻¹ * t)‖ : ℂ) := by
          simpa only [div_eq_mul_inv, mul_comm] using hx
        simp only [φA, hx', Complex.ofReal_mul]
      _ = (K t : ℂ) := by
        simp only [K, norm_mul, integral_complex_ofReal]
  have hK : Integrable K μ := by
    apply (L1.integrable_coeFn B).re.congr
    filter_upwards [hBA] with t ht
    simp only [ht, Complex.ofReal_re, RCLike.re_to_complex]
  have hFAnorm : ‖FA‖ = ‖F‖ := by
    rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [fiA.coeFn_toL1, hF] with x hx hFx
    simp only [FA, hx, φA, hFx, Complex.norm_real, norm_norm]
  have hgAnorm : ‖gA‖ = ‖g‖ := by
    rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [giA.coeFn_toL1] with x hx
    simp only [gA, hx, Complex.norm_real, norm_norm]
  refine ⟨hK, ?_⟩
  calc
    (∫ t, ‖K t‖ ∂μ) = ‖B‖ := by
      rw [L1.norm_eq_integral_norm]
      apply integral_congr_ae
      filter_upwards [hBA] with t ht
      simp only [ht, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖FA‖ * ‖gA‖ := convolution_norm_le μ FA gA
    _ = ‖F‖ * ‖g‖ := by rw [hFAnorm, hgAnorm]


end CompactLeftConvolution

section SumIntegrability
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma integrable_of_hasSum_of_summable_integral_norm {F : ℕ → X → ℂ} {f : X → ℂ}
    (hF : ∀ n, Integrable (F n) ν)
    (hS : Summable fun n => ∫ x, ‖F n x‖ ∂ν)
    (hlim : ∀ᵐ x ∂ν, HasSum (fun n => F n x) (f x)) : Integrable f ν := by
  let u : ℕ → Lp ℂ 1 ν := fun n => (hF n).toL1 (F n)
  have hu (n : ℕ) : ‖u n‖ = ∫ x, ‖F n x‖ ∂ν := by
    rw [integral_norm_eq_lintegral_enorm (hF n).aestronglyMeasurable]
    exact Integrable.norm_toL1_eq_lintegral_enorm _ _
  have hsu : ∑' n, ‖u n‖ₑ ≠ ∞ := by
    apply tsum_enorm_ne_top_iff_summable_norm.mpr
    simpa only [hu] using hS
  have hreps : ∀ᵐ x ∂ν, ∀ n, u n x = F n x :=
    ae_all_iff.mpr fun n => (hF n).coeFn_toL1
  have hseries := Lp.hasSum_coeFn_tsum hsu
  apply (L1.integrable_coeFn (∑' n, u n)).congr
  filter_upwards [hseries, hreps, hlim] with x hx hxrep hxf
  exact (by simpa only [hxrep] using hx : HasSum (fun n => F n x) ((∑' n, u n) x)).unique hxf

end SumIntegrability

section AeSummability
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
lemma ae_summable_norm_of_summable_integral_norm {F : ℕ → X → ℝ}
    (hF : ∀ n, Integrable (F n) ν)
    (hS : Summable fun n => ∫ x, ‖F n x‖ ∂ν) :
    ∀ᵐ x ∂ν, Summable (fun n => ‖F n x‖) := by
  apply summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl
  let u : ℕ → Lp ℝ 1 ν := fun n => (hF n).toL1 (F n)
  have hu (n : ℕ) : ‖u n‖ = ∫ x, ‖F n x‖ ∂ν := L1.norm_of_fun_eq_integral_norm _
  have hsu : ∑' n, ‖u n‖ₑ ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr (by simpa only [hu] using hS)
  convert hsu using 1
  congr 1
  funext n
  change eLpNorm (F n) 1 ν = ‖(hF n).toL1 (F n)‖ₑ
  rw [Integrable.enorm_toL1, eLpNorm_one_eq_lintegral_enorm (hF n).aestronglyMeasurable]
end AeSummability

section ConvolutionSeries
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

lemma convolution_series_extension
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ)
    (f : Lp ℂ 1 μ) (g : G → ℂ) (hg : Integrable g μ)
    (F : ℕ → Lp ℂ 1 μ) (φ : ℕ → G → ℂ)
    (hφm : ∀ n, AEStronglyMeasurable (φ n) μ)
    (hφb : ∀ n, ∃ C : ℝ, ∀ x, ‖φ n x‖ ≤ C)
    (hFφ : ∀ n, F n =ᵐ[μ] φ n)
    (hFsum : Summable fun n => ‖F n‖) (hFlim : HasSum F f)
    (hTφ : ∀ n, T (F n) =ᵐ[μ] fun t => ∫ x, φ n x * g (x⁻¹ * t) ∂μ)
    (hKint : ∀ n, Integrable (fun t => ∫ x, ‖φ n x * g (x⁻¹ * t)‖ ∂μ) μ)
    (C : ℝ) (hKbound : ∀ n,
      (∫ t, ‖∫ x, ‖φ n x * g (x⁻¹ * t)‖ ∂μ‖ ∂μ) ≤ ‖F n‖ * C) :
    (∀ᵐ t ∂μ, Integrable (fun x => f x * g (x⁻¹ * t)) μ) ∧
    (T f =ᵐ[μ] fun t => ∫ x, f x * g (x⁻¹ * t) ∂μ) := by
  have hFtop : ∑' n, ‖F n‖ₑ ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hFsum
  have hpointF : ∀ᵐ x ∂μ, HasSum (fun n => φ n x) (f x) := by
    have hrep : ∀ᵐ x ∂μ, ∀ n, F n x = φ n x := ae_all_iff.mpr hFφ
    filter_upwards [Lp.hasSum_coeFn_tsum hFtop, hrep] with x hx hxrep
    simpa only [hFlim.tsum_eq, hxrep] using hx
  have hTsum : Summable fun n => ‖T (F n)‖ := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => T.le_opNorm (F n))
    simpa only [mul_comm] using hFsum.mul_right ‖T‖
  have hpointT : ∀ᵐ t ∂μ, HasSum (fun n => T (F n) t) (T f t) := by
    have htop : ∑' n, ‖T (F n)‖ₑ ≠ ∞ :=
      tsum_enorm_ne_top_iff_summable_norm.mpr hTsum
    simpa only [(T.hasSum hFlim).tsum_eq] using Lp.hasSum_coeFn_tsum htop
  have hKS : Summable fun n => ∫ t, ‖∫ x, ‖φ n x * g (x⁻¹ * t)‖ ∂μ‖ ∂μ := by
    exact Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      hKbound (hFsum.mul_right C)
  have hpointK : ∀ᵐ t ∂μ, Summable (fun n => ∫ x, ‖φ n x * g (x⁻¹ * t)‖ ∂μ) := by
    have haux := ae_summable_norm_of_summable_integral_norm hKint hKS
    simpa only [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] using haux
  have hrepT : ∀ᵐ t ∂μ, ∀ n, T (F n) t = ∫ x, φ n x * g (x⁻¹ * t) ∂μ :=
    ae_all_iff.mpr hTφ
  have hfull : ∀ᵐ t ∂μ, Integrable (fun x => f x * g (x⁻¹ * t)) μ ∧
      T f t = ∫ x, f x * g (x⁻¹ * t) ∂μ := by
    filter_upwards [hpointK, hpointT, hrepT] with t htK htT htRep
    have hseries : ∀ᵐ x ∂μ,
        HasSum (fun n => φ n x * g (x⁻¹ * t)) (f x * g (x⁻¹ * t)) :=
      hpointF.mono fun x hx => hx.mul_right _
    have hkernel (n : ℕ) : Integrable (fun x => φ n x * g (x⁻¹ * t)) μ := by
      obtain ⟨D, hD⟩ := hφb n
      exact scalar_convolution_integrable_of_bounded_left μ (hφm n) hD hg t
    refine ⟨integrable_of_hasSum_of_summable_integral_norm hkernel htK hseries, ?_⟩
    have hintegrals := hasSum_integral_of_summable_integral_norm hkernel htK
    have heq : (fun x => ∑' n, φ n x * g (x⁻¹ * t)) =ᵐ[μ]
        (fun x => f x * g (x⁻¹ * t)) := hseries.mono fun _ hx => hx.tsum_eq
    rw [integral_congr_ae heq] at hintegrals
    apply HasSum.unique _ hintegrals
    simpa only [htRep] using htT
  exact ⟨hfull.mono fun _ hx => hx.1, hfull.mono fun _ hx => hx.2⟩
end ConvolutionSeries

section PointwiseConvolution
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- The Bochner convolution agrees almost everywhere with the scalar Haar
integral, whose integrability is proved in the original non-sigma-finite setting. -/
lemma convolution_pointwise (f g : L1 μ) :
    (∀ᵐ t ∂μ, Integrable (fun x => f x * g (x⁻¹ * t)) μ) ∧
    (convolution μ f g =ᵐ[μ] fun t => ∫ x, f x * g (x⁻¹ * t) ∂μ) := by
  obtain ⟨F, φ, hφ, hFsum, hFlim⟩ := exists_compact_series μ f
  apply convolution_series_extension μ (convolutionLeftLinear μ g) f g
    (L1.integrable_coeFn g) F φ
    (fun n => (hφ n).1.aestronglyMeasurable) ?_
    (fun n => (hφ n).2.2) hFsum hFlim ?_
    (fun n => (compact_left_absolute_kernel μ (hφ n).1 (hφ n).2.1 (F n) g (hφ n).2.2).1)
    ‖g‖ (fun n => (compact_left_absolute_kernel μ (hφ n).1 (hφ n).2.1 (F n) g (hφ n).2.2).2)
  · intro n
    obtain ⟨C, hC⟩ := ((hφ n).2.1.isCompact_range (hφ n).1).isBounded.exists_norm_le
    exact ⟨C, fun x => hC _ (Set.mem_range_self x)⟩
  · intro n
    exact convolution_ae_of_compact_left_rep μ (hφ n).1 (hφ n).2.1 (F n) g (hφ n).2.2

/-- Haar inversion and translation exchange the two scalar factors. -/
theorem scalar_convolution_comm (f g : G → ℂ) (t : G) :
    (∫ x, f x * g (x⁻¹ * t) ∂μ) = ∫ x, g x * f (x⁻¹ * t) ∂μ := by
  rw [← integral_div_left_eq_self (fun x => f x * g (x⁻¹ * t)) μ t]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp [div_eq_mul_inv, mul_comm]

theorem convolution_comm (f g : L1 μ) : convolution μ f g = convolution μ g f := by
  apply Lp.ext
  filter_upwards [(convolution_pointwise μ f g).2, (convolution_pointwise μ g f).2] with t hf hg
  rw [hf, hg, scalar_convolution_comm μ]

/-- The commutative Banach-algebra multiplication on the original native L¹. -/
abbrev convolutionCommRing : NonUnitalNormedCommRing (L1 μ) :=
  { convolutionRing μ with mul_comm := convolution_comm μ }

theorem convolution_properties :
    _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.ConvolutionAlgebra μ :=
  ⟨inferInstance, convolution_integrable μ,
    fun f g => (convolution_pointwise μ f g).1,
    fun f g => (convolution_pointwise μ f g).2,
    convolution_norm_le μ, convolution_assoc μ, convolution_comm μ,
    convolution_add_left μ, convolution_add_right μ,
    fun f => ⟨convolution_zero_left μ f, convolution_zero_right μ f⟩,
    fun c f g => ⟨convolution_smul_left μ c f g, convolution_smul_right μ c f g⟩⟩

end PointwiseConvolution

section FourierEvaluation
variable (μ : Measure G)

abbrev fourierValue : _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.FourierType μ :=
  _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.fourierValue μ

theorem fourier_integrable (γ : G →ₜ* Circle) (f : L1 μ) :
    Integrable (fun x => f x * star (Circle.coeHom (γ x))) μ := by
  apply (L1.integrable_coeFn f).mul_bdd (c := 1)
    ((continuous_subtype_val.comp γ.continuous).star.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by simp

theorem fourier_norm_le (γ : G →ₜ* Circle) (f : L1 μ) :
    ‖fourierValue μ γ f‖ ≤ ‖f‖ := by
  calc
    ‖fourierValue μ γ f‖ ≤ ∫ x, ‖f x * star (Circle.coeHom (γ x))‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ ∂μ := by simp
    _ = ‖f‖ := by
      rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
      exact (MeasureTheory.L1.norm_def f).symm

/-- The scalar integral on native a.e. classes is complex-linear. -/
def fourierLinearMap (γ : G →ₜ* Circle) : L1 μ →ₗ[ℂ] ℂ where
  toFun := fourierValue μ γ
  map_add' f g := by
    change (∫ x, (f + g) x * star (Circle.coeHom (γ x)) ∂μ) = _
    have heq : (fun x => (f + g) x * star (Circle.coeHom (γ x))) =ᵐ[μ]
        (fun x => (f x + g x) * star (Circle.coeHom (γ x))) := by
      filter_upwards [Lp.coeFn_add f g] with x hx
      simpa only [Pi.add_apply] using congrArg (fun z : ℂ => z * star (Circle.coeHom (γ x))) hx
    rw [integral_congr_ae heq]
    simp only [add_mul]
    exact integral_add (fourier_integrable μ γ f) (fourier_integrable μ γ g)
  map_smul' c f := by
    change (∫ x, (c • f) x * star (Circle.coeHom (γ x)) ∂μ) = _
    have heq : (fun x => (c • f) x * star (Circle.coeHom (γ x))) =ᵐ[μ]
        (fun x => (c * f x) * star (Circle.coeHom (γ x))) := by
      filter_upwards [Lp.coeFn_smul c f] with x hx
      simp only [hx, Pi.smul_apply, smul_eq_mul]
    rw [integral_congr_ae heq]
    simp only [smul_eq_mul, mul_assoc, integral_const_mul, RingHom.id_apply]
    rfl

/-- Fourier evaluation is a contraction, on any positive Borel measure. -/
def fourierLinear (γ : G →ₜ* Circle) : L1 μ →L[ℂ] ℂ :=
  (fourierLinearMap μ γ).mkContinuous 1 (fun f => by
    simpa only [one_mul, fourierLinearMap, LinearMap.coe_mk, AddHom.coe_mk] using fourier_norm_le μ γ f)

@[simp] theorem fourierLinear_apply (γ : G →ₜ* Circle) (f : L1 μ) :
    fourierLinear μ γ f = fourierValue μ γ f := rfl

theorem norm_fourierLinear_le (γ : G →ₜ* Circle) : ‖fourierLinear μ γ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul, fourierLinear_apply] using fourier_norm_le μ γ f

section Invariant
variable [μ.IsMulLeftInvariant]

/-- Fourier evaluation transforms a left translation by the conjugate
character value; the sign matches the manuscript's convention. -/
theorem fourier_translate (γ : G →ₜ* Circle) (x : G) (f : L1 μ) :
    fourierValue μ γ (translate μ x f) = star (Circle.coeHom (γ x)) * fourierValue μ γ f := by
  change (∫ t, (translate μ x f) t * star (Circle.coeHom (γ t)) ∂μ) = _
  have heq : (fun t => (translate μ x f) t * star (Circle.coeHom (γ t))) =ᵐ[μ]
      (fun t => f (x⁻¹ * t) * star (Circle.coeHom (γ t))) := by
    filter_upwards [translate_ae μ x f] with t ht
    rw [ht]
  rw [integral_congr_ae heq]
  rw [← integral_mul_left_eq_self (fun t => f (x⁻¹ * t) * star (Circle.coeHom (γ t))) x]
  simp only [inv_mul_cancel_left, map_mul, star_mul]
  simp only [← mul_assoc, integral_mul_const]
  exact mul_comm _ _

end Invariant

section Haar
variable [μ.IsHaarMeasure] [μ.Regular]

/-- Multiplicativity uses only Bochner integrability and translation, and
therefore does not appeal to a σ-finite product measure. -/
theorem fourier_convolution (γ : G →ₜ* Circle) (f g : L1 μ) :
    fourierValue μ γ (convolution μ f g) = fourierValue μ γ f * fourierValue μ γ g := by
  change fourierLinear μ γ (∫ x, f x • translate μ x g ∂μ) = _
  rw [← (fourierLinear μ γ).integral_comp_comm (convolution_integrable μ f g)]
  simp only [map_smul, fourierLinear_apply, smul_eq_mul, fourier_translate,
    ← mul_assoc, integral_mul_const]
  rfl

/-- A finite positive-measure compact test realizes equality in the Fourier
norm estimate. Its phase is γ, cancelling the conjugate in the transform. -/
theorem exists_fourier_norm_attaining (γ : G →ₜ* Circle) :
    ∃ f : L1 μ, 0 < ‖f‖ ∧ fourierValue μ γ f = (‖f‖ : ℂ) := by
  let K : TopologicalSpace.PositiveCompacts G := Classical.choice inferInstance
  have hK : MeasurableSet (K : Set G) := K.isCompact.measurableSet
  have hKpos : 0 < μ.real (K : Set G) :=
    ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
      K.isCompact.measure_ne_top
  let v : G → ℂ := (K : Set G).indicator (fun x => (Circle.coeHom (γ x)))
  have hi : Integrable v μ := by
    apply (integrable_indicator_iff hK).mpr
    apply ContinuousOn.integrableOn_compact K.isCompact
    exact (continuous_subtype_val.comp γ.continuous).continuousOn
  let f : L1 μ := hi.toL1 v
  have hfnorm : ‖f‖ = μ.real (K : Set G) := by
    rw [L1.norm_of_fun_eq_integral_norm hi]
    have heq : (fun x => ‖v x‖) = (K : Set G).indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ (K : Set G) <;> simp [v, hx]
    rw [heq, integral_indicator_const 1 hK]
    simp
  refine ⟨f, hfnorm ▸ hKpos, ?_⟩
  change (∫ x, f x * star (Circle.coeHom (γ x)) ∂μ) = _
  have heq : (fun x => f x * star (Circle.coeHom (γ x))) =ᵐ[μ]
      (K : Set G).indicator (fun _ => (1 : ℂ)) := by
    filter_upwards [hi.coeFn_toL1] with x hx
    rw [hx]
    by_cases hxK : x ∈ (K : Set G)
    · simp only [v, Set.indicator_of_mem hxK]
      simpa using RCLike.mul_conj (Circle.coeHom (γ x))
    · simp [v, hxK]
  rw [integral_congr_ae heq, integral_indicator_const 1 hK, hfnorm]
  simp

theorem norm_fourierLinear (γ : G →ₜ* Circle) : ‖fourierLinear μ γ‖ = 1 := by
  refine le_antisymm (norm_fourierLinear_le μ γ) ?_
  obtain ⟨f, hfpos, hf⟩ := exists_fourier_norm_attaining μ γ
  have hbound := (fourierLinear μ γ).le_opNorm f
  rw [fourierLinear_apply, hf, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg f)] at hbound
  exact (mul_le_mul_iff_left₀ hfpos).mp (by simpa only [mul_comm, mul_one] using hbound)

theorem fourierLinear_nonzero (γ : G →ₜ* Circle) : (fourierLinear μ γ).toLinearMap ≠ 0 := by
  intro h
  obtain ⟨f, hfpos, hf⟩ := exists_fourier_norm_attaining μ γ
  have hz : fourierValue μ γ f = 0 := congrArg (fun L : L1 μ →ₗ[ℂ] ℂ => L f) h
  rw [hf] at hz
  exact hfpos.ne' (Complex.ofReal_eq_zero.mp hz)

/-- Equality of all Fourier evaluations determines the group character. -/
theorem fourier_injective {γ η : G →ₜ* Circle}
    (h : ∀ f : L1 μ, fourierValue μ γ f = fourierValue μ η f) : γ = η := by
  obtain ⟨f, hfpos, hf⟩ := exists_fourier_norm_attaining μ η
  have hne : fourierValue μ η f ≠ 0 := by
    rw [hf]
    exact Complex.ofReal_ne_zero.mpr hfpos.ne'
  apply ContinuousMonoidHom.ext
  intro x
  apply Circle.coe_injective
  have hx := h (translate μ x f)
  rw [fourier_translate, fourier_translate, h f] at hx
  exact star_injective (mul_right_cancel₀ hne hx)

end Haar

end FourierEvaluation

section AlgebraicCharacters
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Automatic boundedness uses a contraction equation, so even the
associativity theorem is not needed in this argument. -/
theorem character_norm_le (χ : L1 μ →ₗ[ℂ] ℂ)
    (hmul : ∀ f g, χ (convolution μ f g) = χ f * χ g) (f : L1 μ) :
    ‖χ f‖ ≤ ‖f‖ := by
  by_contra hn
  have hlarge : ‖f‖ < ‖χ f‖ := lt_of_not_ge hn
  have hpos : 0 < ‖χ f‖ := (norm_nonneg f).trans_lt hlarge
  have hχf : χ f ≠ 0 := norm_pos_iff.mp hpos
  let a : L1 μ := (χ f)⁻¹ • f
  have ha : ‖a‖ < 1 := by
    simp only [a, norm_smul, norm_inv, inv_mul_eq_div]
    exact (div_lt_one hpos).mpr hlarge
  have hχa : χ a = 1 := by simp [a, map_smul, smul_eq_mul, hχf]
  let T : L1 μ → L1 μ := fun b => a + convolutionRightLinear μ a b
  have hT : ContractingWith ‖a‖₊ T := by
    refine ⟨ha, LipschitzWith.of_dist_le_mul fun b c => ?_⟩
    change dist (a + convolutionRightLinear μ a b) (a + convolutionRightLinear μ a c) ≤
      ‖a‖ * dist b c
    rw [dist_add_left, dist_eq_norm, ← map_sub, dist_eq_norm]
    exact convolution_norm_le μ a (b - c)
  have hb := hT.fixedPoint_isFixedPt
  have heq := congrArg χ hb
  change χ (a + convolution μ a (hT.fixedPoint T)) = χ (hT.fixedPoint T) at heq
  rw [map_add, hmul, hχa, one_mul] at heq
  have hfalse : (1 : ℂ) = 0 := add_right_cancel (heq.trans (zero_add _).symm)
  exact one_ne_zero hfalse

def characterLinear (χ : L1 μ →ₗ[ℂ] ℂ)
    (hmul : ∀ f g, χ (convolution μ f g) = χ f * χ g) : L1 μ →L[ℂ] ℂ :=
  χ.mkContinuous 1 (fun f => by simpa only [one_mul] using character_norm_le μ χ hmul f)

@[simp] theorem characterLinear_apply (χ : L1 μ →ₗ[ℂ] ℂ)
    (hmul : ∀ f g, χ (convolution μ f g) = χ f * χ g) (f : L1 μ) :
    characterLinear μ χ hmul f = χ f := rfl

/-- The ratio obtained from one nonzero value controls every translate. -/
theorem character_translate_ratio (χ : L1 μ →ₗ[ℂ] ℂ)
    (hmul : ∀ f g, χ (convolution μ f g) = χ f * χ g)
    (f₀ : L1 μ) (hf₀ : χ f₀ ≠ 0) (x : G) (f : L1 μ) :
    χ (translate μ x f) = (χ (translate μ x f₀) / χ f₀) * χ f := by
  have h := congrArg χ ((convolution_translate_left μ x f f₀).trans
    (translate_convolution_right μ x f f₀))
  rw [hmul, hmul] at h
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hf₀).mpr
  exact h.trans (mul_comm _ _)

/-- A bounded multiplicative functional induces a continuous circle-valued
group homomorphism, acting on all its translates by scalars. -/
theorem character_translation_hom (χ : L1 μ →ₗ[ℂ] ℂ) (hχ : χ ≠ 0)
    (hmul : ∀ f g, χ (convolution μ f g) = χ f * χ g) :
    ∃ c : G →ₜ* Circle, ∀ x f, χ (translate μ x f) = Circle.coeHom (c x) * χ f := by
  obtain ⟨f₀, hf₀⟩ : ∃ f : L1 μ, χ f ≠ 0 := by
    by_contra hn
    apply hχ
    ext f
    exact not_not.mp (fun h => hn ⟨f, h⟩)
  let c : G → ℂ := fun x => χ (translate μ x f₀) / χ f₀
  have heigen (x : G) (f : L1 μ) : χ (translate μ x f) = c x * χ f :=
    character_translate_ratio μ χ hmul f₀ hf₀ x f
  have hone : c 1 = 1 := by simp [c, hf₀]
  have hmulc (x y : G) : c (x * y) = c x * c y := by
    apply (mul_right_cancel₀ hf₀)
    rw [← heigen, translate_mul, heigen, heigen, mul_assoc]
  let L : L1 μ →L[ℂ] ℂ := characterLinear μ χ hmul
  have hLne : L ≠ 0 := by
    intro h
    apply hf₀
    exact congrArg (fun T : L1 μ →L[ℂ] ℂ => T f₀) h
  have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hLne
  have hcle (x : G) : ‖c x‖ ≤ 1 := by
    have heq : L.comp (translate μ x).toContinuousLinearMap = c x • L := by
      ext f
      exact heigen x f
    have hbound : ‖c x • L‖ ≤ ‖L‖ := by
      rw [← heq]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro f
      calc
        ‖L (translate μ x f)‖ ≤ ‖L‖ * ‖translate μ x f‖ := L.le_opNorm _
        _ = ‖L‖ * ‖f‖ := by rw [norm_translate]
    rw [norm_smul] at hbound
    exact le_of_mul_le_mul_right (by simpa only [one_mul] using hbound) hLpos
  have hcnorm (x : G) : ‖c x‖ = 1 := by
    refine le_antisymm (hcle x) ?_
    have hinv : c x * c x⁻¹ = 1 := by rw [← hmulc, mul_inv_cancel, hone]
    calc
      1 = ‖c x‖ * ‖c x⁻¹‖ := by rw [← norm_mul, hinv, norm_one]
      _ ≤ ‖c x‖ * 1 := mul_le_mul_of_nonneg_left (hcle x⁻¹) (norm_nonneg _)
      _ = ‖c x‖ := mul_one _
  have hccont : Continuous c := by
    exact (L.continuous.comp ((continuous_translate μ).comp
      (continuous_id.prodMk continuous_const))).div_const _
  have hmem (x : G) : c x ∈ Submonoid.unitSphere ℂ := by
    change dist (c x) 0 = 1
    simpa using hcnorm x
  let C : G →ₜ* Circle :=
    { toFun := fun x => ⟨c x, hmem x⟩
      map_one' := Circle.ext hone
      map_mul' := fun x y => Circle.ext (hmulc x y)
      continuous_toFun := hccont.subtype_mk hmem }
  exact ⟨C, heigen⟩

/-- Applying the bounded character to the Bochner identity identifies its
integral kernel, with no L¹-duality representation assumption. -/
theorem character_integral (χ : L1 μ →ₗ[ℂ] ℂ)
    (hmul : ∀ f g, χ (convolution μ f g) = χ f * χ g)
    (g : L1 μ) (hg : χ g ≠ 0) (c : G → ℂ)
    (hc : ∀ x, χ (translate μ x g) = c x * χ g) (f : L1 μ) :
    χ f = ∫ x, f x * c x ∂μ := by
  apply mul_right_cancel₀ hg
  rw [← hmul]
  change characterLinear μ χ hmul (∫ x, f x • translate μ x g ∂μ) = _
  rw [← (characterLinear μ χ hmul).integral_comp_comm (convolution_integrable μ f g)]
  simp only [map_smul, characterLinear_apply, smul_eq_mul, hc, ← mul_assoc, integral_mul_const]

/-- Complete character classification for the concrete Bochner product. -/
theorem character_classification :
    _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.CharacterClassification μ := by
  constructor
  · intro γ
    exact ⟨fourierLinear μ γ, fourierLinear_apply μ γ,
      ⟨fourierLinear_nonzero μ γ, fourier_convolution μ γ⟩, norm_fourierLinear μ γ⟩
  · intro χ hχ
    rcases hχ with ⟨hχne, hmul⟩
    refine ⟨?_, (characterLinear μ χ hmul).continuous⟩
    obtain ⟨c, hc⟩ := character_translation_hom μ χ hχne hmul
    let γ : G →ₜ* Circle := c⁻¹
    have hγ (x : G) : star (Circle.coeHom (γ x)) = Circle.coeHom (c x) := by
      change star (Circle.coeHom ((c x)⁻¹)) = _
      have hi : Circle.coeHom ((c x)⁻¹) = star (Circle.coeHom (c x)) :=
        Circle.coe_inv_eq_conj (c x)
      rw [hi, star_star]
    have hrepr (f : L1 μ) : χ f = fourierValue μ γ f := by
      obtain ⟨g, hg⟩ : ∃ g : L1 μ, χ g ≠ 0 := by
        by_contra hn
        apply hχne
        ext g
        exact not_not.mp (fun hg => hn ⟨g, hg⟩)
      rw [character_integral μ χ hmul g hg (fun x => Circle.coeHom (c x)) (fun x => hc x g) f]
      change (∫ x, f x * Circle.coeHom (c x) ∂μ) = ∫ x, f x * star (Circle.coeHom (γ x)) ∂μ
      simp only [hγ]
    refine ⟨γ, hrepr, ?_⟩
    intro η hη
    exact fourier_injective μ (fun f => (hη f).symm.trans (hrepr f))

end AlgebraicCharacters

/-! Closed targets for the full group-algebra obligation and its components. -/

theorem translation_theorem :
    _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.TranslationTheorem.{u} := by
  intro G _ _ _ _ _ _ _ μ _ _
  exact translation_properties μ

theorem convolution_basic_theorem :
    _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.ConvolutionBasicTheorem.{u} := by
  intro G _ _ _ _ _ _ _ μ _ _
  exact convolution_basic_properties μ

theorem character_theorem :
    _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.CharacterTheorem.{u} := by
  intro G _ _ _ _ _ _ _ μ _ _
  exact character_classification μ

theorem convolution_theorem :
    _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.ConvolutionTheorem.{u} := by
  intro G _ _ _ _ _ _ _ μ _ _
  exact convolution_properties μ

theorem group_algebra_theorem :
    _root_.Specs.ExpandedFA.BanachAlgebra.GroupAlgebraCharacters.GroupAlgebraTheorem.{u} := by
  intro G _ _ _ _ _ _ _ μ _ _
  exact ⟨convolution_properties μ, character_classification μ⟩

end ExpandedFA.BanachAlgebra.GroupAlgebraCharacters

/- Mathlib proof attribution
Adapted portion near line 149:
The continuous compactly supported approximation and density arguments used
for group algebra characters.

Upstream: Mathlib/MeasureTheory/Function/ContinuousMapDense.lean (around line 84)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
