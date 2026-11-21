import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.RadonCcDensityBridge
import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.D11.Ch18.CompactCutoff
import MathGenome.Internal.RealAnalysis.D11.Ch04.CompletionVersions
import MathGenome.Internal.RealAnalysis.D11.Ch11.FinitePSimpleDensity
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Cc density and the ordinary completion isometry

For a finite-measure Borel set s, compact inner approximation on finite sets
and open outer approximation give K ⊆ s ⊆ U with μ(U \ K) small. The LCH
cutoff between K and U has error bounded by the indicator of U \ K.
Simple-function density extends this to all finite-p functions. Global
normality and countability of the domain are never used.

The completion map pulls back along the identity from the ordinary completed
domain to the original measurable domain. Its surjectivity uses an originally
measurable scalar version, and its inverse therefore supplies a Borel version
when the original domain is Borel. No larger Caratheodory domain occurs.
-/

open Set MeasureTheory
open scoped ENNReal
universe u
set_option maxHeartbeats 1200000
noncomputable section
namespace D11.Ch11.RadonCcDensityBridge

section Approximation
variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  {μ : Measure X} [μ.Regular] {p : ℝ≥0∞}

/-- LCH cutoffs approximate finite-measure indicators, without global normality. -/
theorem exists_cc_indicator (hp : p ≠ ∞) (c : 𝕜) {s : Set X}
    (hs : MeasurableSet s) (hμs : μ s < ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → 𝕜, eLpNorm (g - s.indicator (fun _ => c)) p μ ≤ ε ∧
      Continuous g ∧ MemLp g p μ ∧ HasCompactSupport g := by
  obtain ⟨η, hη, hbound⟩ := exists_eLpNorm_indicator_le (μ := μ) hp c hε
  have hhalf : (η : ℝ≥0∞) / 2 ≠ 0 :=
    (ENNReal.half_pos (ENNReal.coe_pos.mpr hη).ne').ne'
  obtain ⟨K, hKs, hK, hsmallK⟩ := hs.exists_isCompact_sdiff_lt hμs.ne hhalf
  obtain ⟨U, hsU, hU, _hμU, hsmallU⟩ := hs.exists_isOpen_sdiff_lt hμs.ne hhalf
  obtain ⟨φ, hφ, hφK, _hφcomp, hφU⟩ :=
    D11.Ch18.compact_cutoff X K U hK hU (hKs.trans hsU)
  let g : X → 𝕜 := fun x => φ x • c
  have hgcont : Continuous g := φ.continuous.smul continuous_const
  have hgsupp : HasCompactSupport g := φ.hasCompactSupport.smul_right
  have hgmem : MemLp g p μ := hgcont.memLp_of_hasCompactSupport hgsupp
  have hμUK : μ (U \ K) ≤ (η : ℝ≥0∞) := by
    calc
      μ (U \ K) ≤ μ (U \ s) + μ (s \ K) :=
        (measure_mono (by intro x hx; by_cases hxs : x ∈ s <;> simp_all)).trans
          (measure_union_le _ _)
      _ ≤ (η : ℝ≥0∞) / 2 + (η : ℝ≥0∞) / 2 := add_le_add hsmallU.le hsmallK.le
      _ = η := ENNReal.add_halves _
  have hpoint : ∀ x, ‖g x - s.indicator (fun _ => c) x‖ ≤
      ‖(U \ K).indicator (fun _ => c) x‖ := by
    intro x
    have hnorm : ‖φ x‖ = φ x := Real.norm_of_nonneg (hφ x).1
    by_cases hxK : x ∈ K
    · simp [g, hxK, hKs hxK, hφK x hxK]
    by_cases hxU : x ∈ U
    · by_cases hxs : x ∈ s
      · simp only [g, indicator_of_mem hxs, indicator_of_mem (show x ∈ U \ K from ⟨hxU, hxK⟩)]
        have hdiff : φ x • c - c = (φ x - 1) • c := by rw [sub_smul, one_smul]
        rw [hdiff, norm_smul, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (hφ x).2)]
        exact mul_le_of_le_one_left (norm_nonneg c) (by linarith [(hφ x).1])
      · simp only [g, indicator_of_notMem hxs, sub_zero,
          indicator_of_mem (show x ∈ U \ K from ⟨hxU, hxK⟩), norm_smul, hnorm]
        exact mul_le_of_le_one_left (norm_nonneg c) (hφ x).2
    · have hxφ : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxU (hφU h))
      have hxs : x ∉ s := fun h => hxU (hsU h)
      simp [g, hxφ, hxs, hxU]
  exact ⟨g, (eLpNorm_mono (hgmem.aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator hs)) hpoint).trans
      (hbound _ hμUK ((hU.measurableSet.diff hK.measurableSet).nullMeasurableSet)),
    hgcont, hgmem, hgsupp⟩

/-- Extension from indicators to all MemLp functions by simple-function density. -/
theorem exists_cc_approximation (hp : p ≠ ∞) {f : X → 𝕜} (hf : MemLp f p μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → 𝕜, eLpNorm (f - g) p μ ≤ ε ∧
      Continuous g ∧ MemLp g p μ ∧ HasCompactSupport g := by
  apply hf.induction_dense hp
    (fun g => Continuous g ∧ MemLp g p μ ∧ HasCompactSupport g) ?_ ?_ hε
  · intro c s hs hμs ε hε
    exact exists_cc_indicator hp c hs hμs hε
  · rintro f g ⟨hfcont, hfmem, hfcomp⟩ ⟨hgcont, hgmem, hgcomp⟩
    exact ⟨hfcont.add hgcont, hfmem.add hgmem, hfcomp.add hgcomp⟩

end Approximation

section Completion
variable {X : Type u} [m : MeasurableSpace X]
  {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Identity from the ordinary completed domain into the original domain. -/
theorem completion_id_measurePreserving :
    @MeasurePreserving (NullMeasurableSpace X μ) X _ m
      id (μ.completion) μ := by
  have hid : @Measurable (NullMeasurableSpace X μ) X _ m id :=
    fun s hs => hs.nullMeasurableSet
  refine @MeasurePreserving.mk (NullMeasurableSpace X μ) X _ m id
    (μ.completion) μ hid ?_
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hid hs]
  rfl

/-- The canonical linear isometric embedding preserves ordinary representatives. -/
def toCompletion : Lp 𝕜 p μ →ₗᵢ[𝕜]
    Lp 𝕜 p μ.completion :=
  Lp.compMeasurePreservingₗᵢ 𝕜 id (completion_id_measurePreserving μ)

theorem toCompletion_ae (f : Lp 𝕜 p μ) :
    (toCompletion μ p f : X → 𝕜) =ᵐ[μ] (f : X → 𝕜) :=
  Lp.coeFn_compMeasurePreserving f (completion_id_measurePreserving μ)

/-- Surjectivity uses an originally measurable version, with no measure-size hypothesis. -/
theorem toCompletion_surjective : Function.Surjective (toCompletion (𝕜 := 𝕜) μ p) := by
  intro f
  obtain ⟨g, hg, heq⟩ := D11.Ch04.CompletionVersions.version_of_countablyGenerated
    μ (f : X → 𝕜) (Lp.stronglyMeasurable f).measurable
  have heq' : g =ᵐ[μ] (f : X → 𝕜) :=
    (D11.Ch04.AeCommonException.aeEq_iff_native μ g f).mp heq
  let gc : NullMeasurableSpace X μ → 𝕜 := fun x => g x
  have heqc : gc =ᵐ[μ.completion] (f : NullMeasurableSpace X μ → 𝕜) := heq'
  have hn : eLpNorm g p μ =
      eLpNorm gc p μ.completion :=
    (eLpNorm_comp_measurePreserving hg.aestronglyMeasurable
      (completion_id_measurePreserving μ)).symm
  have hmem : MemLp g p μ := by
    change eLpNorm g p μ < ∞
    calc
      eLpNorm g p μ = eLpNorm gc p μ.completion := hn
      _ = eLpNorm f p μ.completion := eLpNorm_congr_ae heqc
      _ < ∞ := Lp.memLp f
  refine ⟨hmem.toLp g, ?_⟩
  apply Lp.ext
  exact (toCompletion_ae μ p (hmem.toLp g)).trans (hmem.coeFn_toLp.trans heq')

/-- Ordinary completion changes the measurable representatives, but not Lp classes. -/
def completionLinearIsometryEquiv : Lp 𝕜 p μ ≃ₗᵢ[𝕜]
    Lp 𝕜 p μ.completion :=
  LinearIsometryEquiv.ofSurjective (toCompletion μ p) (toCompletion_surjective μ p)

end Completion

theorem completion_isometry : Specs.D11.Ch11.RadonCcDensityBridge.completion_isometry := by
  intro X m 𝕜 _ _ _ μ p _
  let e := completionLinearIsometryEquiv (𝕜 := 𝕜) μ p
  have he : ∀ f : Lp 𝕜 p μ, (e f : X → 𝕜) =ᵐ[μ] (f : X → 𝕜) :=
    toCompletion_ae μ p
  refine ⟨e, ⟨he, ?_⟩, ?_⟩
  · intro f
    refine ⟨(Lp.stronglyMeasurable (e.symm f)).measurable, ?_⟩
    have h := (he (e.symm f)).symm
    rw [e.apply_symm_apply] at h
    exact h
  · intro e' he'
    apply LinearIsometryEquiv.ext
    intro f
    exact Lp.ext ((he'.1 f).trans (he f).symm)

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

theorem radon_cc_density : Specs.D11.Ch11.RadonCcDensityBridge.radon_cc_density := by
  intro X _ _ _ 𝕜 _ _ _ μ hμ p _ hp f ε hε
  letI : BorelSpace X := ⟨rfl⟩
  letI : μ.Regular := (D11.Ch18.isRadon_iff_regular μ).mp hμ
  obtain ⟨g, hgerr, hgcont, hgmem, hgsupp⟩ :=
    exists_cc_approximation hp (Lp.memLp f)
      (ENNReal.ofReal_ne_zero_iff.mpr (half_pos hε))
  let g' : CompactlySupportedContinuousMap X 𝕜 := ⟨⟨g, hgcont⟩, hgsupp⟩
  refine ⟨g', hgmem, ?_⟩
  rw [← Lp.toLp_coeFn f (Lp.memLp f), ← MemLp.toLp_sub, Lp.norm_toLp]
  exact (ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hgerr).trans_lt
    (by rw [ENNReal.toReal_ofReal (half_pos hε).le]; exact half_lt_self hε)

/-- Transfer the approximants through the established ordinary quotient isometry. -/
theorem ordinary_quotient_density :
    Specs.D11.Ch11.RadonCcDensityBridge.ordinary_quotient_density := by
  intro X _ _ _ 𝕜 _ _ _ μ hμ p _ hp
  refine ⟨D11.Ch10.QuotientConstruction.quotientNormedAddCommGroup μ p,
    D11.Ch10.QuotientConstruction.quotientNormedSpace μ p,
    D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ p,
    D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv_classOf μ p, ?_⟩
  intro f ε hε
  obtain ⟨g, hg, herr⟩ := radon_cc_density μ hμ p hp
    (D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ p f) ε hε
  refine ⟨g, hg, ?_⟩
  rw [← (D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ p).norm_map,
    map_sub, D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv_classOf]
  exact herr

theorem completed_radon_cc_density :
    Specs.D11.Ch11.RadonCcDensityBridge.completed_radon_cc_density := by
  intro X _ _ _ 𝕜 _ _ _ μ hμ p _ hp f ε hε
  let e := completionLinearIsometryEquiv (𝕜 := 𝕜) μ p
  obtain ⟨g, hg, herr⟩ := radon_cc_density μ hμ p hp (e.symm f) ε hε
  let gc : NullMeasurableSpace X μ → 𝕜 := fun x => g x
  have hg' : MemLp gc p μ.completion :=
    hg.comp_measurePreserving (completion_id_measurePreserving μ)
  refine ⟨g, hg', hg, ?_⟩
  have heq : e (hg.toLp g) = hg'.toLp gc := rfl
  change ‖f - e (hg.toLp g)‖ < ε
  have herr' := herr
  rw [← e.norm_map (e.symm f - hg.toLp g), map_sub, e.apply_symm_apply] at herr'
  exact herr'

end D11.Ch11.RadonCcDensityBridge
