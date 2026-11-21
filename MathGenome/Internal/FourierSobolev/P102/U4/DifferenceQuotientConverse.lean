import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DifferenceQuotientConverse
import MathGenome.Internal.FourierSobolev.P102.U4.DifferenceQuotientEstimate
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevTranslationCharacterization

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped NNReal ENNReal Topology Convolution
namespace P102.U4.DifferenceQuotient

/-- Every compact subset of Ω is contained in a relatively compact open subset. -/
theorem exists_relativelyCompact_open {d : ℕ} {Ω : Opens (Space d)}
    {K : Set (Space d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ V : Opens (Space d), RelativelyCompactIn V Ω ∧ K ⊆ V := by
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  exact ⟨⟨V, hVo⟩, ⟨hVc, hVΩ⟩, hKV⟩

/-- The local Lp hypothesis supplies the local L¹ needed by regular distributions. -/
theorem LocallyMemLp.locallyIntegrableOn {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} {u : Space d → 𝕜}
    (hu : LocallyMemLp Ω p u) (hp : 1 ≤ p) : LocallyIntegrableOn u Ω volume := by
  intro x hx
  obtain ⟨V, hV, hxV⟩ := exists_relativelyCompact_open (isCompact_singleton (x := x))
    (singleton_subset_iff.mpr hx)
  have hfinite : IsFiniteMeasure (volume.restrict (V : Set (Space d))) :=
    isFiniteMeasure_restrict.mpr
      ((hV.1.isBounded.subset subset_closure).measure_lt_top.ne)
  exact ⟨V, mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds (hxV (by simp))),
    (hu V hV).integrable hp⟩

/-- Finite-exponent norms on increasing measurable domains recover the union norm. -/
theorem eLpNorm_exhaustion {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {V : ℕ → Opens (Space d)}
    (hV : IsExhaustion Ω V) {p : ℝ≥0∞} (hp : p ≠ 0) (hpt : p ≠ ∞)
    {v : Space d → 𝕜}
    (hv : ∀ n, AEStronglyMeasurable v (volume.restrict (V n : Set (Space d)))) :
    eLpNorm v p (volume.restrict (Ω : Set (Space d))) =
      ⨆ n, eLpNorm v p (volume.restrict (V n : Set (Space d))) := by
  have hm : AEStronglyMeasurable v (volume.restrict (Ω : Set (Space d))) := by
    rw [← hV.2.2]
    exact AEStronglyMeasurable.iUnion hv
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpt hm]
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpt (hv _)]
  rw [← hV.2.2, setLIntegral_iUnion_of_directed _ hV.1.directed_le]
  exact (ENNReal.orderIsoRpow (1 / p.toReal)
    (one_div_pos.mpr (ENNReal.toReal_pos hp hpt))).map_iSup _

/-- A common bound on an increasing exhaustion gives a global Lp bound. -/
theorem memLp_of_exhaustion_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {V : ℕ → Opens (Space d)}
    (hV : IsExhaustion Ω V) {p : ℝ≥0∞} (hp : p ≠ 0) (hpt : p ≠ ∞)
    {v : Space d → 𝕜} (hv : LocallyMemLp Ω p v) (C : ℝ≥0)
    (hC : ∀ n, eLpNorm v p (volume.restrict (V n : Set (Space d))) ≤ C) :
    MemLp v p (volume.restrict (Ω : Set (Space d))) ∧
      eLpNorm v p (volume.restrict (Ω : Set (Space d))) ≤ C := by
  have hm n := (hv (V n) (hV.2.1 n)).aestronglyMeasurable
  have hb : eLpNorm v p (volume.restrict (Ω : Set (Space d))) ≤ C := by
    rw [eLpNorm_exhaustion hV hp hpt hm]
    exact iSup_le hC
  refine ⟨?_, hb⟩
  exact hb.trans_lt ENNReal.coe_lt_top

/-- Restricting a quotient bound preserves its constant and step size. -/
theorem HasBound.mono {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω V W : Opens (Space d)} {j : Fin d} {p : ℝ≥0∞}
    {u : Space d → 𝕜} {C : ℝ≥0} (h : HasBound Ω V j p u C) (hWV : W ≤ V) :
    HasBound Ω W j p u C := by
  obtain ⟨δ, hδ, hb⟩ := h
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  obtain ⟨hs, hm, hn⟩ := hb t ht htδ
  have hμ := Measure.restrict_mono hWV (le_refl volume)
  exact ⟨fun x hx => hs x (hWV hx), hm.mono_measure hμ,
    (eLpNorm_mono_measure _ hμ).trans hn⟩

/-- Compact subsets are contained in a single stage of an open exhaustion. -/
theorem IsExhaustion.cofinal {d : ℕ} {Ω : Opens (Space d)}
    {V : ℕ → Opens (Space d)} (hV : IsExhaustion Ω V)
    {K : Set (Space d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ n, K ⊆ (V n : Set (Space d)) := by
  apply hK.elim_directed_cover (fun n => (V n : Set (Space d)))
    (fun n => (V n).isOpen)
  · intro x hx
    rw [hV.2.2]
    exact hKΩ hx
  · exact hV.1.directed_le

/-- The common-bound hypothesis on an exhaustion supplies all local bounds. -/
theorem locallyBounded_of_exhaustion {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {V : ℕ → Opens (Space d)} (hV : IsExhaustion Ω V)
    {u : Space d → 𝕜} {j : Fin d} {p : ℝ≥0∞} {C : ℝ≥0}
    (hC : ∀ n, HasBound Ω (V n) j p u C) : LocallyBounded Ω j p u := by
  intro W hW
  obtain ⟨n, hn⟩ := hV.cofinal hW.1 hW.2
  exact ⟨C, (hC n).mono (subset_closure.trans hn)⟩

/-- Relatively compact increasing open exhaustions exist even for the empty domain. -/
theorem exists_exhaustion {d : ℕ} (Ω : Opens (Space d)) :
    ∃ V : ℕ → Opens (Space d), IsExhaustion Ω V := by
  let := Ω.isOpen.locallyCompactSpace
  let K := CompactExhaustion.choice (Ω : Set (Space d))
  let A : ℕ → Set (Space d) := fun n => Subtype.val '' K n
  have hc (n : ℕ) : IsCompact (A n) := (K.isCompact n).image continuous_subtype_val
  have hs (n : ℕ) : A n ⊆ (Ω : Set (Space d)) := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  let V : ℕ → Opens (Space d) := fun n => ⟨interior (A n), isOpen_interior⟩
  refine ⟨V, ?_, ?_, ?_⟩
  · intro m n hmn
    exact interior_mono (image_mono (K.subset hmn))
  · intro n
    exact ⟨(hc n).closure_of_subset interior_subset,
      (closure_mono interior_subset).trans ((hc n).isClosed.closure_subset.trans (hs n))⟩
  · apply Subset.antisymm
    · exact iUnion_subset (fun n => interior_subset.trans (hs n))
    · intro x hx
      obtain ⟨n, hn⟩ := K.exists_mem ⟨x, hx⟩
      refine mem_iUnion.mpr ⟨n + 1, ?_⟩
      exact Ω.isOpen.isOpenMap_subtype_val.image_interior_subset _
        ⟨⟨x, hx⟩, K.subset_interior_succ n hn, rfl⟩

/-- The generic Hahn–Banach/Lp-duality bridge, specialized to the shared test
space. This does not assume that the distribution is already regular. -/
theorem exists_density_of_test_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate q p] (hqt : q ≠ ∞)
    (T : DistributionSpace 𝕜 Ω) (C : ℝ≥0)
    (hT : ∀ φ : TestSpace 𝕜 Ω,
      ‖T φ‖ ≤ C * (eLpNorm φ q (volume.restrict (Ω : Set (Space d)))).toReal) :
    ∃ g : DomainLp 𝕜 Ω p,
      eLpNorm g p (volume.restrict (Ω : Set (Space d))) ≤ C ∧
      T = regularDistribution Ω g := by
  let J : TestSpace 𝕜 Ω →ₗ[𝕜] DomainLp 𝕜 Ω q :=
    { toFun := fun φ => (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hJ (φ : TestSpace 𝕜 Ω) : ‖J φ‖ =
      (eLpNorm φ q (volume.restrict (Ω : Set (Space d)))).toReal :=
    Lp.norm_toLp φ (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)
  obtain ⟨g, hg, hrepr⟩ :=
    ExpandedFA.Sobolev.Translation.exists_lp_density_of_linear_bound
      (volume.restrict (Ω : Set (Space d))) p q hqt J T.toLinearMap C C.coe_nonneg
      (by
        intro φ
        change ‖T φ‖ ≤ C * ‖J φ‖
        rw [hJ]
        exact hT φ)
  refine ⟨g, ?_, ?_⟩
  · rw [← Lp.enorm_def, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hg
  · ext φ
    rw [regular_pairing d 𝕜 Ω g (domainLp_locallyIntegrable Ω p g)]
    have he := hrepr φ
    change T φ = ∫ x in Ω, J φ x * g x at he
    rw [he]
    apply integral_congr_ae
    have hφ := (φ.continuous.memLp_of_hasCompactSupport
      (μ := volume.restrict (Ω : Set (Space d))) (p := q) φ.hasCompactSupport).coeFn_toLp
    filter_upwards [hφ] with x hx
    rw [show J φ x = φ x from hx, mul_comm]

/-- Differentiating a compact-test correlation places the derivative on the
smooth test. The input needs only local integrability on the ambient space. -/
theorem test_translate_hasDerivAt {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (u : Space d → 𝕜) (hu : LocallyIntegrable u volume)
    (φ : TestSpace 𝕜 Ω) (j : Fin d) :
    HasDerivAt (fun t : ℝ => ∫ x, φ x * u (x + t • coordinateVector d j))
      (-(∫ x, testPartialWord Ω [j] φ x * u x)) 0 := by
  let ψ : Space d → 𝕜 := fun x => φ (-x)
  let L : 𝕜 →L[ℝ] 𝕜 →L[ℝ] 𝕜 := ContinuousLinearMap.mul ℝ 𝕜
  have hc : HasCompactSupport ψ := φ.hasCompactSupport.comp_homeomorph (Homeomorph.neg _)
  have hd : ContDiff ℝ 1 ψ := φ.contDiff.of_le (by simp) |>.comp contDiff_neg
  have hf := hc.hasFDerivAt_convolution_right L hu hd (0 : Space d)
  have hψ (x : Space d) : fderiv ℝ ψ (-x) (coordinateVector d j) =
      -(testPartialWord Ω [j] φ x) := by
    have hh : HasFDerivAt ψ
        ((fderiv ℝ φ x).comp (-(ContinuousLinearMap.id ℝ (Space d)))) (-x) := by
      convert (φ.contDiff.differentiable (by simp) (-(-x))).hasFDerivAt.comp (-x)
        ((hasFDerivAt_id (-x)).neg) using 1 <;> simp [ψ, Function.comp_def]
    rw [hh.fderiv, testPartialWord_coe]
    simp [partialWord]
  have hi : Integrable (fun x => (L.precompR (Space d)) (u x) (fderiv ℝ ψ (-x))) volume := by
    have h := (hc.fderiv ℝ).convolutionExists_right (L.precompR (Space d)) hu
      (hd.continuous_fderiv (by simp)) (0 : Space d)
    simpa only [ConvolutionExistsAt, zero_sub] using h
  have hf' : HasFDerivAt (u ⋆[L, volume] ψ)
      ((u ⋆[L.precompR (Space d), volume] fderiv ℝ ψ) 0)
      ((0 : ℝ) • coordinateVector d j) := by simpa only [zero_smul] using hf
  have hder := hf'.comp_hasDerivAt (0 : ℝ)
    (by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector d j)) :
      HasDerivAt (fun t : ℝ => t • coordinateVector d j) (coordinateVector d j) 0)
  have hde : ((u ⋆[L.precompR (Space d), volume] fderiv ℝ ψ) 0)
      (coordinateVector d j) = -(∫ x, testPartialWord Ω [j] φ x * u x) := by
    simp only [convolution_def, zero_sub]
    rw [ContinuousLinearMap.integral_apply hi]
    simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, hψ]
    change (∫ x, u x * -(testPartialWord Ω [j] φ x)) = _
    simp_rw [mul_neg, mul_comm (u _)]
    exact integral_neg _
  rw [hde] at hder
  convert hder using 1
  funext t
  change (∫ x, φ x * u (x + t • coordinateVector d j)) =
    (∫ x, u x * ψ (t • coordinateVector d j - x))
  rw [← integral_add_right_eq_self (fun x => u x * ψ (t • coordinateVector d j - x))
    (t • coordinateVector d j)]
  congr 1
  funext x
  simp [ψ, mul_comm]

/-- Hölder's inequality for the bilinear scalar pairing of raw representatives. -/
theorem integral_mul_bound {X : Type} [MeasurableSpace X]
    {𝕜 : Type} [RCLike 𝕜] {μ : Measure X} {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {f g : X → 𝕜} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    ‖∫ x, f x * g x ∂μ‖ ≤ (eLpNorm g q μ).toReal * (eLpNorm f p μ).toReal := by
  rw [← ExpandedFA.FunctionSpaces.lp_pairing_on_representatives μ p q f g hf hg]
  simpa only [Lp.norm_toLp] using
    ExpandedFA.FunctionSpaces.lp_pairing_apply_bound μ p q (hg.toLp g) (hf.toLp f)

/-- A uniform local quotient bound gives the sharp dual bound on compact tests.
A compact interior localization permits differentiating a correlation, without
requiring any integrability across the boundary of Ω. -/
theorem HasBound.test_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω V : Opens (Space d)} {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {u : Space d → 𝕜} {j : Fin d} {C : ℝ≥0}
    (hu : LocallyIntegrableOn u Ω volume) (hV : RelativelyCompactIn V Ω)
    (hb : HasBound Ω V j p u C) (φ : TestSpace 𝕜 V) :
    ‖∫ x, testPartialWord V [j] φ x * u x‖ ≤
      C * (eLpNorm φ q (volume.restrict (V : Set (Space d)))).toReal := by
  obtain ⟨ε, hε, hKΩ⟩ := hV.1.exists_cthickening_subset_open Ω.isOpen hV.2
  let K := Metric.cthickening ε (closure (V : Set (Space d)))
  have hKc : IsCompact K := hV.1.cthickening
  have hKm : MeasurableSet K := hKc.measurableSet
  let w := K.indicator u
  have hw : Integrable w volume :=
    (integrable_indicator_iff hKm).mpr (hu.integrableOn_compact_subset hKΩ hKc)
  have hbase (x : Space d) (hx : x ∈ (V : Set (Space d))) : w x = u x :=
    indicator_of_mem (Metric.self_subset_cthickening _ (subset_closure hx)) u
  have hshift (t : ℝ) (ht : |t| < ε) (x : Space d) (hx : x ∈ (V : Set (Space d))) :
      w (x + t • coordinateVector d j) = u (x + t • coordinateVector d j) := by
    apply indicator_of_mem _ u
    apply Metric.mem_cthickening_of_dist_le _ x ε _ (subset_closure hx)
    simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_coordinateVector,
      mul_one, Real.norm_eq_abs] using ht.le
  let F : ℝ → 𝕜 := fun t => ∫ x, φ x * w (x + t • coordinateVector d j)
  have hint (t : ℝ) : Integrable (fun x => φ x * w (x + t • coordinateVector d j)) :=
    φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
      (((measurePreserving_add_right volume (t • coordinateVector d j)).integrable_comp_of_integrable hw).locallyIntegrable.locallyIntegrableOn
          (V : Set (Space d)))
  have hder := test_translate_hasDerivAt w hw.locallyIntegrable φ j
  have hderu : (∫ x, testPartialWord V [j] φ x * w x) =
      ∫ x, testPartialWord V [j] φ x * u x := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    by_cases hx : x ∈ (V : Set (Space d))
    · rw [hbase x hx]
    · simp only [(testPartialWord V [j] φ).zero_on_compl hx, Pi.zero_apply, zero_mul]
  rw [hderu] at hder
  obtain ⟨δ, hδ, hb⟩ := hb
  have hφ : MemLp φ q (volume.restrict (V : Set (Space d))) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hinc : ∀ᶠ t in 𝓝 (0 : ℝ),
      ‖F t - F 0‖ ≤ (C * (eLpNorm φ q (volume.restrict (V : Set (Space d)))).toReal) * ‖t-0‖ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min hδ hε)] with t ht
    have ht' : |t| < min δ ε := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
    by_cases ht0 : t = 0
    · simp [ht0]
    obtain ⟨_, hm, hn⟩ := hb t (abs_pos.mpr ht0) (ht'.trans_le (min_le_left _ _))
    have heq : F t - F 0 = t •
        ∫ x in V, quotient u j t x * φ x := by
      rw [← integral_sub (hint t) (hint 0)]
      simp only [zero_smul, add_zero]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (V : Set (Space d)))
        (fun x hx => by simp only [φ.zero_on_compl hx, Pi.zero_apply, zero_mul, sub_self])]
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
      rw [hbase x hx, hshift t (ht'.trans_le (min_le_right _ _)) x hx]
      simp only [quotient, smul_mul_assoc, smul_smul, mul_inv_cancel₀ ht0, one_smul]
      ring
    rw [heq, norm_smul, Real.norm_eq_abs]
    have hbint : ‖∫ x in V, quotient u j t x * φ x‖ ≤
        C * (eLpNorm φ q (volume.restrict (V : Set (Space d)))).toReal := by
      calc
        _ ≤ (eLpNorm φ q (volume.restrict (V : Set (Space d)))).toReal *
            (eLpNorm (quotient u j t) p (volume.restrict (V : Set (Space d)))).toReal :=
          integral_mul_bound hm hφ
        _ ≤ (eLpNorm φ q (volume.restrict (V : Set (Space d)))).toReal * C :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast ENNReal.toReal_mono ENNReal.coe_ne_top hn)
            ENNReal.toReal_nonneg
        _ = _ := mul_comm _ _
    simpa only [sub_zero, Real.norm_eq_abs, mul_comm |t|] using
      mul_le_mul_of_nonneg_left hbint (abs_nonneg t)
  simpa only [norm_neg] using
    hder.le_of_lip' (mul_nonneg C.coe_nonneg ENNReal.toReal_nonneg) hinc

/-- Each bounded family of interior quotients determines an Lp derivative on V,
with exactly the same bound C. No weak derivative appears in the hypotheses. -/
theorem HasBound.exists_local_derivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω V : Opens (Space d)} {p : ℝ≥0∞} (hp : 1 < p) (hpt : p ≠ ∞)
    {u : Space d → 𝕜} {j : Fin d} {C : ℝ≥0}
    (hu : LocallyIntegrableOn u Ω volume) (hV : RelativelyCompactIn V Ω)
    (hb : HasBound Ω V j p u C) :
    ∃ g : DomainLp 𝕜 V p,
      eLpNorm g p (volume.restrict (V : Set (Space d))) ≤ C ∧
      distributionPartial {j} (regularDistribution V u) = regularDistribution V g := by
  let : Fact (1 ≤ p) := ⟨hp.le⟩
  obtain ⟨q, hq, hqt, hpq⟩ :=
    ExpandedFA.Sobolev.Translation.exists_interior_holder_conjugate hp hpt
  let : Fact (1 ≤ q) := ⟨hq.le⟩
  let : ENNReal.HolderConjugate p q := hpq
  have huV : LocallyIntegrableOn u V volume := hu.mono_set (subset_closure.trans hV.2)
  apply exists_density_of_test_bound V p q hqt
    (distributionPartial {j} (regularDistribution V u)) C
  intro φ
  have he : distributionPartial {j} (regularDistribution V u) φ =
      -(∫ x, testPartialWord V [j] φ x * u x) := by
    simp [distributionPartial, regularDistribution,
      TestFunction.integralAgainstBilinCLM_eq_integral huV]
  rw [he, norm_neg]
  exact hb.test_bound hu hV φ

/-- Restriction of a weak derivative to a smaller open set. -/
theorem weak_derivative_restrict {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω V : Opens (Space d)} (hVΩ : V ≤ Ω) {u v : Space d → 𝕜}
    {j : Fin d} (hu : LocallyIntegrableOn u Ω volume)
    (hv : LocallyIntegrableOn v Ω volume)
    (h : distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v) :
    distributionPartial {j} (regularDistribution V u) = regularDistribution V v := by
  apply (ACL.weak_iff_test_identity j (hu.mono_set hVΩ) (hv.mono_set hVΩ)).mpr
  intro φ
  let ψ : TestSpace 𝕜 Ω := TestFunction.monoCLM 𝕜 φ
  have he : (ψ : Space d → 𝕜) = φ := by
    simp only [ψ, TestFunction.monoCLM_apply, le_refl, hVΩ, and_self, ite_true]
  have hd : (testPartialWord Ω [j] ψ : Space d → 𝕜) = testPartialWord V [j] φ := by
    rw [testPartialWord_coe, he, testPartialWord_coe]
  simpa only [he, hd] using (ACL.weak_iff_test_identity j hu hv).mp h ψ

/-- Compatible local derivatives glue along an open exhaustion. Compatibility
is proved by injectivity of regular distributions, rather than assumed. -/
theorem exists_derivative_of_exhaustion {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {V : ℕ → Opens (Space d)} (hV : IsExhaustion Ω V)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : Space d → 𝕜} {j : Fin d}
    (hu : LocallyIntegrableOn u Ω volume)
    (g : ∀ n, DomainLp 𝕜 (V n) p)
    (hg : ∀ n, distributionPartial {j} (regularDistribution (V n) u) =
      regularDistribution (V n) (g n)) :
    ∃ v : Space d → 𝕜, LocallyMemLp Ω p v ∧
      distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v := by
  classical
  have hUΩ n : V n ≤ Ω := subset_closure.trans (hV.2.1 n).2
  have hgloc n := domainLp_locallyIntegrable (V n) p (g n)
  have hcompat (m n : ℕ) (hmn : m ≤ n) :
      (g m : Space d → 𝕜) =ᵐ[volume.restrict (V m : Set (Space d))] g n := by
    have hn := weak_derivative_restrict (hV.1 hmn) (hu.mono_set (hUΩ n)) (hgloc n) (hg n)
    exact (regular_injectivity d 𝕜 (V m) (g m) (g n)
      (hgloc m) ((hgloc n).mono_set (hV.1 hmn))).mp ((hg m).symm.trans hn)
  let v : Space d → 𝕜 := fun x =>
    if hx : ∃ n, x ∈ (V n : Set (Space d)) then g (Nat.find hx) x else 0
  have hvn (n : ℕ) : v =ᵐ[volume.restrict (V n : Set (Space d))] g n := by
    have hall (m : ℕ) : ∀ᵐ x ∂volume.restrict (V n : Set (Space d)),
        m ≤ n → x ∈ (V m : Set (Space d)) → g m x = g n x := by
      by_cases hm : m ≤ n
      · exact ae_restrict_of_ae ((ae_restrict_iff' (V m).isOpen.measurableSet).mp (hcompat m n hm))
          |>.mono (fun _ hx _ => hx)
      · exact Eventually.of_forall (fun _ h => (hm h).elim)
    filter_upwards [ae_all_iff.mpr hall, ae_restrict_mem (V n).isOpen.measurableSet] with x hx hxn
    have hex : ∃ k, x ∈ (V k : Set (Space d)) := ⟨n, hxn⟩
    simp only [v, dite_eq_left hex]
    exact hx (Nat.find hex) (Nat.find_min' hex hxn) (Nat.find_spec hex)
  have hvp : LocallyMemLp Ω p v := by
    intro W hW
    obtain ⟨n, hn⟩ := hV.cofinal hW.1 hW.2
    have hWn : W ≤ V n := subset_closure.trans hn
    exact (memLp_congr_ae (ae_restrict_of_ae_restrict_of_subset hWn (hvn n))).mpr
      ((Lp.memLp (g n)).mono_measure (Measure.restrict_mono hWn (le_refl volume)))
  refine ⟨v, hvp, ?_⟩
  apply (ACL.weak_iff_test_identity j hu (hvp.locallyIntegrableOn Fact.out)).mpr
  intro φ
  obtain ⟨n, hn⟩ := hV.cofinal φ.hasCompactSupport φ.tsupport_subset
  let ψ : TestSpace 𝕜 (V n) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hn⟩
  have hψ : (ψ : Space d → 𝕜) = φ := rfl
  have hd : (testPartialWord (V n) [j] ψ : Space d → 𝕜) = testPartialWord Ω [j] φ := by
    rw [testPartialWord_coe, hψ, testPartialWord_coe]
  have htest := (ACL.weak_iff_test_identity j (hu.mono_set (hUΩ n)) (hgloc n)).mp (hg n) ψ
  rw [hd, hψ] at htest
  refine Eq.trans ?_ htest
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' (V n).isOpen.measurableSet).mp (hvn n)] with x hx
  by_cases hxn : x ∈ (V n : Set (Space d))
  · simp only [hx hxn]
  · have hz : φ x = 0 := ψ.zero_on_compl hxn
    simp only [hz, zero_mul]

end P102.U4.DifferenceQuotient

namespace P102.U4
open DifferenceQuotient

/-- U4-05, the converse for one coordinate direction, with all local constants
retained. The derivative is constructed from the quotient hypothesis. -/
theorem difference_quotient_converse : DifferenceQuotientConverseExpected.LocalConverse := by
  intro d _hd 𝕜 _ Ω j p hp hpt u hup hbounded
  let : Fact (1 ≤ p) := ⟨hp.le⟩
  have hu : LocallyIntegrableOn u Ω volume := hup.locallyIntegrableOn hp.le
  obtain ⟨V, hV⟩ := exists_exhaustion Ω
  choose C hC using (fun n => hbounded (V n) (hV.2.1 n))
  choose g hgC hgweak using
    (fun n => (hC n).exists_local_derivative hp hpt hu (hV.2.1 n))
  obtain ⟨v, hvp, hweak⟩ := exists_derivative_of_exhaustion hV hu g hgweak
  have hv : LocallyIntegrableOn v Ω volume := hvp.locallyIntegrableOn hp.le
  refine ⟨v, hv, hvp, hweak, ?_⟩
  intro W B hW hb
  obtain ⟨w, hwB, hw⟩ := hb.exists_local_derivative hp hpt hu hW
  have hWΩ : W ≤ Ω := subset_closure.trans hW.2
  have hvW := weak_derivative_restrict hWΩ hu hv hweak
  have he := (regular_injectivity d 𝕜 W v w (hv.mono_set hWΩ)
    (domainLp_locallyIntegrable W p w)).mp (hvW.symm.trans hw)
  exact (eLpNorm_congr_ae he).le.trans hwB

/-- The common bound on an arbitrary increasing relatively compact exhaustion
controls the global derivative, without requiring u itself to be globally Lp. -/
theorem difference_quotient_converse_global : DifferenceQuotientConverseExpected.GlobalConverse := by
  intro d hd 𝕜 _ Ω j p hp hpt u V C hup hV hC
  obtain ⟨v, hv, hvp, hweak, hbound⟩ :=
    difference_quotient_converse d hd 𝕜 Ω j p hp hpt u hup
      (locallyBounded_of_exhaustion hV hC)
  obtain ⟨hmem, hn⟩ := memLp_of_exhaustion_bound hV
    (ne_of_gt (zero_lt_one.trans hp)) hpt hvp C
    (fun n => hbound (V n) C (hV.2.1 n) (hC n))
  exact ⟨v, hv, hmem, hweak, hn⟩

/-- The full source theorem: local L¹ ACL equivalence, the constant-one forward
estimate including p=1 for locally integrable u and v, with an Lp hypothesis only
on v, and the strictly interior converse and exhaustion bound. -/
theorem line_representatives_and_difference_quotients :
    DifferenceQuotientConverseExpected.FullTheorem :=
  ⟨acl_characterization, difference_quotient_estimate,
    difference_quotient_converse, difference_quotient_converse_global⟩

end P102.U4
