import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.RellichEmbeddings
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.KolmogorovRiesz
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevTranslationCharacterization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.C1DomainExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.MorreyEmbedding
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem wholeUnderlying_coe (u : SpaceValue 𝕜 d ⊤ 1 p) :
    wholeUnderlying u =ᵐ[volume] u.val (zeroIndex d 1) :=
  MemLp.coeFn_toLp _

theorem wholeUnderlying_norm (u : SpaceValue 𝕜 d ⊤ 1 p) :
    ‖wholeUnderlying u‖ = ‖u.val (zeroIndex d 1)‖ := by
  rw [wholeUnderlying, Lp.norm_toLp, Lp.norm_def]
  simp

/-- The underlying Lp class is a bounded scalar-linear projection from the
canonical derivative graph, with norm at most one. -/
def wholeUnderlyingCLM : SpaceValue 𝕜 d ⊤ 1 p →L[𝕜] Lp 𝕜 p (volume : Measure (Domain d)) :=
  LinearMap.mkContinuous
    { toFun := wholeUnderlying
      map_add' := by
        intro u v
        apply Lp.ext
        have h := Lp.coeFn_add (u.val (zeroIndex d 1)) (v.val (zeroIndex d 1))
        simp only [Opens.coe_top, Measure.restrict_univ] at h
        filter_upwards [wholeUnderlying_coe (u + v), wholeUnderlying_coe u,
          wholeUnderlying_coe v, Lp.coeFn_add (wholeUnderlying u) (wholeUnderlying v), h]
          with x huv hu hv hadd hsource
        change wholeUnderlying (u + v) x = (wholeUnderlying u + wholeUnderlying v) x
        rw [huv, hadd]
        change (u.val (zeroIndex d 1) + v.val (zeroIndex d 1)) x = _
        rw [hsource]
        simp [hu, hv]
      map_smul' := by
        intro c u
        apply Lp.ext
        have h := Lp.coeFn_smul c (u.val (zeroIndex d 1))
        simp only [Opens.coe_top, Measure.restrict_univ] at h
        filter_upwards [wholeUnderlying_coe (c • u), wholeUnderlying_coe u,
          Lp.coeFn_smul c (wholeUnderlying u), h] with x hcu hu hsmul hsource
        change wholeUnderlying (c • u) x = (c • wholeUnderlying u) x
        rw [hcu, hsmul]
        change (c • u.val (zeroIndex d 1)) x = _
        rw [hsource]
        simp [hu] }
    1 (fun u => by
      change ‖wholeUnderlying u‖ ≤ 1 * ‖u‖
      rw [one_mul, wholeUnderlying_norm]
      exact PiLp.norm_apply_le u.val _)

/-- A dimension-dependent but exponent-independent bound in the coordinate
supremum norm. Its only analytic ingredient is the accepted forward estimate. -/
theorem translation_norm_bound (u : SpaceValue 𝕜 d ⊤ 1 p) (h : Domain d) :
    ‖lpTranslation p h (wholeUnderlying u) - wholeUnderlying u‖ ≤
      (d : ℝ) ^ 2 * ‖h‖ * ‖u‖ := by
  have htrans := (measurePreserving_sub_right (volume : Measure (Domain d)) h).quasiMeasurePreserving.ae_eq_comp (wholeUnderlying_coe u)
  have heq : (lpTranslation p h (wholeUnderlying u) - wholeUnderlying u :
      Lp 𝕜 p (volume : Measure (Domain d))) =ᵐ[volume]
      (fun x => u.val (zeroIndex d 1) (x + -h) - u.val (zeroIndex d 1) x) := by
    filter_upwards [Lp.coeFn_sub (lpTranslation p h (wholeUnderlying u)) (wholeUnderlying u),
      lpTranslation_representative p h (wholeUnderlying u), wholeUnderlying_coe u,
      htrans] with x hsub ht hu htr
    simp only [Pi.sub_apply] at hsub
    change lpTranslation p h (wholeUnderlying u) x = _ at ht
    simp only [Function.comp_apply] at htr
    rw [hsub, ht, hu, htr]
    simp only [sub_eq_add_neg]
  have hg : eLpNorm (Translation.gradient u) p volume ≤
      (d : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
    have hidx (j : Fin d) : Subcritical.firstIndex j = Translation.firstIndex j := by
      apply Subtype.ext
      funext i
      rfl
    have hgEq : Subcritical.weakGradient u = Translation.gradient u := by
      funext x
      apply PiLp.ext
      intro j
      change u.val (Subcritical.firstIndex j) x = u.val (Translation.firstIndex j) x
      rw [hidx]
    rw [← hgEq]
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Subcritical.weakGradient_eLpNorm_le u
  have he : Translation.euclideanLength (-h) ≤ (d : ℝ) * ‖h‖ := by
    rw [Translation.euclideanLength_neg]
    change Morrey.euclideanNorm h ≤ _
    exact Morrey.euclideanNorm_le h
  have hB : ENNReal.ofReal (Translation.euclideanLength (-h)) *
      eLpNorm (Translation.gradient u) p volume ≤
      ENNReal.ofReal ((d : ℝ) ^ 2 * ‖h‖ * ‖u‖) := by
    calc
      _ ≤ ENNReal.ofReal ((d : ℝ) * ‖h‖) *
          ((d : ℝ≥0∞) * ENNReal.ofReal ‖u‖) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal he) hg
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2 * ‖h‖),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2),
          ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ d),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d),
          ENNReal.ofReal_natCast]
        ring
  rw [Lp.norm_def, eLpNorm_congr_ae heq]
  have hbound := (Translation.forward_estimate 𝕜 d p u (-h)).trans hB
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

/-- A norm-bounded family has a uniform translation modulus, including the
zero-dimensional and empty-family cases. -/
theorem bounded_uniformTranslationContinuous
    (A : Set (SpaceValue 𝕜 d ⊤ 1 p)) (hA : Bornology.IsBounded A) :
    KolmogorovRieszSpec.UniformTranslationContinuous p ((wholeUnderlyingCLM (𝕜 := 𝕜) (d := d) (p := p)) '' A) := by
  obtain ⟨M, hM, hbound⟩ := hA.exists_pos_norm_le
  intro ε hε
  let D : ℝ := (d : ℝ) ^ 2 * M + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨ε / D, div_pos hε hD, ?_⟩
  intro h hh f hf
  obtain ⟨u, hu, rfl⟩ := hf
  change ‖lpTranslation p h (wholeUnderlying u) - wholeUnderlying u‖ < ε
  calc
    _ ≤ (d : ℝ) ^ 2 * ‖h‖ * ‖u‖ := translation_norm_bound u h
    _ ≤ ((d : ℝ) ^ 2 * M) * ‖h‖ := by
      nlinarith [mul_le_mul_of_nonneg_left (hbound u hu)
        (mul_nonneg (sq_nonneg (d : ℝ)) (norm_nonneg h))]
    _ ≤ D * ‖h‖ := by dsimp [D]; nlinarith [norm_nonneg h]
    _ < D * (ε / D) := mul_lt_mul_of_pos_left hh hD
    _ = ε := mul_div_cancel₀ ε hD.ne'

theorem local_lp_compactness :
    Specs.ExpandedFA.Sobolev.RellichEmbeddings.LocalLpCompactness := by
  intro 𝕜 _ d p _ hp A hA s hs hsb
  have H := local_compactness d p hp ((wholeUnderlyingCLM (𝕜 := 𝕜) (d := d) (p := p)) '' A)
    ((wholeUnderlyingCLM (𝕜 := 𝕜) (d := d) (p := p)).lipschitzWith.isBounded_image hA)
    (bounded_uniformTranslationContinuous A hA) s hs hsb
  have hfun : (wholeUnderlyingCLM (𝕜 := 𝕜) (d := d) (p := p) :
      SpaceValue 𝕜 d ⊤ 1 p → Lp 𝕜 p (volume : Measure (Domain d))) =
      wholeUnderlying := rfl
  simpa only [Set.image_image, hfun] using H

/-- Compactness at the original exponent needs only an extension and the
boundedness of the target region. No support normalization is necessary. -/
theorem same_exponent : Specs.ExpandedFA.Sobolev.RellichEmbeddings.SameExponent := by
  intro 𝕜 _ d Ω hC1 hΩ p _ hp
  have hfront := hΩ.isCompact_closure.of_isClosed_subset
    isClosed_frontier frontier_subset_closure
  obtain ⟨T, E, hE, _hcompat, _hsupport⟩ :=
    C1Extension.extension_exists 𝕜 d Ω hC1 hfront
  let J : SpaceValue 𝕜 d Ω 1 p →L[𝕜] DomainLp 𝕜 Ω p :=
    ((PiLp.proj 1 (fun _ : DerivativeIndex d 1 => DomainLp 𝕜 Ω p)
      (zeroIndex d 1)).comp (derivativeGraph 𝕜 Ω 1 p).subtypeL)
  have hJ (u : SpaceValue 𝕜 d Ω 1 p) : J u = u.val (zeroIndex d 1) := rfl
  refine ⟨J, fun u => by rw [hJ], ?_⟩
  intro A hA
  have H := local_lp_compactness 𝕜 d p hp ((E p) '' A)
    ((E p).lipschitzWith.isBounded_image hA) (Ω : Set (Domain d)) Ω.isOpen.measurableSet hΩ
  have heq : (fun v : SpaceValue 𝕜 d ⊤ 1 p =>
      KolmogorovRieszSpec.LpRestrictValue p volume (Ω : Set (Domain d))
        (wholeUnderlying v)) ∘ E p = J := by
    funext u
    apply Lp.ext
    filter_upwards [lpRestrict_representative (Ω : Set (Domain d))
      (wholeUnderlying (E p u)),
      (ae_restrict_of_ae (s := (Ω : Set (Domain d))) (wholeUnderlying_coe (E p u))),
      hE p u] with x hr hw he
    exact hr.trans (hw.trans he)
  rw [Set.image_image] at H
  change IsCompact (closure (((fun v : SpaceValue 𝕜 d ⊤ 1 p =>
    KolmogorovRieszSpec.LpRestrictValue p volume (Ω : Set (Domain d))
      (wholeUnderlying v)) ∘ E p) '' A)) at H
  rw [heq] at H
  exact H

theorem compact_closure_of_subsequences {X : Type*} [MetricSpace X] {s : Set X}
    (h : ∀ u : ℕ → X, (∀ n, u n ∈ s) →
      ∃ (a : X) (σ : ℕ → ℕ), StrictMono σ ∧ Tendsto (u ∘ σ) atTop (𝓝 a)) :
    IsCompact (closure s) := by
  apply IsSeqCompact.isCompact
  intro u hu
  have happ (n : ℕ) : ∃ v ∈ s, dist (u n) v < 1 / ((n : ℝ) + 1) :=
    Metric.mem_closure_iff.mp (hu n) _ (by positivity)
  choose v hv hd using happ
  obtain ⟨a, σ, hσ, ha⟩ := h v hv
  have ht : Tendsto (fun n => dist (v n) (u n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => (dist_comm _ _).trans_le (hd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hu' := ha.congr_dist (ht.comp hσ.tendsto_atTop)
  exact ⟨a, isClosed_closure.mem_of_tendsto hu' (Eventually.of_forall (fun n => hu _)),
    σ, hσ, hu'⟩

/-- A bounded higher Lp norm gives uniform absolute continuity at a strictly
lower positive finite exponent. -/
theorem unifIntegrable_of_higher_bound {X E I : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f : I → X → E}
    {q r : ℝ≥0} (hq : 0 < q) (hqr : q < r)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hb : ∀ i, eLpNorm (f i) r μ ≤ C) :
    UnifIntegrable f q μ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqrR : (q : ℝ) < r := by exact_mod_cast hqr
  have hpow : 0 < 1 / (q : ℝ) - 1 / (r : ℝ) := by
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hqR hqrR)
  have ht := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC hpow
  apply unifIntegrable_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := ENNReal.nhds_zero_basis_Iic.eventually_iff.mp
    (ENNReal.tendsto_nhds_zero.mp ht ε hε)
  refine ⟨δ, hδ, fun i s hs => ?_⟩
  calc
    eLpNorm (f i) q (μ.restrict s) ≤ eLpNorm (f i) r (μ.restrict s) *
        (μ.restrict s) univ ^ (1 / (q : ℝ) - 1 / (r : ℝ)) := by
      simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (show (q : ℝ≥0∞) ≤ r by exact_mod_cast hqr.le) (hf i).restrict
    _ ≤ C * (μ s) ^ (1 / (q : ℝ) - 1 / (r : ℝ)) := by
      rw [Measure.restrict_apply_univ]
      gcongr
      exact (eLpNorm_restrict_le _ _ _ _).trans (hb i)
    _ ≤ ε := hbound hs

theorem lp_convergent_of_higher_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {q r : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]
    (hq : 0 < q) (hqr : q < r) (f : ℕ → Lp E q μ) (g : Lp E p μ)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hb : ∀ n, eLpNorm (f n) r μ ≤ C)
    (ht : TendstoInMeasure μ (fun n => f n) atTop g) :
    ∃ z : Lp E q μ, Tendsto f atTop (𝓝 z) := by
  have hgr : MemLp g r μ :=
   
    (eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hb) ht
      (fun n => (Lp.memLp (f n)).aestronglyMeasurable)).trans_lt (lt_top_iff_ne_top.mpr hC)
  have hgq := hgr.mono_exponent (show (q : ℝ≥0∞) ≤ r by exact_mod_cast hqr.le)
  refine ⟨hgq.toLp g, Lp.tendsto_Lp_of_tendsto_eLpNorm g hgq ?_⟩
  exact tendsto_Lp_finite_of_tendstoInMeasure Fact.out ENNReal.coe_ne_top
    (fun n => (Lp.memLp (f n)).aestronglyMeasurable) hgq
    (unifIntegrable_of_higher_bound hq hqr
      (fun n => (Lp.memLp (f n)).aestronglyMeasurable) hC hb) ht

/-- The a.e. inclusion is bounded and scalar linear whenever the analytic norm
estimate holds. -/
theorem inclusion_of_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : TopologicalSpace.Opens (Domain d)} {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] {C : ℝ≥0∞} (hC : C ≠ ∞)
    (H : ∀ u : SpaceValue 𝕜 d Ω 1 p,
      MemLp (u.val (zeroIndex d 1)) q (volume.restrict (Ω : Set (Domain d))) ∧
      eLpNorm (u.val (zeroIndex d 1)) q (volume.restrict (Ω : Set (Domain d))) ≤
        C * ENNReal.ofReal ‖u‖) :
    ∃ J : SpaceValue 𝕜 d Ω 1 p →L[𝕜] DomainLp 𝕜 Ω q,
      ∀ u, J u =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) := by
  let F (u : SpaceValue 𝕜 d Ω 1 p) : DomainLp 𝕜 Ω q := (H u).1.toLp _
  have hF (u) : F u =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1) :=
    MemLp.coeFn_toLp _
  let L : SpaceValue 𝕜 d Ω 1 p →ₗ[𝕜] DomainLp 𝕜 Ω q :=
    { toFun := F
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [hF (u + v), hF u, hF v, Lp.coeFn_add (F u) (F v),
          Lp.coeFn_add (u.val (zeroIndex d 1)) (v.val (zeroIndex d 1))]
          with x huv hu hv hsum hsrc
        change F (u + v) x = (F u + F v) x
        rw [huv, hsum]
        change (u.val (zeroIndex d 1) + v.val (zeroIndex d 1)) x = _
        rw [hsrc]
        simp [hu, hv]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [hF (c • u), hF u, Lp.coeFn_smul c (F u),
          Lp.coeFn_smul c (u.val (zeroIndex d 1))] with x hcu hu hsm hsrc
        change F (c • u) x = (c • F u) x
        rw [hcu, hsm]
        change (c • u.val (zeroIndex d 1)) x = _
        rw [hsrc]
        simp [hu] }
  refine ⟨L.mkContinuous C.toReal (fun u => ?_), hF⟩
  change ‖(H u).1.toLp _‖ ≤ _
  rw [Lp.norm_toLp]
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) (H u).2
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg u)] using hh

/-- Relative compactness in one Lp norm and a higher norm bound imply relative
compactness at every strictly intermediate finite target exponent. The base
exponent need not lie below the target. -/
theorem compact_of_higher_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : TopologicalSpace.Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    [IsFiniteMeasure (volume.restrict (Ω : Set (Domain d)))]
    (hbase : CompactLpInclusion (𝕜 := 𝕜) Ω p p)
    {q r : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]
    (hq : 1 ≤ q) (hqr : q < r) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (H : ∀ u : SpaceValue 𝕜 d Ω 1 p,
      MemLp (u.val (zeroIndex d 1)) r (volume.restrict (Ω : Set (Domain d))) ∧
      eLpNorm (u.val (zeroIndex d 1)) r (volume.restrict (Ω : Set (Domain d))) ≤
        C * ENNReal.ofReal ‖u‖) : CompactLpInclusion (𝕜 := 𝕜) Ω p q := by
  let μ : Measure (Domain d) := volume.restrict (Ω : Set (Domain d))
  let α : ℝ := 1 / (q : ℝ) - 1 / (r : ℝ)
  have hq0 : (0 : ℝ≥0) < q := lt_of_lt_of_le zero_lt_one hq
  have hα : 0 < α := one_div_lt_one_div_of_lt
    (by exact_mod_cast hq0) (by exact_mod_cast hqr) |> sub_pos.mpr
  have hfin : μ univ ^ α ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg hα.le (measure_ne_top μ univ)).ne
  obtain ⟨J, hJ⟩ := inclusion_of_bound (ENNReal.mul_ne_top hC hfin) (fun u =>
    ⟨(H u).1.mono_exponent (show (q : ℝ≥0∞) ≤ r by exact_mod_cast hqr.le), by
      calc
        eLpNorm (u.val (zeroIndex d 1)) q μ ≤
            eLpNorm (u.val (zeroIndex d 1)) r μ * μ univ ^ α := by
          simpa [α, μ] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ
            (show (q : ℝ≥0∞) ≤ r by exact_mod_cast hqr.le)
            (H u).1.aestronglyMeasurable
        _ ≤ (C * ENNReal.ofReal ‖u‖) * μ univ ^ α := by gcongr; exact (H u).2
        _ = (C * μ univ ^ α) * ENNReal.ofReal ‖u‖ := by ac_rfl⟩)
  obtain ⟨P, hP, hcompact⟩ := hbase
  refine ⟨J, hJ, fun A hA => compact_closure_of_subsequences ?_⟩
  intro f hf
  choose u hu heq using hf
  have heq' (n : ℕ) : f n = J (u n) := (heq n).symm
  obtain ⟨M, hM, hMb⟩ := hA.exists_pos_norm_le
  obtain ⟨g, hg, σ, hσ, ht⟩ := (hcompact A hA).tendsto_subseq
    (fun n => subset_closure (mem_image_of_mem P (hu n)))
  have hmeasure : TendstoInMeasure μ (fun n => f (σ n)) atTop g := by
    apply (tendstoInMeasure_of_tendsto_Lp ht).congr_left
    intro n
    exact (hP (u (σ n))).trans ((hJ (u (σ n))).symm) |>.trans
      (by rw [heq' (σ n)])
  have hbound (n : ℕ) : eLpNorm (f (σ n)) r μ ≤ C * ENNReal.ofReal M := by
    rw [heq' (σ n), eLpNorm_congr_ae (hJ _)]
    apply (H _).2.trans
    gcongr
    exact hMb _ (hu _)
  obtain ⟨z, hz⟩ := lp_convergent_of_higher_bound hq0 hqr
    (fun n => f (σ n)) g (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hbound hmeasure
  exact ⟨z, σ, hσ, hz⟩

/-- Compactness throughout the finite subcritical range. -/
theorem subcritical : Specs.ExpandedFA.Sobolev.RellichEmbeddings.Subcritical := by
  intro 𝕜 _ d Ω hC1 hΩ p q hp hpd hq hqr _ _
  letI : IsFiniteMeasure (volume.restrict (Ω : Set (Domain d))) :=
    ⟨by simpa using hΩ.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := Subcritical.bounded_domain_inequality 𝕜 d Ω hC1 hΩ p hp hpd
  exact compact_of_higher_bound (same_exponent 𝕜 d Ω hC1 hΩ p ENNReal.coe_ne_top)
    hq hqr ENNReal.coe_ne_top hC

/-- At p=d use a bounded L^(q+1) embedding, including d=p=1. -/
theorem critical : Specs.ExpandedFA.Sobolev.RellichEmbeddings.Critical := by
  intro 𝕜 _ d hd Ω hC1 hΩ q hq _ _
  letI : IsFiniteMeasure (volume.restrict (Ω : Set (Domain d))) :=
    ⟨by simpa using hΩ.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := Subcritical.critical_bounded_domain_inequality 𝕜 d hd Ω hC1 hΩ
    (q + 1) (le_add_of_nonneg_left (show 0 ≤ q from bot_le))
  exact compact_of_higher_bound (same_exponent 𝕜 d Ω hC1 hΩ d (by simp))
    hq (lt_add_one q) ENNReal.coe_ne_top hC

end ExpandedFA.Sobolev.Rellich

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d m : ℕ} {Ω : Opens (Domain d)}
  {p r : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (r : ℝ≥0∞))]
  [IsFiniteMeasure (volume.restrict (Ω : Set (Domain d)))]

def lowerExponentCLM (hr : 1 ≤ r) (hrp : r ≤ p) :
    SpaceValue 𝕜 d Ω m p →L[𝕜] SpaceValue 𝕜 d Ω m r := by
  let h : (r : ℝ≥0∞) ≤ p := by exact_mod_cast hrp
  let F := C1Extension.Transport.lowerExponent (𝕜 := 𝕜) (d := d) (m := m) (Ω := Ω) h
  have hF (u) (α : DerivativeIndex d m) : (F u).val α =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val α :=
    C1Extension.Transport.lowerExponent_coe h u α
  let L : SpaceValue 𝕜 d Ω m p →ₗ[𝕜] SpaceValue 𝕜 d Ω m r :=
    { toFun := F
      map_add' := by
        intro u v
        apply Subtype.ext
        apply PiLp.ext
        intro α
        apply Lp.ext
        filter_upwards [hF (u + v) α, hF u α, hF v α,
          Lp.coeFn_add ((F u).val α) ((F v).val α),
          Lp.coeFn_add (u.val α) (v.val α)] with x huv hu hv hsum hsrc
        change (F (u + v)).val α x = ((F u).val α + (F v).val α) x
        rw [huv, hsum]
        change (u.val α + v.val α) x = _
        rw [hsrc]
        simp [hu, hv]
      map_smul' := by
        intro c u
        apply Subtype.ext
        apply PiLp.ext
        intro α
        apply Lp.ext
        filter_upwards [hF (c • u) α, hF u α,
          Lp.coeFn_smul c ((F u).val α), Lp.coeFn_smul c (u.val α)] with x hcu hu hsm hsrc
        change (F (c • u)).val α x = (c • (F u).val α) x
        rw [hcu, hsm]
        change (c • u.val α) x = _
        rw [hsrc]
        simp [hu] }
  let C := (volume.restrict (Ω : Set (Domain d))) univ ^ (1/(r : ℝ) - 1/(p : ℝ))
  have hr0 : (0 : ℝ) < r := by exact_mod_cast lt_of_lt_of_le zero_lt_one hr
  have hC : C ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg
    (sub_nonneg.mpr (one_div_le_one_div_of_le hr0 (by exact_mod_cast hrp)))
    (measure_ne_top _ _)).ne
  refine L.mkContinuous C.toReal (fun u => ?_)
  have hb := Subcritical.lowerExponent_eNorm_le h u
  have hb' : ENNReal.ofReal ‖F u‖ ≤ ENNReal.ofReal ‖u‖ * C := by
    simpa only [ENNReal.coe_toReal] using hb
  change ‖F u‖ ≤ _
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC) hb'
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), mul_comm] using hh

theorem lowerExponentCLM_coe (hr : 1 ≤ r) (hrp : r ≤ p)
    (u : SpaceValue 𝕜 d Ω m p) (α : DerivativeIndex d m) :
    (lowerExponentCLM hr hrp u).val α =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val α :=
  C1Extension.Transport.lowerExponent_coe (q := (r : ℝ≥0∞)) (by exact_mod_cast hrp) u α

def lowerZeroExponentCLM (hr : 1 ≤ r) (hrp : r ≤ p) :
    ZeroSpaceValue 𝕜 d Ω m p ENNReal.coe_ne_top →L[𝕜]
      ZeroSpaceValue 𝕜 d Ω m r ENNReal.coe_ne_top := by
  let L := lowerExponentCLM (𝕜 := 𝕜) (d := d) (m := m) (Ω := Ω) hr hrp
  have hmaps : MapsTo L (SmoothMembers 𝕜 d Ω m p) (SmoothMembers 𝕜 d Ω m r) := by
    rintro u ⟨φ, hφ⟩
    exact ⟨φ, (lowerExponentCLM_coe hr hrp u _).trans hφ⟩
  refine (L.comp (ZeroSpaceValue 𝕜 d Ω m p ENNReal.coe_ne_top).subtypeL).codRestrict
    (ZeroSpaceValue 𝕜 d Ω m r ENNReal.coe_ne_top) (fun u => ?_)
  exact hmaps.closure L.continuous u.property
end ExpandedFA.Sobolev.Rellich

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
theorem zero_inclusion_of_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : TopologicalSpace.Opens (Domain d)} {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ∞) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (H : ∀ u : ZeroSpaceValue 𝕜 d Ω 1 p hp,
      MemLp (u.val.val (zeroIndex d 1)) q (volume.restrict (Ω : Set (Domain d))) ∧
      eLpNorm (u.val.val (zeroIndex d 1)) q (volume.restrict (Ω : Set (Domain d))) ≤
        C * ENNReal.ofReal ‖u‖) :
    ∃ J : ZeroSpaceValue 𝕜 d Ω 1 p hp →L[𝕜] DomainLp 𝕜 Ω q,
      ∀ u, J u =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val.val (zeroIndex d 1) := by
  let F (u : ZeroSpaceValue 𝕜 d Ω 1 p hp) : DomainLp 𝕜 Ω q := (H u).1.toLp _
  have hF (u) : F u =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val.val (zeroIndex d 1) :=
    MemLp.coeFn_toLp _
  let L : ZeroSpaceValue 𝕜 d Ω 1 p hp →ₗ[𝕜] DomainLp 𝕜 Ω q :=
    { toFun := F
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [hF (u + v), hF u, hF v, Lp.coeFn_add (F u) (F v),
          Lp.coeFn_add (u.val.val (zeroIndex d 1)) (v.val.val (zeroIndex d 1))]
          with x huv hu hv hsum hsrc
        change F (u + v) x = (F u + F v) x
        rw [huv, hsum]
        change (u.val.val (zeroIndex d 1) + v.val.val (zeroIndex d 1)) x = _
        rw [hsrc]
        simp [hu, hv]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [hF (c • u), hF u, Lp.coeFn_smul c (F u),
          Lp.coeFn_smul c (u.val.val (zeroIndex d 1))] with x hcu hu hsm hsrc
        change F (c • u) x = (c • F u) x
        rw [hcu, hsm]
        change (c • u.val.val (zeroIndex d 1)) x = _
        rw [hsrc]
        simp [hu] }
  refine ⟨L.mkContinuous C.toReal (fun u => ?_), hF⟩
  change ‖(H u).1.toLp _‖ ≤ _
  rw [Lp.norm_toLp]
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) (H u).2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg u)] at hh
  exact hh

/-- Relative compactness in one Lp norm and a higher norm bound imply relative
compactness at every strictly intermediate finite target exponent. The base
exponent need not lie below the target. -/
theorem compact_zero_of_higher_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : TopologicalSpace.Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    [IsFiniteMeasure (volume.restrict (Ω : Set (Domain d)))]
    (hbase : CompactZeroLpInclusion (𝕜 := 𝕜) Ω p hp p)
    {q r : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]
    (hq : 1 ≤ q) (hqr : q < r) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (H : ∀ u : ZeroSpaceValue 𝕜 d Ω 1 p hp,
      MemLp (u.val.val (zeroIndex d 1)) r (volume.restrict (Ω : Set (Domain d))) ∧
      eLpNorm (u.val.val (zeroIndex d 1)) r (volume.restrict (Ω : Set (Domain d))) ≤
        C * ENNReal.ofReal ‖u‖) : CompactZeroLpInclusion (𝕜 := 𝕜) Ω p hp q := by
  let μ : Measure (Domain d) := volume.restrict (Ω : Set (Domain d))
  let α : ℝ := 1 / (q : ℝ) - 1 / (r : ℝ)
  have hq0 : (0 : ℝ≥0) < q := lt_of_lt_of_le zero_lt_one hq
  have hα : 0 < α := one_div_lt_one_div_of_lt
    (by exact_mod_cast hq0) (by exact_mod_cast hqr) |> sub_pos.mpr
  have hfin : μ univ ^ α ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg hα.le (measure_ne_top μ univ)).ne
  obtain ⟨J, hJ⟩ := zero_inclusion_of_bound hp (ENNReal.mul_ne_top hC hfin) (fun u =>
    ⟨(H u).1.mono_exponent (show (q : ℝ≥0∞) ≤ r by exact_mod_cast hqr.le), by
      calc
        eLpNorm (u.val.val (zeroIndex d 1)) q μ ≤
            eLpNorm (u.val.val (zeroIndex d 1)) r μ * μ univ ^ α := by
          simpa [α, μ] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ
            (show (q : ℝ≥0∞) ≤ r by exact_mod_cast hqr.le)
            (H u).1.aestronglyMeasurable
        _ ≤ (C * ENNReal.ofReal ‖u‖) * μ univ ^ α := by gcongr; exact (H u).2
        _ = (C * μ univ ^ α) * ENNReal.ofReal ‖u‖ := by ac_rfl⟩)
  obtain ⟨P, hP, hcompact⟩ := hbase
  refine ⟨J, hJ, fun A hA => compact_closure_of_subsequences ?_⟩
  intro f hf
  choose u hu heq using hf
  have heq' (n : ℕ) : f n = J (u n) := (heq n).symm
  obtain ⟨M, hM, hMb⟩ := hA.exists_pos_norm_le
  obtain ⟨g, hg, σ, hσ, ht⟩ := (hcompact A hA).tendsto_subseq
    (fun n => subset_closure (mem_image_of_mem P (hu n)))
  have hmeasure : TendstoInMeasure μ (fun n => f (σ n)) atTop g := by
    apply (tendstoInMeasure_of_tendsto_Lp ht).congr_left
    intro n
    exact (hP (u (σ n))).trans ((hJ (u (σ n))).symm) |>.trans
      (by rw [heq' (σ n)])
  have hbound (n : ℕ) : eLpNorm (f (σ n)) r μ ≤ C * ENNReal.ofReal M := by
    rw [heq' (σ n), eLpNorm_congr_ae (hJ _)]
    apply (H _).2.trans
    gcongr
    exact hMb _ (hu _)
  obtain ⟨z, hz⟩ := lp_convergent_of_higher_bound hq0 hqr
    (fun n => f (σ n)) g (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hbound hmeasure
  exact ⟨z, σ, hσ, hz⟩


end ExpandedFA.Sobolev.Rellich

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Zero extension on derivative tuples, without a premature graph claim. -/
def zeroTuple : SpaceValue 𝕜 d Ω 1 p →L[𝕜] DerivativeTuple 𝕜 (d := d) ⊤ 1 p :=
  LinearMap.mkContinuous
    { toFun := fun u => WithLp.toLp 1 (fun α => C1Extension.zeroLp ⊤ (u.val α))
      map_add' := by
        intro u v
        apply PiLp.ext
        intro α
        exact (C1Extension.zeroLpLM ⊤).map_add _ _
      map_smul' := by
        intro c u
        apply PiLp.ext
        intro α
        exact (C1Extension.zeroLpLM ⊤).map_smul c _ }
    1 (fun u => by
      change ‖WithLp.toLp 1 (fun α => C1Extension.zeroLp ⊤ (u.val α))‖ ≤ 1 * ‖u.val‖
      rw [one_mul, PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
      exact le_of_eq (Finset.sum_congr rfl (fun α _ => C1Extension.zeroLp_norm le_top _)))

theorem zeroTuple_test (φ : Tests 𝕜 Ω) :
    zeroTuple (testToSobolev (p := p) 1 φ) =
      (testToSobolev (p := p) 1 (C1Extension.enlargeTest le_top φ)).val := by
  apply PiLp.ext
  intro α
  apply Lp.ext
  let ψ := testPartialCLM (multiIndexWord (natIndex α)).reverse φ
  change C1Extension.zeroLp ⊤ (testToDomainLp (p := p) ψ) =ᵐ[_]
    testToDomainLp (p := p) (testPartialCLM (multiIndexWord (natIndex α)).reverse
      (C1Extension.enlargeTest le_top φ))
  rw [← C1Extension.enlargeTest_partial]
  have hψ := (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).mp
    (testToDomainLp_coe (p := p) ψ)
  have hψ' : (Ω : Set (Domain d)).indicator ψ = (ψ : Domain d → 𝕜) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · simp [hx, ψ.zero_on_compl hx]
  rw [hψ'] at hψ
  filter_upwards [C1Extension.zeroLp_coe (Λ := ⊤) (testToDomainLp (p := p) ψ),
    hψ.filter_mono (ae_mono Measure.restrict_le_self),
    testToDomainLp_coe (p := p) (C1Extension.enlargeTest le_top ψ)] with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

theorem zeroTuple_mem (hp : p ≠ ∞) (u : ZeroSpaceValue 𝕜 d Ω 1 p hp) :
    zeroTuple u.val ∈ derivativeGraph 𝕜 (d := d) ⊤ 1 p := by
  have hc : IsClosed ((zeroTuple (𝕜 := 𝕜) (Ω := Ω) (p := p)) ⁻¹'
      (derivativeGraph 𝕜 (d := d) ⊤ 1 p : Set _)) :=
    Smoothing.derivativeGraph_isClosed.preimage zeroTuple.continuous
  apply closure_minimal (t := (zeroTuple (𝕜 := 𝕜) (Ω := Ω) (p := p)) ⁻¹'
      (derivativeGraph 𝕜 (d := d) ⊤ 1 p : Set _)) ?_ hc u.property
  rintro v ⟨φ, hφ⟩
  have hv : v = testToSobolev (p := p) 1 φ := by
    apply sobolev_underlying_injective 𝕜 d Ω 1 p
    change v.val (zeroIndex d 1) = (testToSobolev (p := p) 1 φ).val (zeroIndex d 1)
    rw [testToSobolev_underlying]
    exact Lp.ext (hφ.trans (testToDomainLp_coe φ).symm)
  rw [hv, mem_preimage, zeroTuple_test]
  exact (testToSobolev (p := p) 1 (C1Extension.enlargeTest le_top φ)).property

/-- Canonical zero extension, first proved on tests and then on their closure. -/
def zeroSobolev (hp : p ≠ ∞) :
    ZeroSpaceValue 𝕜 d Ω 1 p hp →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p :=
  ((zeroTuple (𝕜 := 𝕜) (Ω := Ω) (p := p)).comp
    (ZeroSpaceValue 𝕜 d Ω 1 p hp).subtypeL).codRestrict
      (derivativeGraph 𝕜 (d := d) ⊤ 1 p) (zeroTuple_mem hp)

theorem zeroSobolev_coe (hp : p ≠ ∞) (u : ZeroSpaceValue 𝕜 d Ω 1 p hp)
    (α : DerivativeIndex d 1) :
    (zeroSobolev hp u).val α =ᵐ[volume]
      (Ω : Set (Domain d)).indicator (u.val.val α) := by
  change C1Extension.zeroLp ⊤ (u.val.val α) =ᵐ[volume] _
  simpa using C1Extension.zeroLp_coe (Λ := ⊤) (u.val.val α)

theorem zeroSobolev_norm (hp : p ≠ ∞) (u : ZeroSpaceValue 𝕜 d Ω 1 p hp) :
    ‖zeroSobolev hp u‖ = ‖u‖ := by
  change ‖WithLp.toLp 1 (fun α => C1Extension.zeroLp ⊤ (u.val.val α))‖ = ‖u.val.val‖
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  exact Finset.sum_congr rfl (fun α _ => C1Extension.zeroLp_norm le_top _)

theorem zero_same_exponent (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    (hp : p ≠ ∞) : CompactZeroLpInclusion (𝕜 := 𝕜) Ω p hp p := by
  let E : ZeroSpaceValue 𝕜 d Ω 1 p hp →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p :=
    zeroSobolev hp
  let J : ZeroSpaceValue 𝕜 d Ω 1 p hp →L[𝕜] DomainLp 𝕜 Ω p :=
    (((PiLp.proj 1 (fun _ : DerivativeIndex d 1 => DomainLp 𝕜 Ω p)
      (zeroIndex d 1)).comp (derivativeGraph 𝕜 Ω 1 p).subtypeL).comp
        (ZeroSpaceValue 𝕜 d Ω 1 p hp).subtypeL)
  have hJ (u : ZeroSpaceValue 𝕜 d Ω 1 p hp) : J u = u.val.val (zeroIndex d 1) := rfl
  refine ⟨J, fun u => by rw [hJ], ?_⟩
  intro A hA
  have hEA : Bornology.IsBounded (E '' A) := by
    obtain ⟨M, hM⟩ := hA.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact (zeroSobolev_norm hp u).trans_le (hM u hu)
  have H := local_lp_compactness 𝕜 d p hp (E '' A)
    hEA (Ω : Set (Domain d)) Ω.isOpen.measurableSet hΩ
  have heq : (fun v : SpaceValue 𝕜 d ⊤ 1 p =>
      KolmogorovRieszSpec.LpRestrictValue p volume (Ω : Set (Domain d))
        (wholeUnderlying v)) ∘ E = J := by
    funext u
    apply Lp.ext
    filter_upwards [lpRestrict_representative (Ω : Set (Domain d))
      (wholeUnderlying (E u)),
      (ae_restrict_of_ae (s := (Ω : Set (Domain d))) (wholeUnderlying_coe (E u))),
      (ae_restrict_of_ae (s := (Ω : Set (Domain d)))
        (zeroSobolev_coe hp u (zeroIndex d 1))),
      ae_restrict_mem Ω.isOpen.measurableSet] with x hr hw he hx
    exact hr.trans (hw.trans (he.trans (Set.indicator_of_mem hx _)))
  rw [Set.image_image] at H
  change IsCompact (closure (((fun v : SpaceValue 𝕜 d ⊤ 1 p =>
    KolmogorovRieszSpec.LpRestrictValue p volume (Ω : Set (Domain d))
      (wholeUnderlying v)) ∘ E) '' A)) at H
  rw [heq] at H
  exact H
end ExpandedFA.Sobolev.Rellich

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma norm_le_of_ae_bound {α : Type} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (hμ : μ ≠ 0) (g : Lp 𝕜 p μ) (z : 𝕜) (K : ℝ)
    (hb : ∀ᵐ y ∂μ, ‖z‖ ≤ ‖g y‖ + K) :
    ‖z‖ ≤ ‖g‖ / (μ univ ^ (1 / p.toReal)).toReal + K := by
  let b : ℝ := (μ univ ^ (1 / p.toReal)).toReal
  have hbpos : 0 < b := by
    dsimp [b]
    apply ENNReal.toReal_pos
    · simp [ENNReal.rpow_eq_zero_iff, Measure.measure_univ_ne_zero.mpr hμ, measure_ne_top μ _]
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ _)
  by_cases hc : 0 ≤ ‖z‖ - K
  · have hmono : eLpNorm (fun _ : α => ‖z‖ - K) p μ ≤ eLpNorm g p μ :=
      eLpNorm_mono_ae aestronglyMeasurable_const (hb.mono fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg hc]
        linarith)
    have ht := ENNReal.toReal_mono (Lp.memLp g).ne hmono
    rw [eLpNorm_const _ (ne_of_gt (zero_lt_one.trans_le Fact.out)) hμ,
      ENNReal.toReal_mul] at ht
    change |‖z‖ - K| * b ≤ ‖g‖ at ht
    rw [abs_of_nonneg hc] at ht
    have : ‖z‖ - K ≤ ‖g‖ / b := (le_div_iff₀ hbpos).mpr ht
    linarith
  · have hn : 0 ≤ ‖g‖ / b := div_nonneg (norm_nonneg _) hbpos.le
    change ‖z‖ ≤ ‖g‖ / b + K
    linarith


theorem supercritical_representative_clm
    (Ω : Opens (Domain d)) (hC1 : C1Extension.IsC1Domain Ω)
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    (hdp : (d : ℝ≥0∞) < p) :
    letI : CompactSpace (closure (Ω : Set (Domain d))) :=
      isCompact_iff_compactSpace.mp hΩ.isCompact_closure
    ∃ J : SpaceValue 𝕜 d Ω 1 p →L[𝕜] C(closure (Ω : Set (Domain d)), 𝕜),
      (∀ u, ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))),
        ∃ hx : x ∈ closure (Ω : Set (Domain d)),
          J u ⟨x, hx⟩ = u.val (zeroIndex d 1) x) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u x y,
        ‖J u x - J u y‖ ≤ C * ‖u‖ * Morrey.euclideanNorm (x.val - y.val) ^ Morrey.exponent d p := by
  classical
  letI : CompactSpace (closure (Ω : Set (Domain d))) :=
    isCompact_iff_compactSpace.mp hΩ.isCompact_closure
  obtain ⟨C, hC, hmor⟩ := Morrey.c1_domains 𝕜 d Ω hC1
    (hΩ.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure) p hdp
  choose f hf hrep hbound using hmor
  let F : SpaceValue 𝕜 d Ω 1 p → C(closure (Ω : Set (Domain d)), 𝕜) :=
    fun u => ⟨fun x => f u x.val, (hf u).comp continuous_subtype_val⟩
  have hFadd : ∀ u v, F (u + v) = F u + F v := by
    intro u v
    have hrepadd : Morrey.Represents (u + v) (fun x => f u x + f v x) := by
      filter_upwards [Lp.coeFn_add (u.val (zeroIndex d 1)) (v.val (zeroIndex d 1)),
        hrep u, hrep v] with x hx hu hv
      change (u.val (zeroIndex d 1) + v.val (zeroIndex d 1)) x = _
      simpa only [Pi.add_apply, hu, hv] using hx
    ext x
    exact Morrey.representative_unique (u + v) _ _ (hf _) ((hf u).add (hf v))
      (hrep _) hrepadd x.property
  have hFsmul : ∀ (c : 𝕜) u, F (c • u) = c • F u := by
    intro c u
    have hrepsmul : Morrey.Represents (c • u) (fun x => c • f u x) := by
      filter_upwards [Lp.coeFn_smul c (u.val (zeroIndex d 1)), hrep u] with x hx hu
      change (c • u.val (zeroIndex d 1)) x = _
      simpa only [Pi.smul_apply, hu] using hx
    ext x
    exact Morrey.representative_unique (c • u) _ _ (hf _) ((hf u).const_smul c)
      (hrep _) hrepsmul x.property
  let L : SpaceValue 𝕜 d Ω 1 p →ₗ[𝕜] C(closure (Ω : Set (Domain d)), 𝕜) :=
    { toFun := F, map_add' := hFadd, map_smul' := hFsmul }
  have hLbound : ∃ M : ℝ, ∀ u, ‖L u‖ ≤ M * ‖u‖ := by
    by_cases hne : (Ω : Set (Domain d)).Nonempty
    · let μ := volume.restrict (Ω : Set (Domain d))
      letI : IsFiniteMeasure μ := ⟨by
        dsimp [μ]
        simpa using hΩ.measure_lt_top⟩
      have hμ : μ ≠ 0 := by
        simpa [μ, Measure.restrict_eq_zero] using Ω.isOpen.measure_ne_zero (μ := volume) hne
      obtain ⟨R, hR, hnorm⟩ := hΩ.closure.exists_pos_norm_le
      let D : ℝ := C * ((d : ℝ) * (2 * R)) ^ Morrey.exponent d p
      have hD : 0 ≤ D := mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
      let b : ℝ := (μ univ ^ (1 / p.toReal)).toReal
      have hbpos : 0 < b := by
        dsimp [b]
        apply ENNReal.toReal_pos
        · simp [ENNReal.rpow_eq_zero_iff, Measure.measure_univ_ne_zero.mpr hμ, measure_ne_top μ _]
        · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ _)
      refine ⟨1 / b + D, fun u => (ContinuousMap.norm_le _ (by positivity)).mpr (fun x => ?_)⟩
      have hpoint : ∀ᵐ y ∂μ, ‖f u x.val‖ ≤ ‖u.val (zeroIndex d 1) y‖ + D * ‖u‖ := by
        filter_upwards [self_mem_ae_restrict Ω.isOpen.measurableSet, hrep u] with y hy hfy
        have hdist : Morrey.euclideanNorm (x.val - y) ≤ (d : ℝ) * (2 * R) :=
          (Morrey.euclideanNorm_le _).trans (mul_le_mul_of_nonneg_left
            ((norm_sub_le x.val y).trans (by
              have hxR := hnorm x.val x.property
              have hyR := hnorm y (subset_closure hy)
              linarith)) (Nat.cast_nonneg _))
        have hd := (hbound u x.val x.property y (subset_closure hy)).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hdist (Morrey.exponent_pos hdp).le)
            (mul_nonneg hC (norm_nonneg u)))
        calc
          ‖f u x.val‖ ≤ ‖f u x.val - f u y‖ + ‖f u y‖ := by simpa only [add_comm] using norm_le_insert' (f u x.val) (f u y)
          _ ≤ C * ‖u‖ * ((d : ℝ) * (2 * R)) ^ Morrey.exponent d p + ‖f u y‖ := by linarith [hd]
          _ = _ := by rw [← hfy]; dsimp [D]; ring
      have hx := norm_le_of_ae_bound μ hμ (u.val (zeroIndex d 1)) (f u x.val) (D * ‖u‖) hpoint
      change ‖f u x.val‖ ≤ _
      calc
        _ ≤ ‖u.val (zeroIndex d 1)‖ / b + D * ‖u‖ := hx
        _ ≤ ‖u‖ / b + D * ‖u‖ := by
          have hn : ‖u.val (zeroIndex d 1)‖ ≤ ‖u‖ := PiLp.norm_apply_le u.val _
          have hh := div_le_div_of_nonneg_right hn hbpos.le
          linarith
        _ = _ := by ring
    · have hΩempty : (Ω : Set (Domain d)) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      refine ⟨0, fun u => ?_⟩
      apply (ContinuousMap.norm_le _ (by simp)).mpr
      intro x
      simpa [hΩempty] using x.property
  obtain ⟨M, hM⟩ := hLbound
  let J := L.mkContinuous M hM
  refine ⟨J, fun u => ?_, C, hC, fun u x y => hbound u x.val x.property y.val y.property⟩
  filter_upwards [self_mem_ae_restrict Ω.isOpen.measurableSet, hrep u] with x hx hfx
  exact ⟨subset_closure hx, hfx.symm⟩



theorem supercritical : Specs.ExpandedFA.Sobolev.RellichEmbeddings.Supercritical := by
  intro 𝕜 _ d Ω hC1 hΩ p _ hdp
  letI : CompactSpace (closure (Ω : Set (Domain d))) :=
    isCompact_iff_compactSpace.mp hΩ.isCompact_closure
  obtain ⟨J, hrep, C, hC, hbound⟩ := supercritical_representative_clm (𝕜 := 𝕜) Ω hC1 hΩ hdp
  refine ⟨J, hrep, fun A hA => ?_⟩
  obtain ⟨M, hM, hnorm⟩ := hA.exists_pos_norm_le
  let e := ContinuousMap.isometryEquivBoundedOfCompact (closure (Ω : Set (Domain d))) 𝕜
  let B := e '' (J '' A)
  have heq : Equicontinuous ((↑) : B → (closure (Ω : Set (Domain d))) → 𝕜) := by
    intro x
    let b : (closure (Ω : Set (Domain d))) → ℝ := fun y =>
      C * M * Morrey.euclideanNorm (x.val - y.val) ^ Morrey.exponent d p
    have hb : Continuous b := continuous_const.mul
      ((Morrey.euclideanNorm_continuous.comp (continuous_const.sub continuous_subtype_val)).rpow_const
        (fun _ => Or.inr (Morrey.exponent_pos hdp).le))
    have hblim : Tendsto b (𝓝 x) (𝓝 0) := by
      have hx : b x = 0 := by simp [b, Morrey.euclideanNorm, (Morrey.exponent_pos hdp).ne']
      simpa only [hx] using hb.tendsto x
    apply Metric.equicontinuousAt_of_continuity_modulus b hblim
    apply Eventually.of_forall
    intro y g
    rcases g.property with ⟨v, ⟨u, hu, hv⟩, hg⟩
    change dist (g.val x) (g.val y) ≤ b y
    rw [← hg, ← hv]
    change dist (J u x) (J u y) ≤ b y
    rw [dist_eq_norm]
    exact (hbound u x y).trans (by
      dsimp [b]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hnorm u hu) hC) (Real.rpow_nonneg (norm_nonneg _) _))
  have hrange : ∀ (g : BoundedContinuousFunction (closure (Ω : Set (Domain d))) 𝕜) (x : closure (Ω : Set (Domain d))),
      g ∈ B → g x ∈ Metric.closedBall (0 : 𝕜) (‖J‖ * M) := by
    intro g x hg
    rcases hg with ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    change J u x ∈ Metric.closedBall (0 : 𝕜) (‖J‖ * M)
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact ((J u).norm_coe_le_norm x).trans ((J.le_opNorm u).trans
      (mul_le_mul_of_nonneg_left (hnorm u hu) (norm_nonneg J)))
  have hcomp : IsCompact (closure B) := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : 𝕜) (‖J‖ * M)) (isCompact_closedBall _ _) B hrange heq
  have hcomp' := hcomp.image e.symm.continuous
  have he : e.symm '' closure B = closure (J '' A) := by
    change e.toHomeomorph.symm '' closure B = _
    rw [e.toHomeomorph.symm.image_closure]
    congr 1
    dsimp [B]
    exact e.toEquiv.symm.image_symm_image _
  rwa [he] at hcomp'

end ExpandedFA.Sobolev.Rellich

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

theorem zeroSobolev_restrict_coe {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (u : ZeroSpaceValue 𝕜 d Ω 1 p hp)
    (α : DerivativeIndex d 1) :
    (zeroSobolev hp u).val α =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val.val α := by
  filter_upwards [ae_restrict_of_ae (s := (Ω : Set (Domain d))) (zeroSobolev_coe hp u α),
    ae_restrict_mem Ω.isOpen.measurableSet] with x he hx
  exact he.trans (Set.indicator_of_mem hx _)

/-- The homogeneous whole-space inequality applies to zero extensions on every open set. -/
theorem zero_subcritical_bound (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0) (hp : 1 ≤ p) (hpd : p < d) [Fact (1 ≤ (p : ℝ≥0∞))] :
    ∃ C : ℝ≥0, ∀ u : ZeroSpaceValue 𝕜 d Ω 1 p ENNReal.coe_ne_top,
      MemLp (u.val.val (zeroIndex d 1)) (Subcritical.criticalExponent d p)
        (volume.restrict (Ω : Set (Domain d))) ∧
      eLpNorm (u.val.val (zeroIndex d 1)) (Subcritical.criticalExponent d p)
        (volume.restrict (Ω : Set (Domain d))) ≤ (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
  obtain ⟨C, hC⟩ := Subcritical.whole_space_inequality d p hp hpd
  refine ⟨C * d, fun u => ?_⟩
  let v := zeroSobolev ENNReal.coe_ne_top u
  have heq := zeroSobolev_restrict_coe ENNReal.coe_ne_top u (zeroIndex d 1)
  have hv := hC 𝕜 v
  have hmem : MemLp (u.val.val (zeroIndex d 1)) (Subcritical.criticalExponent d p)
      (volume.restrict (Ω : Set (Domain d))) := (hv.1.restrict (Ω : Set (Domain d))).ae_eq heq
  refine ⟨hmem, ?_⟩
  calc
    _ = eLpNorm (v.val (zeroIndex d 1)) (Subcritical.criticalExponent d p)
        (volume.restrict (Ω : Set (Domain d))) := eLpNorm_congr_ae heq.symm
    _ ≤ eLpNorm (v.val (zeroIndex d 1)) (Subcritical.criticalExponent d p) volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ C * eLpNorm (Subcritical.weakGradient v) p volume := hv.2
    _ ≤ C * ((d : ℝ≥0∞) * ENNReal.ofReal ‖v‖) := by
      gcongr
      simpa only [Opens.coe_top, Measure.restrict_univ] using Subcritical.weakGradient_eLpNorm_le v
    _ = (C * d : ℝ≥0) * ENNReal.ofReal ‖u‖ := by
      rw [zeroSobolev_norm]
      simp only [ENNReal.coe_mul, ENNReal.coe_natCast]
      ac_rfl

theorem zero_subcritical : Specs.ExpandedFA.Sobolev.RellichEmbeddings.ZeroSubcritical := by
  intro 𝕜 _ d Ω hΩ p q hp hpd hq hqr _ _
  letI : IsFiniteMeasure (volume.restrict (Ω : Set (Domain d))) :=
    ⟨by simpa using hΩ.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := zero_subcritical_bound 𝕜 d Ω p hp hpd
  exact compact_zero_of_higher_bound ENNReal.coe_ne_top (zero_same_exponent hΩ ENNReal.coe_ne_top)
    hq hqr ENNReal.coe_ne_top hC
end ExpandedFA.Sobolev.Rellich

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
theorem zero_one_bound
    (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Domain 1))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain 1)))
    (q : ℝ≥0) (_hq : 1 ≤ q) :
    ∃ C : ℝ≥0, ∀ [Fact (1 ≤ (1 : ℝ≥0∞))] (u : ZeroSpaceValue 𝕜 1 Ω 1 1 (by simp)),
      MemLp (u.val.val (zeroIndex 1 1)) q (volume.restrict (Ω : Set (Domain 1))) ∧
      eLpNorm (u.val.val (zeroIndex 1 1)) q (volume.restrict (Ω : Set (Domain 1))) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  let E : ZeroSpaceValue 𝕜 1 Ω 1 1 (by simp) →L[𝕜] SpaceValue 𝕜 1 ⊤ 1 1 :=
    zeroSobolev (by simp)
  have hE (u : ZeroSpaceValue 𝕜 1 Ω 1 1 (by simp)) :
      (E u).val (zeroIndex 1 1) =ᵐ[volume.restrict (Ω : Set (Domain 1))]
        u.val.val (zeroIndex 1 1) := by
    filter_upwards [ae_restrict_of_ae (s := (Ω : Set (Domain 1)))
      (zeroSobolev_coe (by simp) u (zeroIndex 1 1)), ae_restrict_mem Ω.isOpen.measurableSet]
      with x he hx
    exact he.trans (Set.indicator_of_mem hx _)
  obtain ⟨r, hr, hball⟩ := hΩ.subset_ball_lt 1 (0 : Domain 1)
  let I : Opens ℝ := ⟨Set.Ioo (-r) r, isOpen_Ioo⟩
  have hΩI : Ω ≤ OneDimensional.lineDomain I := by
    intro x hx
    have hxnorm : ‖x‖ < r := by simpa using hball hx
    have hxcoord : |x 0| < r := by simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm x 0).trans_lt hxnorm
    exact abs_lt.mp hxcoord
  have hrr : -r < r := by linarith
  have hμ : volume (Ω : Set (Domain 1)) ≠ ∞ :=
    (measure_mono (s := (Ω : Set (Domain 1))) subset_closure).trans_lt
      hΩ.isCompact_closure.measure_lt_top |>.ne
  let A : ℝ≥0∞ := volume (Ω : Set (Domain 1)) ^ (1 / (q : ℝ))
  have hA : A ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hμ
  refine ⟨2 * A.toNNReal, ?_⟩
  intro _ u
  let v : OneDimensional.W1p 𝕜 I 1 := C1Extension.restrictSobolev le_top (E u)
  obtain ⟨f, hf⟩ := OneDimensional.representative_existence 𝕜 I Set.ordConnected_Ioo 1 v
  have hvinfty := OneDimensional.finite_interval_essential_supremum 𝕜 (-r) r hrr 1 v f hf
  have hbase : ‖OneDimensional.baseLp v‖ ≤ ‖v‖ := PiLp.norm_apply_le v.val _
  have hder : ‖OneDimensional.derivativeLp v‖ ≤ ‖v‖ := PiLp.norm_apply_le v.val _
  have hlen : (r - -r)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr (by linarith)
  have hvreal : (r - -r) ^ (-OneDimensional.reciprocalExponent 1) *
        ‖OneDimensional.baseLp v‖ + (r - -r) ^
        (1 - OneDimensional.reciprocalExponent 1) * ‖OneDimensional.derivativeLp v‖ ≤
        2 * ‖u‖ := by
    simp only [OneDimensional.reciprocalExponent, ENNReal.toReal_one, div_one,
      Real.rpow_neg_one, sub_self, Real.rpow_zero, one_mul]
    calc
      (r - -r)⁻¹ * ‖OneDimensional.baseLp v‖ + ‖OneDimensional.derivativeLp v‖ ≤
          ‖v‖ + ‖v‖ := by
        apply add_le_add _ hder
        exact (mul_le_mul_of_nonneg_right hlen (norm_nonneg _)).trans (by simpa using hbase)
      _ ≤ 2 * ‖u‖ := by
        have hvnorm := C1Extension.restrictSobolev_norm_le (le_top : OneDimensional.lineDomain I ≤ ⊤) (E u)
        have hEnorm := zeroSobolev_norm (by simp) u
        dsimp [v, E] at *
        nlinarith
  have hrestr : (OneDimensional.baseLp v : Domain 1 → 𝕜) =ᵐ[volume.restrict (Ω : Set (Domain 1))]
      (E u).val (zeroIndex 1 1) :=
    (C1Extension.restrictSobolev_coe le_top (E u) (zeroIndex 1 1)).filter_mono
      (ae_mono (Measure.restrict_mono hΩI le_rfl))
  have huinfty : eLpNorm (u.val.val (zeroIndex 1 1)) ∞ (volume.restrict (Ω : Set (Domain 1))) ≤
      ENNReal.ofReal (2 * ‖u‖) := by
    calc
      _ = eLpNorm (OneDimensional.baseLp v) ∞ (volume.restrict (Ω : Set (Domain 1))) :=
        eLpNorm_congr_ae ((hE u).symm.trans hrestr.symm)
      _ ≤ eLpNorm (OneDimensional.baseLp v) ∞
          (volume.restrict (OneDimensional.lineDomain I : Set (Domain 1))) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono hΩI le_rfl)
      _ ≤ _ := hvinfty.trans (ENNReal.ofReal_le_ofReal hvreal)
  have hubound : eLpNorm (u.val.val (zeroIndex 1 1)) q (volume.restrict (Ω : Set (Domain 1))) ≤
      ((2 * A.toNNReal : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
    calc
      _ ≤ eLpNorm (u.val.val (zeroIndex 1 1)) ∞ (volume.restrict (Ω : Set (Domain 1))) * A := by
        simpa [A] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ (le_top : (q : ℝ≥0∞) ≤ ∞)
          (Lp.memLp (u.val.val (zeroIndex 1 1))).aestronglyMeasurable
      _ ≤ ENNReal.ofReal (2 * ‖u‖) * A := mul_le_mul_left huinfty A
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_toNNReal hA, ENNReal.ofReal_ofNat]
        change (2 * ENNReal.ofReal ‖u‖) * A =
          (2 * A) * ENNReal.ofReal ‖u‖
        ac_rfl
  exact ⟨hubound.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top), hubound⟩



end ExpandedFA.Sobolev.Rellich

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
theorem eLpNorm_zero_dim_eq {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Domain 0))
    (f : Domain 0 → 𝕜) {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hq0 : q ≠ 0) (hqt : q ≠ ∞) :
    eLpNorm f p (volume.restrict (Ω : Set (Domain 0))) =
      eLpNorm f q (volume.restrict (Ω : Set (Domain 0))) := by
  classical
  have hf : f = fun _ => f 0 := funext (fun x => congrArg f (Subsingleton.elim x 0))
  rw [hf, eLpNorm_const' _ hp0 hpt, eLpNorm_const' _ hq0 hqt]
  have hvol : volume (univ : Set (Domain 0)) = 1 := by
    have hset : (univ : Set (Domain 0)) = Set.pi univ (fun _ : Fin 0 => univ) := by simp
    rw [hset, volume_pi_pi]
    simp
  by_cases hx : (0 : Domain 0) ∈ Ω
  · have hΩ : (Ω : Set (Domain 0)) = univ := by
      ext x
      rw [Subsingleton.elim x 0]
      exact iff_of_true hx (mem_univ _)
    simp [hΩ, hvol]
  · have hΩ : (Ω : Set (Domain 0)) = ∅ := by
      ext x
      rw [Subsingleton.elim x 0]
      exact iff_of_false hx (by simp)
    simp [hΩ, ENNReal.toReal_pos hp0 hpt, ENNReal.toReal_pos hq0 hqt]

theorem zero_dim_bound {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Domain 0))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (q : ℝ≥0) (hq : 1 ≤ q)
    (u : ZeroSpaceValue 𝕜 0 Ω 1 p hp) :
    MemLp (u.val.val (zeroIndex 0 1)) q (volume.restrict (Ω : Set (Domain 0))) ∧
      eLpNorm (u.val.val (zeroIndex 0 1)) q (volume.restrict (Ω : Set (Domain 0))) ≤
        ENNReal.ofReal ‖u‖ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hq))
  have heq := eLpNorm_zero_dim_eq Ω (u.val.val (zeroIndex 0 1)) hq0
    ENNReal.coe_ne_top hp0 hp
  have hmem : MemLp (u.val.val (zeroIndex 0 1)) q (volume.restrict (Ω : Set (Domain 0))) :=
    heq.trans_lt (Lp.memLp (u.val.val (zeroIndex 0 1))).eLpNorm_lt_top
  refine ⟨hmem, ?_⟩
  rw [heq, ← Lp.enorm_def, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  exact PiLp.norm_apply_le u.val.val (zeroIndex 0 1)

theorem zero_dim_compact {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Domain 0))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain 0)))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (q : ℝ≥0) (hq : 1 ≤ q) [Fact (1 ≤ (q : ℝ≥0∞))] :
    CompactZeroLpInclusion (𝕜 := 𝕜) Ω p hp q := by
  letI : IsFiniteMeasure (volume.restrict (Ω : Set (Domain 0))) :=
    ⟨by simpa using hΩ.measure_lt_top (μ := volume)⟩
  apply compact_zero_of_higher_bound hp (zero_same_exponent hΩ hp)
    hq (lt_add_one q) (C := 1) ENNReal.one_ne_top
  intro u
  simpa only [one_mul] using zero_dim_bound Ω hp (q + 1)
    (le_add_of_nonneg_left (show 0 ≤ q from bot_le)) u
end ExpandedFA.Sobolev.Rellich

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

theorem zero_higher_bound_of_two_le (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (hd : 2 ≤ d)
    (Ω : Opens (Domain d)) (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    (p : ℝ≥0) (hdp : (d : ℝ≥0) ≤ p) [Fact (1 ≤ (p : ℝ≥0∞))]
    (q : ℝ≥0) (hq : 1 ≤ q) :
    ∃ r : ℝ≥0, q < r ∧ ∃ D : ℝ≥0∞, D ≠ ∞ ∧
      ∀ u : ZeroSpaceValue 𝕜 d Ω 1 p ENNReal.coe_ne_top,
        MemLp (u.val.val (zeroIndex d 1)) r (volume.restrict (Ω : Set (Domain d))) ∧
        eLpNorm (u.val.val (zeroIndex d 1)) r (volume.restrict (Ω : Set (Domain d))) ≤
          D * ENNReal.ofReal ‖u‖ := by
  let μ := volume.restrict (Ω : Set (Domain d))
  letI : IsFiniteMeasure μ := ⟨by simpa [μ] using hΩ.measure_lt_top (μ := volume)⟩
  obtain ⟨s, hs, hsd, hqr⟩ := Subcritical.choose_subcritical_exponent hd (q + 1)
    (by exact le_trans hq (le_add_of_nonneg_right zero_le_one))
  letI : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by exact_mod_cast hs⟩
  obtain ⟨C, hC⟩ := zero_subcritical_bound 𝕜 d Ω s hs hsd
  have hsp : s ≤ p := hsd.le.trans hdp
  let L := lowerZeroExponentCLM (𝕜 := 𝕜) (d := d) (m := 1) (Ω := Ω) hs hsp
  let α : ℝ := 1 / (s : ℝ) - 1 / (p : ℝ)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast lt_of_lt_of_le zero_lt_one hs
  have hα : 0 ≤ α := sub_nonneg.mpr (one_div_le_one_div_of_le hs0 (by exact_mod_cast hsp))
  let D : ℝ≥0∞ := (C : ℝ≥0∞) * μ univ ^ α
  have hD : D ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hα (measure_ne_top μ _))
  refine ⟨Subcritical.criticalExponent d s, lt_of_lt_of_le (lt_add_one q) hqr, D, hD, fun u => ?_⟩
  have heq : (L u).val.val (zeroIndex d 1) =ᵐ[μ] u.val.val (zeroIndex d 1) :=
    lowerExponentCLM_coe hs hsp u.val _
  refine ⟨(hC (L u)).1.ae_eq heq, ?_⟩
  have hnorm : ENNReal.ofReal ‖L u‖ ≤ ENNReal.ofReal ‖u‖ * μ univ ^ α := by
    change ENNReal.ofReal ‖C1Extension.Transport.lowerExponent
      (show (s : ℝ≥0∞) ≤ p by exact_mod_cast hsp) u.val‖ ≤ _
    simpa only [α, μ, ENNReal.coe_toReal, Submodule.norm_coe] using
      (Subcritical.lowerExponent_eNorm_le
        (show (s : ℝ≥0∞) ≤ p by exact_mod_cast hsp) u.val)
  calc
    _ = eLpNorm ((L u).val.val (zeroIndex d 1)) (Subcritical.criticalExponent d s) μ :=
      eLpNorm_congr_ae heq.symm
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal ‖L u‖ := (hC (L u)).2
    _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal ‖u‖ * μ univ ^ α) := mul_le_mul_right hnorm _
    _ = D * ENNReal.ofReal ‖u‖ := by dsimp [D]; ac_rfl

theorem zero_critical_of_two_le (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (hd : 2 ≤ d)
    (Ω : Opens (Domain d)) (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    (q : ℝ≥0) (hq : 1 ≤ q) [Fact (1 ≤ (d : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] :
    CompactZeroLpInclusion (𝕜 := 𝕜) Ω d (by simp) q := by
  letI : IsFiniteMeasure (volume.restrict (Ω : Set (Domain d))) :=
    ⟨by simpa using hΩ.measure_lt_top (μ := volume)⟩
  letI : Fact (1 ≤ ((d : ℝ≥0) : ℝ≥0∞)) := ⟨by exact_mod_cast (show 1 ≤ d by omega)⟩
  obtain ⟨r, hqr, D, hD, H⟩ := zero_higher_bound_of_two_le 𝕜 d hd Ω hΩ d le_rfl q hq
  exact compact_zero_of_higher_bound (by simp) (zero_same_exponent hΩ (by simp)) hq hqr hD H

theorem zero_supercritical_of_two_le (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (hd : 2 ≤ d)
    (Ω : Opens (Domain d)) (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    (p q : ℝ≥0) (hdp : (d : ℝ≥0) < p) (hq : 1 ≤ q)
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] :
    CompactZeroLpInclusion (𝕜 := 𝕜) Ω p ENNReal.coe_ne_top q := by
  letI : IsFiniteMeasure (volume.restrict (Ω : Set (Domain d))) :=
    ⟨by simpa using hΩ.measure_lt_top (μ := volume)⟩
  obtain ⟨r, hqr, D, hD, H⟩ := zero_higher_bound_of_two_le 𝕜 d hd Ω hΩ p hdp.le q hq
  exact compact_zero_of_higher_bound ENNReal.coe_ne_top (zero_same_exponent hΩ ENNReal.coe_ne_top) hq hqr hD H
end ExpandedFA.Sobolev.Rellich

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- A fixed positive Lp norm and an almost everywhere zero pointwise limit exclude all
norm convergent subsequences. -/
theorem no_subsequence_of_ae_zero_limit {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (v : ℕ → Lp E q μ) (hzero : ∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) (hnorm : ∀ n, ‖v n‖ = c) :
    ¬ ∃ (σ : ℕ → ℕ) (v₀ : Lp E q μ),
      StrictMono σ ∧ Tendsto (v ∘ σ) atTop (𝓝 v₀) := by
  rintro ⟨σ, v₀, hσ, hv⟩
  obtain ⟨τ, hτ, hconv⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hzero₀ : v₀ = 0 := by
    apply Lp.ext
    filter_upwards [hzero, hconv, Lp.coeFn_zero E q μ] with x hx hcx hzx
    have hlim := (hx.comp hσ.tendsto_atTop).comp hτ.tendsto_atTop
    exact (tendsto_nhds_unique hcx hlim).trans hzx.symm
  have hn : Tendsto (fun _ : ℕ => c) atTop (𝓝 ‖v₀‖) := by
    simpa only [Function.comp_def, hnorm] using hv.norm
  have : c = 0 := by
    simpa [hzero₀] using (tendsto_nhds_unique hn tendsto_const_nhds).symm
  exact hc.ne' this

/-- Scalar dilation and translation, with the exact Haar Jacobian. -/
theorem dilated_lpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Domain d → 𝕜) (hφ : Continuous φ) {scale : ℝ} (hscale : 0 < scale)
    (a : Domain d) (q : ℝ≥0∞) :
    (eLpNorm (fun x => φ (scale • (x-a))) q volume).toReal =
      scale ^ (-(d : ℝ) / q.toReal) * (eLpNorm φ q volume).toReal := by
  have hmap : Measure.map (fun x : Domain d => scale • x) volume =
      (ENNReal.ofReal (scale ^ d))⁻¹ • volume := by
    rw [Measure.map_addHaar_smul volume hscale.ne']
    simp only [Module.finrank_pi, Fintype.card_fin,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hscale.le d)), ENNReal.ofReal_inv_of_pos (pow_pos hscale d)]
  have htrans : eLpNorm (fun x => φ (scale • (x-a))) q volume =
      eLpNorm (fun x => φ (scale • x)) q volume := by
    exact eLpNorm_comp_measurePreserving
      (hφ.comp (by fun_prop : Continuous (fun x : Domain d => scale • x))).aestronglyMeasurable
      (measurePreserving_sub_right volume a)
  rw [htrans]
  change (eLpNorm (φ ∘ (fun x : Domain d => scale • x)) q volume).toReal = _
  rw [← eLpNorm_map_measure hφ.aestronglyMeasurable (by fun_prop), hmap,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)]
  simp only [one_div, ENNReal.toReal_inv, smul_eq_mul, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (pow_nonneg hscale.le d)]
  rw [Real.inv_rpow (pow_nonneg hscale.le d), ← Real.rpow_neg (pow_nonneg hscale.le d), ← Real.rpow_natCast_mul hscale.le]
  congr 2
  ring

theorem concentratingBump_contDiff {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0) (a : Domain d) {φ : Domain d → 𝕜}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (concentratingBump p a φ n) := by
  exact (hφ.comp ((contDiff_id.sub contDiff_const).const_smul (n+1 : ℝ))).const_smul _

theorem concentratingBump_compactSupport {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0) (a : Domain d) {φ : Domain d → 𝕜}
    (hφ : HasCompactSupport φ) (n : ℕ) :
    HasCompactSupport (concentratingBump p a φ n) := by
  let H : Domain d ≃ₜ Domain d := (Homeomorph.subRight a).trans
    (Homeomorph.smul (Units.mk0 (n+1 : ℝ) (by positivity)))
  change HasCompactSupport ((fun _ : Domain d => ((n+1 : ℝ)^((d : ℝ)/p-1))) • (φ ∘ H))
  exact (hφ.comp_isClosedEmbedding H.isClosedEmbedding).smul_left

theorem concentratingBump_tsupport {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0) (a : Domain d) {φ : Domain d → 𝕜} {r : ℝ}
    (hφ : tsupport φ ⊆ Metric.ball 0 r) (n : ℕ) :
    tsupport (concentratingBump p a φ n) ⊆ Metric.ball a r := by
  intro x hx
  have hpre : (n+1 : ℝ) • (x-a) ∈ tsupport φ :=
    tsupport_comp_subset_preimage φ (f := fun y : Domain d => (n+1 : ℝ) • (y-a)) (by fun_prop)
      ((tsupport_smul_subset_right (fun _ : Domain d => ((n+1 : ℝ)^((d : ℝ)/p-1))) (fun y => φ ((n+1 : ℝ) • (y-a)))) hx)
  have hr : ‖(n+1 : ℝ) • (x-a)‖ < r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hφ hpre
  rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (n+1 : ℝ))] at hr
  rw [Metric.mem_ball, dist_eq_norm]
  have hnx : ‖x-a‖ ≤ (n+1 : ℝ) * ‖x-a‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  exact hnx.trans_lt hr

theorem concentratingBump_eventually_zero {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0) (a : Domain d) {φ : Domain d → 𝕜}
    (hφ : HasCompactSupport φ) {x : Domain d} (hx : x ≠ a) :
    ∀ᶠ n : ℕ in atTop, concentratingBump p a φ n x = 0 := by
  obtain ⟨R, hR, hbound⟩ := hφ.isBounded.exists_pos_norm_le
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ) * ‖x-a‖) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const (norm_pos_iff.mpr (sub_ne_zero.mpr hx))
  filter_upwards [hn.eventually_gt_atTop R] with n hn
  unfold concentratingBump
  have hnot : (n+1 : ℝ) • (x-a) ∉ tsupport φ := by
    intro hs
    have hb := hbound _ hs
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (n+1 : ℝ))] at hb
    exact (not_le_of_gt hn) hb
  rw [image_eq_zero_of_notMem_tsupport hnot, smul_zero]

/-- Every nonempty open set contains an interior centre and a nonzero smooth
compact bump on a ball centred at the origin whose every concentration stays inside. -/
theorem exists_concentrating_bump {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Domain d)) (hΩ : (Ω : Set (Domain d)).Nonempty) :
    ∃ (a : Domain d) (φ : Domain d → 𝕜), a ∈ Ω ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ φ ≠ 0 ∧
      ∀ (p : ℝ≥0) (n : ℕ), tsupport (concentratingBump p a φ n) ⊆ Ω := by
  obtain ⟨a, ha⟩ := hΩ
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp Ω.isOpen a ha
  obtain ⟨f, hfs, hfc, hfd, _, hf0⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (Metric.ball_mem_nhds (0 : Domain d) hr)
  let φ : Domain d → 𝕜 := fun x => (f x : 𝕜)
  have hφd : ContDiff ℝ (⊤ : ℕ∞) φ := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hfd
  have hφc : HasCompactSupport φ := hfc.comp_left (by simp)
  have hφs : tsupport φ ⊆ Metric.ball 0 r :=
    (tsupport_comp_subset (g := fun t : ℝ => (t : 𝕜)) (by simp) f).trans hfs
  refine ⟨a, φ, ha, hφd, hφc, ?_, fun p n => (concentratingBump_tsupport p a hφs n).trans hrs⟩
  intro hφ
  have : φ 0 = 1 := by simp [φ, hf0]
  simp [hφ] at this

theorem scalar_dilated_lpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Domain d → 𝕜) (hφ : Continuous φ) {scale : ℝ} (hs : 0 < scale)
    (a : Domain d) (q : ℝ≥0∞) (exponent : ℝ) :
    (eLpNorm (fun x => scale ^ exponent • φ (scale • (x-a))) q volume).toReal =
      scale ^ (exponent - (d : ℝ) / q.toReal) * (eLpNorm φ q volume).toReal := by
  change (eLpNorm ((scale ^ exponent) • (fun x => φ (scale • (x-a)))) q volume).toReal = _
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, enorm_eq_nnnorm, ENNReal.coe_toReal,
    coe_nnnorm, Real.norm_of_nonneg (Real.rpow_nonneg hs.le _), dilated_lpNorm φ hφ hs]
  rw [← mul_assoc, ← Real.rpow_add hs]
  congr 2
  ring

theorem concentratingBump_lpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0) (a : Domain d) {φ : Domain d → 𝕜} (hφ : Continuous φ)
    (n : ℕ) (q : ℝ≥0∞) :
    (eLpNorm (concentratingBump p a φ n) q volume).toReal =
      (n+1 : ℝ) ^ ((d : ℝ)/p - 1 - (d : ℝ)/q.toReal) * (eLpNorm φ q volume).toReal :=
  scalar_dilated_lpNorm φ hφ (by positivity) a q _

theorem concentratingBump_critical_lpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0} (hp : 1 ≤ p) (hpd : p < d) (a : Domain d)
    {φ : Domain d → 𝕜} (hφ : Continuous φ) (n : ℕ) :
    (eLpNorm (concentratingBump p a φ n) (Subcritical.criticalExponent d p) volume).toReal =
      (eLpNorm φ (Subcritical.criticalExponent d p) volume).toReal := by
  rw [concentratingBump_lpNorm p a hφ n]
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp))
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp.trans hpd.le))
  have hdp : (d : ℝ) - p ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hpd))
  have hq : ((Subcritical.criticalExponent d p : ℝ≥0∞)).toReal =
      (d : ℝ) * p / ((d : ℝ) - p) := by
    simp only [ENNReal.coe_toReal, Subcritical.criticalExponent, NNReal.coe_div,
      NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_sub hpd.le]
  have hexp : (d : ℝ)/p - 1 - (d : ℝ)/((Subcritical.criticalExponent d p : ℝ≥0∞)).toReal = 0 := by
    rw [hq]
    field_simp
    ring
  rw [hexp, Real.rpow_zero, one_mul]

def testToZeroSobolev {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Domain d)}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (φ : Tests 𝕜 Ω) :
    ZeroSpaceValue 𝕜 d Ω 1 p hp :=
  ⟨testToSobolev 1 φ, (smoothSubmodule 𝕜 d Ω 1 p).le_topologicalClosure
    ⟨φ, by simpa only [testToSobolev_underlying] using testToDomainLp_coe (p := p) φ⟩⟩

theorem concentrating_ae_zero_limit {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hd : 0 < d) {Ω : Opens (Domain d)} (p : ℝ≥0) (a : Domain d)
    {φ : Domain d → 𝕜} (hφ : HasCompactSupport φ)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (v : ℕ → DomainLp 𝕜 Ω q)
    (hv : ∀ n, v n =ᵐ[volume.restrict (Ω : Set (Domain d))] concentratingBump p a φ n) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))),
      Tendsto (fun n => v n x) atTop (𝓝 0) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hne : ∀ᵐ x : Domain d ∂volume, x ≠ a := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_of_ae hne, ae_all_iff.mpr hv] with x hx hrep
  have hevent : ∀ᶠ n : ℕ in atTop, v n x = 0 :=
    (concentratingBump_eventually_zero p a hφ hx).mono fun n hn => (hrep n).trans hn
  exact tendsto_const_nhds.congr' (hevent.mono fun n hn => hn.symm)

theorem fderiv_scalar_dilate {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Domain d → 𝕜} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {scale : ℝ} (hs : 0 < scale) (a : Domain d) (exponent : ℝ)
    (x z : Domain d) :
    fderiv ℝ (fun y => scale ^ exponent • φ (scale • (y-a))) x z =
      scale ^ (exponent+1) • fderiv ℝ φ (scale • (x-a)) z := by
  have hi : HasFDerivAt (fun y : Domain d => scale • (y-a))
      (scale • ContinuousLinearMap.id ℝ (Domain d)) x :=
    ((hasFDerivAt_id x).sub_const a).const_smul scale
  have ho := ((hφ.differentiable (by simp) (scale • (x-a))).hasFDerivAt.comp x hi).const_smul (scale ^ exponent)
  have heq := congrArg (fun L : Domain d →L[ℝ] 𝕜 => L z) ho.fderiv
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul] at heq
  rw [Real.rpow_add hs, Real.rpow_one]
  convert! heq using 3

theorem concentratingBump_derivative_lpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0) (a : Domain d) {φ : Domain d → 𝕜}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (n : ℕ) (i : Fin d) :
    (eLpNorm (fun x => fderiv ℝ (concentratingBump p a φ n) x (coordinateVector i)) p volume).toReal =
      (eLpNorm (fun x => fderiv ℝ φ x (coordinateVector i)) p volume).toReal := by
  have heq : (fun x => fderiv ℝ (concentratingBump p a φ n) x (coordinateVector i)) =
      (fun x => (n+1 : ℝ)^((d : ℝ)/p) • fderiv ℝ φ ((n+1 : ℝ) • (x-a)) (coordinateVector i)) := by
    funext x
    unfold concentratingBump
    simpa only [sub_add_cancel] using fderiv_scalar_dilate hφ (by positivity : 0 < (n+1 : ℝ)) a ((d : ℝ)/p-1) x (coordinateVector i)
  rw [heq]
  have hc : Continuous (fun x => fderiv ℝ φ x (coordinateVector i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [scalar_dilated_lpNorm _ hc (by positivity), ENNReal.coe_toReal, sub_self,
    Real.rpow_zero, one_mul]

theorem concentratingBump_base_lpNorm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0) (a : Domain d) {φ : Domain d → 𝕜} (hφ : Continuous φ) (n : ℕ) :
    (eLpNorm (concentratingBump p a φ n) p volume).toReal ≤
      (eLpNorm φ p volume).toReal := by
  rw [concentratingBump_lpNorm p a hφ n, ENNReal.coe_toReal]
  have he : (d : ℝ)/p - 1 - (d : ℝ)/p = -1 := by ring
  rw [he, Real.rpow_neg_one]
  exact mul_le_of_le_one_left ENNReal.toReal_nonneg (inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]))

theorem testToSobolev_norm_le_first_order {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (ψ : Tests 𝕜 Ω)
    {C : ℝ} (h0 : ‖testToDomainLp (p := p) ψ‖ ≤ C)
    (h1 : ∀ i : Fin d, ‖testToDomainLp (p := p) (testPartialCLM [i] ψ)‖ ≤ C) :
    ‖testToSobolev (p := p) 1 ψ‖ ≤ (Fintype.card (DerivativeIndex d 1) : ℝ) * C := by
  classical
  rw [sobolev_norm_formula]
  change (∑ α, ‖(testToSobolev (p := p) 1 ψ).val α‖) ≤ _
  calc
    _ ≤ ∑ _ : DerivativeIndex d 1, C := by
      apply Finset.sum_le_sum
      intro α hα
      change ‖testToDomainLp (p := p) (testPartialCLM (multiIndexWord (natIndex α)).reverse ψ)‖ ≤ C
      have hl : (multiIndexWord (natIndex α)).reverse.length ≤ 1 := by
        simpa only [List.length_reverse, multiIndexWord_length, natIndex] using α.property
      cases hw : (multiIndexWord (natIndex α)).reverse with
      | nil => exact h0
      | cons i w =>
        cases w with
        | nil => exact h1 i
        | cons j w => simp [hw] at hl
    _ = _ := by simp

theorem testToDomainLp_norm_full {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (ψ : Tests 𝕜 Ω) :
    ‖testToDomainLp (p := p) ψ‖ = (eLpNorm ψ p volume).toReal := by
  unfold testToDomainLp
  rw [Lp.norm_toLp, eLpNorm_restrict_eq_of_support_subset ψ.continuous.aestronglyMeasurable
    ((subset_tsupport ψ).trans ψ.tsupport_subset)]

theorem critical_noncompactness :
    Specs.ExpandedFA.Sobolev.RellichEmbeddings.CriticalNoncompactness := by
  classical
  intro 𝕜 _ d Ω hΩ p hp hpd _ _
  obtain ⟨a, φ, ha, hφd, hφc, hφ0, hφs⟩ := exists_concentrating_bump (𝕜 := 𝕜) Ω hΩ
  let ψ : ℕ → Tests 𝕜 Ω := fun n =>
    ⟨concentratingBump p a φ n, concentratingBump_contDiff p a hφd n,
      concentratingBump_compactSupport p a hφc n, hφs p n⟩
  let u : ℕ → ZeroSpaceValue 𝕜 d Ω 1 p ENNReal.coe_ne_top :=
    fun n => testToZeroSobolev p ENNReal.coe_ne_top (ψ n)
  let v : ℕ → DomainLp 𝕜 Ω (Subcritical.criticalExponent d p) :=
    fun n => testToDomainLp (ψ n)
  have huv (n : ℕ) : (u n).val.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      concentratingBump p a φ n := by
    simpa only [u, testToZeroSobolev, testToSobolev_underlying, ψ, TestFunction.coe_mk] using testToDomainLp_coe (p := p) (ψ n)
  have hv (n : ℕ) : v n =ᵐ[volume.restrict (Ω : Set (Domain d))] concentratingBump p a φ n := by
    simpa only [v, ψ, TestFunction.coe_mk] using testToDomainLp_coe (p := (Subcritical.criticalExponent d p : ℝ≥0∞)) (ψ n)
  let B : ℝ := (eLpNorm φ p volume).toReal +
    ∑ i : Fin d, (eLpNorm (fun x => fderiv ℝ φ x (coordinateVector i)) p volume).toReal
  have hB0 : (eLpNorm φ p volume).toReal ≤ B :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
  have hB1 (i : Fin d) :
      (eLpNorm (fun x => fderiv ℝ φ x (coordinateVector i)) p volume).toReal ≤ B := by
    calc
      _ ≤ ∑ j : Fin d, (eLpNorm (fun x => fderiv ℝ φ x (coordinateVector j)) p volume).toReal :=
        Finset.single_le_sum (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ i)
      _ ≤ B := le_add_of_nonneg_left ENNReal.toReal_nonneg
  have hu_bound (n : ℕ) : ‖u n‖ ≤ (Fintype.card (DerivativeIndex d 1) : ℝ) * B := by
    change ‖testToSobolev (p := (p : ℝ≥0∞)) 1 (ψ n)‖ ≤ _
    apply testToSobolev_norm_le_first_order
    · rw [testToDomainLp_norm_full]
      exact (concentratingBump_base_lpNorm_le p a hφd.continuous n).trans hB0
    · intro i
      rw [testToDomainLp_norm_full]
      have heq : (testPartialCLM [i] (ψ n) : Domain d → 𝕜) =
          fun x => fderiv ℝ (concentratingBump p a φ n) x (coordinateVector i) := by
        ext x
        exact testPartial_single_apply i (ψ n) x
      rw [heq, concentratingBump_derivative_lpNorm p a hφd n i]
      exact hB1 i
  have hu_bdd : Bornology.IsBounded (Set.range u) :=
    isBounded_iff_forall_norm_le.mpr ⟨_, fun z hz => by obtain ⟨n, rfl⟩ := hz; exact hu_bound n⟩
  let c : ℝ := (eLpNorm φ (Subcritical.criticalExponent d p) volume).toReal
  have hc : 0 < c := by
    apply ENNReal.toReal_pos
    · intro hz
      have hae := (eLpNorm_eq_zero_iff (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ (Subcritical.criticalExponent d p : ℝ≥0∞))))).mp hz
      exact hφ0 ((hφd.continuous.ae_eq_iff_eq volume continuous_const).mp hae)
    · exact (hφd.continuous.memLp_of_hasCompactSupport hφc).eLpNorm_ne_top
  have hvnorm (n : ℕ) : ‖v n‖ = c := by
    change ‖testToDomainLp (ψ n)‖ = c
    rw [testToDomainLp_norm_full]
    exact concentratingBump_critical_lpNorm hp hpd a hφd.continuous n
  refine ⟨a, φ, u, v, ha, hφd, hφc, hφ0, hu_bdd, ?_, huv, hv, ⟨c, hc, hvnorm⟩, ?_⟩
  · exact fun n => ⟨concentratingBump_compactSupport p a hφc n, hφs p n⟩
  · have hd : 0 < d := by exact_mod_cast (lt_of_le_of_lt (show (0 : ℝ≥0) ≤ p from bot_le) hpd)
    exact no_subsequence_of_ae_zero_limit v (concentrating_ae_zero_limit hd p a hφc v hv) hc hvnorm

end ExpandedFA.Sobolev.Rellich

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

theorem zero_bound_of_lower_exponent {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p s r : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    [Fact (1 ≤ (s : ℝ≥0∞))] [IsFiniteMeasure (volume.restrict (Ω : Set (Domain d)))]
    (hs : 1 ≤ s) (hsp : s ≤ p) (C : ℝ≥0)
    (H : ∀ u : ZeroSpaceValue 𝕜 d Ω 1 s ENNReal.coe_ne_top,
      MemLp (u.val.val (zeroIndex d 1)) r (volume.restrict (Ω : Set (Domain d))) ∧
      eLpNorm (u.val.val (zeroIndex d 1)) r (volume.restrict (Ω : Set (Domain d))) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖) :
    ∃ D : ℝ≥0, ∀ u : ZeroSpaceValue 𝕜 d Ω 1 p ENNReal.coe_ne_top,
      MemLp (u.val.val (zeroIndex d 1)) r (volume.restrict (Ω : Set (Domain d))) ∧
      eLpNorm (u.val.val (zeroIndex d 1)) r (volume.restrict (Ω : Set (Domain d))) ≤
        (D : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
  let L := lowerZeroExponentCLM (𝕜 := 𝕜) (d := d) (m := 1) (Ω := Ω) hs hsp
  let A := (volume.restrict (Ω : Set (Domain d))) univ ^ (1/(s : ℝ) - 1/(p : ℝ))
  have hs0 : (0 : ℝ) < s := by exact_mod_cast lt_of_lt_of_le zero_lt_one hs
  have hA : A ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg
    (sub_nonneg.mpr (one_div_le_one_div_of_le hs0 (by exact_mod_cast hsp)))
    (measure_ne_top _ _)).ne
  refine ⟨C * A.toNNReal, fun u => ?_⟩
  have heq : (L u).val.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      u.val.val (zeroIndex d 1) := lowerExponentCLM_coe hs hsp u.val _
  have hnorm : ENNReal.ofReal ‖L u‖ ≤ ENNReal.ofReal ‖u‖ * A := by
    change ENNReal.ofReal ‖C1Extension.Transport.lowerExponent
      (show (s : ℝ≥0∞) ≤ p by exact_mod_cast hsp) u.val‖ ≤ _
    simpa only [ENNReal.coe_toReal, Submodule.norm_coe, A] using
      Subcritical.lowerExponent_eNorm_le (show (s : ℝ≥0∞) ≤ p by exact_mod_cast hsp) u.val
  refine ⟨(H (L u)).1.ae_eq heq, ?_⟩
  calc
    _ = eLpNorm ((L u).val.val (zeroIndex d 1)) r (volume.restrict (Ω : Set (Domain d))) :=
      eLpNorm_congr_ae heq.symm
    _ ≤ C * ENNReal.ofReal ‖L u‖ := (H (L u)).2
    _ ≤ C * (ENNReal.ofReal ‖u‖ * A) := mul_le_mul_right hnorm C
    _ = (C * A.toNNReal : ℝ≥0) * ENNReal.ofReal ‖u‖ := by
      rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hA]
      ac_rfl
end ExpandedFA.Sobolev.Rellich

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
theorem zero_one_compact {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Domain 1))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain 1)))
    (p q : ℝ≥0) (hp : 1 ≤ p) (hq : 1 ≤ q)
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] :
    CompactZeroLpInclusion (𝕜 := 𝕜) Ω p ENNReal.coe_ne_top q := by
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  letI : IsFiniteMeasure (volume.restrict (Ω : Set (Domain 1))) :=
    ⟨by simpa using hΩ.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := zero_one_bound 𝕜 Ω hΩ (q + 1)
    (le_add_of_nonneg_left (show 0 ≤ q from bot_le))
  obtain ⟨D, hD⟩ := zero_bound_of_lower_exponent
    (p := p) (s := 1) (by norm_num) hp C (fun u => hC u)
  exact compact_zero_of_higher_bound ENNReal.coe_ne_top
    (zero_same_exponent hΩ ENNReal.coe_ne_top) hq (lt_add_one q)
    ENNReal.coe_ne_top hD


/-- The critical-dimensional zero-boundary compactness includes dimension one. -/
theorem zero_critical : Specs.ExpandedFA.Sobolev.RellichEmbeddings.ZeroCritical := by
  intro 𝕜 _ d hd Ω hΩ q hq _ _
  by_cases hd1 : d = 1
  · subst d
    letI : Fact (1 ≤ ((1 : ℝ≥0) : ℝ≥0∞)) := ⟨by simp⟩
    simpa only [ENNReal.coe_one, Nat.cast_one] using
      zero_one_compact (𝕜 := 𝕜) Ω hΩ 1 q le_rfl hq
  · exact zero_critical_of_two_le 𝕜 d (by omega) Ω hΩ q hq

/-- All finite targets are compact for finite p>d, on every bounded open set. -/
theorem zero_supercritical : Specs.ExpandedFA.Sobolev.RellichEmbeddings.ZeroSupercritical := by
  intro 𝕜 _ d Ω hΩ p q hp hdp hq _ _
  by_cases hd0 : d = 0
  · subst d
    exact zero_dim_compact (𝕜 := 𝕜) Ω hΩ ENNReal.coe_ne_top q hq
  by_cases hd1 : d = 1
  · subst d
    exact zero_one_compact (𝕜 := 𝕜) Ω hΩ p q hp hq
  exact zero_supercritical_of_two_le 𝕜 d (by omega) Ω hΩ p q hdp hq

/-- The complete Rellich conclusion, with the explicit critical obstruction. -/
theorem embeddings : Specs.ExpandedFA.Sobolev.RellichEmbeddings.Embeddings :=
  ⟨subcritical, critical, supercritical, zero_subcritical, zero_critical,
    zero_supercritical, critical_noncompactness⟩

end ExpandedFA.Sobolev.Rellich
