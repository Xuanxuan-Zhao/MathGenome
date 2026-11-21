import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.BoundaryChartLocalization
import MathGenome.Internal.FourierSobolev.P102.Trace.GraphFractionalTransport
import MathGenome.Internal.FourierSobolev.P102.Fractional.Localization
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace P102.Trace.BoundaryChartLocalization
open P102.U4.GraphPieces P102.Sobolev.Geometry
open MeasuredFractional

variable {m : ℕ} {Ω : Set (Ambient m)} {𝕜 : Type*} [RCLike 𝕜]

theorem graph_subset_frontier (C : BoundaryChart Ω) :
    chartGraph C '' ball C.center C.radius ⊆ frontier Ω := by
  rintro _ ⟨x, hx, rfl⟩
  have hh : chartGraph C x ∈ C.frame '' (graph C.graphFunction '' ball C.center C.radius) :=
    ⟨graph C.graphFunction x, ⟨x, hx, rfl⟩, rfl⟩
  rw [← C.boundary] at hh
  exact hh.1

theorem graphMeasure_le_surfaceMeasure (C : BoundaryChart Ω) :
    GraphFractionalTransport.graphMeasure C.frame C.graphFunction
      (ball C.center C.radius) ≤ surfaceMeasure Ω :=
  Measure.restrict_mono (graph_subset_frontier C) le_rfl

/-- The smaller physical cylinder forces the tangential support into its
smaller ball, independently of values of the graph off the chart. -/
theorem cutoff_eq_zero_off_smaller (C : BoundaryChart Ω) (χ : Ambient m → ℝ)
    {r a : ℝ} (hsupp : tsupport χ ⊆
      chartImage C.frame C.graphFunction C.center r a)
    {x : P102.U4.Space m} (hx : x ∉ ball C.center r) :
    χ (chartGraph C x) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  obtain ⟨_, ⟨z, hz, rfl⟩, heq⟩ := hsupp ht
  have heq' := C.frame.injective heq
  have hfirst := congrArg (fun w : Ambient m => w.ofLp.1) heq'
  change z.ofLp.1 = x at hfirst
  exact hx (hfirst ▸ hz.1)

theorem localizedPullback_eq_zero_off_smaller (C : BoundaryChart Ω)
    (χ : Ambient m → ℝ) {r a : ℝ} (hsupp : tsupport χ ⊆
      chartImage C.frame C.graphFunction C.center r a)
    (g : Ambient m → 𝕜) {x : P102.U4.Space m} (hx : x ∉ ball C.center r) :
    localizedPullback C χ g x = 0 := by
  classical
  simp [localizedPullback, cutoff_eq_zero_off_smaller C χ hsupp hx]

theorem cutoff_supportedAway (C : BoundaryChart Ω) (χ : Ambient m → ℝ)
    {r a : ℝ} (hsupp : tsupport χ ⊆
      chartImage C.frame C.graphFunction C.center r a) (g : Ambient m → 𝕜) :
    P102.Fractional.SupportedAway (ball C.center C.radius) univ (C.radius - r)
      (fun x => χ (chartGraph C x) • g (chartGraph C x)) := by
  apply Filter.Eventually.of_forall
  intro x hx y hy
  have hxs : x ∈ ball C.center r := by
    by_contra hnot
    exact hx (by simp only [cutoff_eq_zero_off_smaller C χ hsupp hnot, zero_smul])
  have hyb : C.radius ≤ dist y C.center := by
    simpa only [mem_ball, not_lt] using hy.2
  have hxb : dist x C.center < r := hxs
  have ht := dist_triangle y x C.center
  rw [dist_comm y x] at ht
  linarith

/-- Smooth compactly supported ambient cutoffs have genuine finite bounds;
these are derived here rather than included as extra hypotheses. -/
theorem cutoff_bounds (C : BoundaryChart Ω) (χ : Ambient m → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    ∃ M L : ℝ≥0, LipschitzOnWith L (χ ∘ chartGraph C) (ball C.center C.radius) ∧
      ∀ x ∈ ball C.center C.radius, ‖χ (chartGraph C x)‖ ≤ M := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hχ (by simp)
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hχ.continuous
  refine ⟨⟨max A 0, le_max_right _ _⟩, K * graphConstant C.constant, ?_, ?_⟩
  · exact hK.comp_lipschitzOnWith
      (graph_geometry_in_frame m _ _ _ C.graph_lipschitz C.frame).1
  · intro x hx
    exact (hA _).trans (le_max_left _ _)

theorem metricNorm_euclidean {d : ℕ} (G : Set (P102.Fractional.Domain d))
    (s : ℝ) (p : ℝ≥0∞) (u : P102.Fractional.Domain d → 𝕜) :
    metricNorm d (volume.restrict G) s p u =
      eLpNorm u p (P102.Fractional.domainMeasure G) + P102.Fractional.seminorm G s p u := by
  simp only [metricNorm, metricSeminorm, metricEnergy, P102.Fractional.seminorm,
    P102.Fractional.energy, P102.Fractional.domainMeasure, dist_eq_norm]

theorem metricNorm_mono_measure {X E : Type*} [MetricSpace X] [MeasurableSpace X]
    [NormedAddCommGroup E] (d : ℕ) (s : ℝ) (p : ℝ≥0∞) {μ ν : Measure X}
    (hμν : μ ≤ ν) (g : X → E) : metricNorm d μ s p g ≤ metricNorm d ν s p g := by
  apply add_le_add (eLpNorm_mono_measure g hμν)
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply lintegral_mono' hμν
  intro x
  exact lintegral_mono' hμν (fun _ => le_rfl)

/-- Raw sum-norm bound from the accepted multiplier energy estimate. This
does not require the input fractional energy to be finite. -/
theorem multiplier_norm_bound (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s)
    (hs1 : s < 1) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hpt : p ≠ ∞) (M L : ℝ≥0) :
    ∃ A : ℝ≥0, ∀ {𝕜 : Type*} [RCLike 𝕜] (G : Set (P102.Fractional.Domain d)),
      IsOpen G → ∀ φ : P102.Fractional.Domain d → 𝕜,
      LipschitzOnWith L φ G → (∀ x ∈ G, ‖φ x‖ ≤ M) →
      ∀ u : P102.Fractional.Domain d → 𝕜,
      MemLp u p (P102.Fractional.domainMeasure G) →
      MemLp (fun x => φ x * u x) p (P102.Fractional.domainMeasure G) ∧
      metricNorm d (volume.restrict G) s p (fun x => φ x * u x) ≤
        (A : ℝ≥0∞) * metricNorm d (volume.restrict G) s p u := by
  obtain ⟨C, hC⟩ := P102.Fractional.bounded_lipschitz_multiplier d hd s hs hs1 p hpt M L
  refine ⟨M + 2 * (C + 1), ?_⟩
  intro 𝕜 _ G hG φ hφ hM u hu
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have henergy := (hC G hG φ hφ hM).1 u hu
  have hc1 : (1 : ℝ≥0∞) ≤ ((C + 1 : ℝ≥0) : ℝ≥0∞) := by
    simp only [ENNReal.coe_add, ENNReal.coe_one]
    exact le_add_self
  have he : P102.Fractional.energy G s p (fun x => φ x * u x) ≤
      ((C + 1 : ℝ≥0) : ℝ≥0∞) *
        (P102.Fractional.energy G s p u + P102.Fractional.lpMass G p u) := by
    apply henergy.trans
    gcongr
    exact le_self_add
  have hroot := P102.Fractional.LocalizationMultiplier.root_sum_le hpt hc1 he
  have hmass : P102.Fractional.lpMass G p u ^ (1 / p.toReal) =
      eLpNorm u p (P102.Fractional.domainMeasure G) := by
    exact (eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hu.aestronglyMeasurable).symm
  rw [hmass] at hroot
  refine ⟨P102.Fractional.LocalizationMultiplier.memLp_mul hG hφ hM hu, ?_⟩
  rw [metricNorm_euclidean, metricNorm_euclidean]
  calc
    _ ≤ (M : ℝ≥0∞) * eLpNorm u p (P102.Fractional.domainMeasure G) +
        (2 * ((C + 1 : ℝ≥0) : ℝ≥0∞)) *
          (P102.Fractional.seminorm G s p u + eLpNorm u p (P102.Fractional.domainMeasure G)) :=
      add_le_add (P102.Fractional.LocalizationMultiplier.eLpNorm_mul_le hG hφ hM hu) hroot
    _ ≤ (M : ℝ≥0∞) *
        (eLpNorm u p (P102.Fractional.domainMeasure G) + P102.Fractional.seminorm G s p u) +
        (2 * ((C + 1 : ℝ≥0) : ℝ≥0∞)) *
          (P102.Fractional.seminorm G s p u + eLpNorm u p (P102.Fractional.domainMeasure G)) :=
      add_le_add (mul_le_mul le_rfl le_self_add (by positivity) (by positivity)) le_rfl
    _ = _ := by
      simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat]
      ring

/-- The whole-space artificial-edge contribution is included before taking
the root, using the accepted separated zero-extension theorem. -/
theorem zero_extension_norm_bound (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s)
    (hs1 : s < 1) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hpt : p ≠ ∞) (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℝ≥0, ∀ {𝕜 : Type*} [RCLike 𝕜] (G : Set (P102.Fractional.Domain d)),
      IsOpen G → ∀ u : P102.Fractional.Domain d → 𝕜,
      MemLp u p (P102.Fractional.domainMeasure G) →
      P102.Fractional.SupportedAway G univ δ u →
      MemLp (P102.Fractional.zeroExtend G u) p volume ∧
      metricNorm d volume s p (P102.Fractional.zeroExtend G u) ≤
        (D : ℝ≥0∞) * metricNorm d (volume.restrict G) s p u := by
  obtain ⟨C, hC⟩ := P102.Fractional.zero_extension_away d hd s hs hs1 p hpt
  let A : ℝ≥0 := C * Real.toNNReal (δ ^ (-s * p.toReal))
  refine ⟨2 + A, ?_⟩
  intro 𝕜 _ G hG u hu hsep
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hp1 : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hpt (Fact.out : 1 ≤ p)
  have hq0 : 0 ≤ 1 / p.toReal := by positivity
  have hq1 : (1 : ℝ) / p.toReal ≤ 1 := (div_le_iff₀ hp).mpr (by simpa using hp1)
  have he := (hC G univ hG isOpen_univ (subset_univ _) δ hδ).1 u hu hsep
  have he' : P102.Fractional.energy univ s p (P102.Fractional.zeroExtend G u) ≤
      P102.Fractional.energy G s p u + (A : ℝ≥0∞) * P102.Fractional.lpMass G p u := by
    have hA : (A : ℝ≥0∞) = (C : ℝ≥0∞) * ENNReal.ofReal (δ ^ (-s * p.toReal)) := by
      simp only [A, ENNReal.coe_mul, ENNReal.ofReal]
    rwa [hA]
  have hnorm := P102.Fractional.ZeroExtension.eLpNorm_indicator
    hG.measurableSet (subset_univ _) u (p := p)
  simp only [P102.Fractional.domainMeasure, Measure.restrict_univ] at hnorm
  have hmem : MemLp (P102.Fractional.zeroExtend G u) p volume := by
    change eLpNorm _ _ _ < ∞
    rw [P102.Fractional.zeroExtend, hnorm]
    exact hu.eLpNorm_lt_top
  refine ⟨hmem, ?_⟩
  have hmass : P102.Fractional.lpMass G p u ^ (1 / p.toReal) =
      eLpNorm u p (P102.Fractional.domainMeasure G) :=
    (eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hu.aestronglyMeasurable).symm
  have hroot : P102.Fractional.seminorm univ s p (P102.Fractional.zeroExtend G u) ≤
      P102.Fractional.seminorm G s p u +
        (1 + (A : ℝ≥0∞)) * eLpNorm u p (P102.Fractional.domainMeasure G) := by
    unfold P102.Fractional.seminorm
    calc
      _ ≤ (P102.Fractional.energy G s p u + (A : ℝ≥0∞) *
          P102.Fractional.lpMass G p u) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow he' hq0
      _ ≤ P102.Fractional.energy G s p u ^ (1 / p.toReal) +
          ((A : ℝ≥0∞) * P102.Fractional.lpMass G p u) ^ (1 / p.toReal) :=
        ENNReal.rpow_add_le_add_rpow _ _ hq0 hq1
      _ = P102.Fractional.energy G s p u ^ (1 / p.toReal) +
          (A : ℝ≥0∞) ^ (1 / p.toReal) * eLpNorm u p (P102.Fractional.domainMeasure G) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0, hmass]
      _ ≤ _ := by
        gcongr
        exact P102.Fractional.ZeroExtension.root_le_one_add _ hq0 hq1
  rw [show metricNorm d volume s p (P102.Fractional.zeroExtend G u) =
    metricNorm d (volume.restrict univ) s p (P102.Fractional.zeroExtend G u) by simp,
    metricNorm_euclidean, metricNorm_euclidean]
  simp only [P102.Fractional.domainMeasure, Measure.restrict_univ]
  calc
    _ ≤ eLpNorm u p (volume.restrict G) + (P102.Fractional.seminorm G s p u +
        (1 + (A : ℝ≥0∞)) * eLpNorm u p (volume.restrict G)) := by
      rw [P102.Fractional.zeroExtend, hnorm]
      exact add_le_add le_rfl hroot
    _ ≤ ((2 + A : ℝ≥0) : ℝ≥0∞) *
        (eLpNorm u p (volume.restrict G) + P102.Fractional.seminorm G s p u) := by
      simp only [ENNReal.coe_add, ENNReal.coe_ofNat]
      calc
        _ = (2 + (A : ℝ≥0∞)) * eLpNorm u p (volume.restrict G) +
            1 * P102.Fractional.seminorm G s p u := by ring
        _ ≤ _ := by
          rw [mul_add]
          gcongr
          exact (by norm_num : (1 : ℝ≥0∞) ≤ 2).trans le_self_add

/-- The single-chart estimate includes the whole-space artificial-edge term.
The graph, multiplier, and separated zero-extension constants are chosen before
both the scalar field and the representative. -/
theorem localized_estimate : Expected.LocalizedEstimate := by
  intro m hm Ω hΩ C r a hr hrR ha haH χ hχ hc hsupp s hs hs1 p hp hpt
  let : Fact (1 ≤ p) := ⟨hp⟩
  obtain ⟨T, hTpos, hT⟩ := GraphFractionalTransport.local_graph_comparison m hm s hs hs1 p hp hpt C.constant
  obtain ⟨M, L, hL, hM⟩ := cutoff_bounds C χ hχ hc
  obtain ⟨A, hA⟩ := multiplier_norm_bound.{0} m hm s hs hs1 p hpt.ne M L
  obtain ⟨D, hD⟩ := zero_extension_norm_bound.{0} m hm s hs hs1 p hpt.ne
    (C.radius - r) (sub_pos.mpr hrR)
  refine ⟨D * A * T + 1, by positivity, ?_⟩
  intro 𝕜 _ g hg
  let B := ball C.center C.radius
  let ν := GraphFractionalTransport.graphMeasure C.frame C.graphFunction B
  let u₀ : P102.U4.Space m → 𝕜 := g ∘ chartGraph C
  let φ : P102.U4.Space m → 𝕜 := fun x => (χ (chartGraph C x) : 𝕜)
  have hgν : MemLp g p ν := hg.mono_measure (graphMeasure_le_surfaceMeasure C)
  obtain ⟨_, _, hlp, _, _, _, hsemi, _, hmem⟩ :=
    hT C.center C.radius C.radius_pos C.graphFunction C.graph_lipschitz C.frame 𝕜 g
  have hu : MemLp u₀ p (P102.Fractional.domainMeasure B) := hmem.mp hgν
  have hφ : LipschitzOnWith L φ B := by
    simpa only [φ, B, Function.comp_def, one_mul] using RCLike.lipschitzWith_ofReal.comp_lipschitzOnWith hL
  have hφM : ∀ x ∈ B, ‖φ x‖ ≤ M := by
    intro x hx
    simpa only [φ, RCLike.norm_ofReal, Real.norm_eq_abs] using hM x hx
  obtain ⟨hw, hwbound⟩ := hA B isOpen_ball φ hφ hφM u₀ hu
  have hsep : P102.Fractional.SupportedAway B univ (C.radius - r)
      (fun x => φ x * u₀ x) := by
    simpa only [φ, u₀, Function.comp_apply, RCLike.real_smul_eq_coe_mul] using
      cutoff_supportedAway C χ hsupp g
  obtain ⟨hv, hvbound⟩ := hD B isOpen_ball (fun x => φ x * u₀ x) hw hsep
  have hvdef : P102.Fractional.zeroExtend B (fun x => φ x * u₀ x) =
      localizedPullback C χ g := by
    classical
    funext x
    simp only [P102.Fractional.zeroExtend, Set.indicator_apply, localizedPullback,
      φ, u₀, Function.comp_apply, RCLike.real_smul_eq_coe_mul, B]
  rw [hvdef] at hv hvbound
  refine ⟨hv, ?_⟩
  have huBound : metricNorm m (volume.restrict B) s p u₀ ≤
      (T : ℝ≥0∞) * metricNorm m ν s p g := by
    exact (add_le_add hlp hsemi).trans_eq (mul_add _ _ _).symm
  have hνBound := metricNorm_mono_measure m s p (graphMeasure_le_surfaceMeasure C) g
  calc
    _ ≤ (D : ℝ≥0∞) * metricNorm m (volume.restrict B) s p (fun x => φ x * u₀ x) := hvbound
    _ ≤ (D : ℝ≥0∞) * ((A : ℝ≥0∞) * metricNorm m (volume.restrict B) s p u₀) := by
      gcongr
    _ ≤ (D : ℝ≥0∞) * ((A : ℝ≥0∞) * ((T : ℝ≥0∞) * metricNorm m ν s p g)) := by
      gcongr
    _ ≤ (D : ℝ≥0∞) * ((A : ℝ≥0∞) * ((T : ℝ≥0∞) * metricNorm m (surfaceMeasure Ω) s p g)) := by
      gcongr
    _ = ((D * A * T : ℝ≥0) : ℝ≥0∞) * metricNorm m (surfaceMeasure Ω) s p g := by
      simp only [ENNReal.coe_mul]
      ring
    _ ≤ _ := by
      gcongr
      exact le_self_add

/-- Null sets are transported using the actual lower geometric measure bound;
no Borel hypothesis is imposed on the two representatives. -/
theorem representative_independence : Expected.RepresentativeIndependence := by
  intro m Ω C χ 𝕜 _ g h hgh
  obtain ⟨f, hf, heq, hle, _⟩ := GraphFractionalTransport.pushforward_comparison m (ball C.center C.radius) isOpen_ball
    C.graphFunction C.constant C.graph_lipschitz C.frame
  have hν : g =ᵐ[GraphFractionalTransport.graphMeasure C.frame C.graphFunction
      (ball C.center C.radius)] h :=
    hgh.filter_mono (ae_mono (graphMeasure_le_surfaceMeasure C))
  have hmap : g =ᵐ[Measure.map f (volume.restrict (ball C.center C.radius))] h :=
    hν.filter_mono (ae_mono hle)
  have hbase := ae_of_ae_map hf.measurable.aemeasurable hmap
  have hall := (ae_restrict_iff' isOpen_ball.measurableSet).mp hbase
  filter_upwards [hall] with x hx
  classical
  by_cases hxb : x ∈ ball C.center C.radius
  · have he := heq hxb
    have hxgh : g (chartGraph C x) = h (chartGraph C x) := by
      simpa only [chartGraph, he] using hx hxb
    simp only [localizedPullback, ite_eq_left hxb, hxgh]
  · simp only [localizedPullback, ite_eq_right hxb]

end P102.Trace.BoundaryChartLocalization
