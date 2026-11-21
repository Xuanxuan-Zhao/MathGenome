import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.TruncatedGreenIdentity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CornerDecay
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.FiniteCircularArcs
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.DiskUnionBoundarySectors
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CircularCornerRounding
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CutCircularGeometry
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.PiecewiseCircularGreen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff NNReal ComplexConjugate

namespace D12Complex.TruncatedGreenIdentity
open CircularExhaustion

lemma normalFlux_bound (u v : ℂ → ℝ) (z ν : ℂ) (hν : ‖ν‖ ≤ 1) :
    |normalFlux u v z ν| ≤ |u z| * ‖gradient v z‖ + |v z| * ‖gradient u z‖ := by
  have h₁ : |inner ℝ (gradient v z) ν| ≤ ‖gradient v z‖ := by
    calc
      _ ≤ ‖gradient v z‖ * ‖ν‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖gradient v z‖ * 1 := mul_le_mul_of_nonneg_left hν (norm_nonneg _)
      _ = _ := mul_one _
  have h₂ : |inner ℝ (gradient u z) ν| ≤ ‖gradient u z‖ := by
    calc
      _ ≤ ‖gradient u z‖ * ‖ν‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖gradient u z‖ * 1 := mul_le_mul_of_nonneg_left hν (norm_nonneg _)
      _ = _ := mul_one _
  unfold normalFlux
  calc
    _ ≤ |u z * inner ℝ (gradient v z) ν| + |v z * inner ℝ (gradient u z) ν| := abs_sub _ _
    _ ≤ _ := by
      simpa only [abs_mul] using add_le_add
        (mul_le_mul_of_nonneg_left h₁ (abs_nonneg (u z)))
        (mul_le_mul_of_nonneg_left h₂ (abs_nonneg (v z)))

lemma norm_inwardCircleNormal (t : ℝ) : ‖inwardCircleNormal t‖ = 1 := by
  simp [inwardCircleNormal, Complex.norm_exp]

lemma norm_arcParam_sub (c : ℂ) (r t : ℝ) (hr : 0 ≤ r) :
    ‖arcParam c r t - c‖ = r := by
  simp [arcParam, Complex.norm_exp, abs_of_nonneg hr]

/-- The factor r in the flux integral is the actual arclength speed. -/
lemma norm_deriv_arcParam (c : ℂ) (r t : ℝ) (hr : 0 ≤ r) :
    ‖deriv (arcParam c r) t‖ = r := by
  change ‖deriv (circleMap c r) t‖ = r
  rw [(FiniteCircularArcs.circle_hasDerivAt c r t).deriv]
  simp [Complex.norm_exp, abs_of_nonneg hr]

/-- This normal points from the cut region into the deleted closed disk. -/
lemma inwardCircleNormal_eq_radial (c : ℂ) (r t : ℝ) (hr : 0 < r) :
    inwardCircleNormal t = -(arcParam c r t - c) / (r : ℂ) := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  apply (eq_div_iff hr').mpr
  simp only [inwardCircleNormal, arcParam, add_sub_cancel_left]
  ring

/-- The definition is the unsigned arclength flux with the deleted-circle
outward normal, rather than a choice of positive traversal orientation. -/
lemma circleFluxIntegrand_eq_normal_arclength (D : Set ℂ) (u v : ℂ → ℝ)
    (c : ℂ) (r t : ℝ) (hr : 0 < r) :
    circleFluxIntegrand D u v c r t =
      if arcParam c r t ∈ D then
        normalFlux u v (arcParam c r t) (-(arcParam c r t - c) / (r : ℂ)) *
          ‖deriv (arcParam c r) t‖ else 0 := by
  rw [norm_deriv_arcParam c r t hr.le, ← inwardCircleNormal_eq_radial c r t hr]
  rfl

/-- The density is O(r^(2α-1)); multiplying by arclength speed r gives
O(r^(2α)). No sign restriction is imposed on 2α-1. -/
lemma circleFluxIntegrand_bound {D : Set ℂ} {u v : ℂ → ℝ} {c : ℂ}
    {α C₁ C₂ δ r : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hu : ∀ z ∈ D, ‖z-c‖ < δ →
      |u z| ≤ C₁ * ‖z-c‖ ^ α ∧ ‖gradient u z‖ ≤ C₁ * ‖z-c‖ ^ (α-1))
    (hv : ∀ z ∈ D, ‖z-c‖ < δ →
      |v z| ≤ C₂ * ‖z-c‖ ^ α ∧ ‖gradient v z‖ ≤ C₂ * ‖z-c‖ ^ (α-1))
    (hr : 0 < r) (hrδ : r < δ) (t : ℝ) :
    |circleFluxIntegrand D u v c r t| ≤ (2 * C₁ * C₂) * r ^ (2 * α) := by
  have hp : 0 ≤ r ^ α := Real.rpow_nonneg hr.le _
  have hq : 0 ≤ r ^ (α-1) := Real.rpow_nonneg hr.le _
  have hpow : r ^ α * r ^ (α-1) * r = r ^ (2 * α) := by
    calc
      _ = r ^ (α + (α-1)) * r ^ (1 : ℝ) := by
        rw [Real.rpow_add hr, Real.rpow_one]
      _ = r ^ (α + (α-1) + 1) := (Real.rpow_add hr _ _).symm
      _ = _ := by congr 1; ring
  unfold circleFluxIntegrand
  split_ifs with hz
  · have hn := norm_arcParam_sub c r t hr.le
    obtain ⟨hu₁, hu₂⟩ := hu _ hz (by simpa [hn] using hrδ)
    obtain ⟨hv₁, hv₂⟩ := hv _ hz (by simpa [hn] using hrδ)
    rw [hn] at hu₁ hu₂ hv₁ hv₂
    rw [abs_mul, abs_of_pos hr]
    calc
      |normalFlux u v (arcParam c r t) (inwardCircleNormal t)| * r ≤
          (|u (arcParam c r t)| * ‖gradient v (arcParam c r t)‖ +
            |v (arcParam c r t)| * ‖gradient u (arcParam c r t)‖) * r :=
        mul_le_mul_of_nonneg_right (normalFlux_bound _ _ _ _
          (norm_inwardCircleNormal t).le) hr.le
      _ ≤ ((C₁ * r ^ α) * (C₂ * r ^ (α-1)) +
        (C₂ * r ^ α) * (C₁ * r ^ (α-1))) * r := by
        gcongr
      _ = (2 * C₁ * C₂) * (r ^ α * r ^ (α-1) * r) := by ring
      _ = _ := by rw [hpow]
  · simp only [abs_zero]
    positivity

lemma continuousOn_gradient_of_contDiffOn {U : Set ℂ} {u : ℂ → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) : ContinuousOn (gradient u) U := by
  have hd := (hu.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).continuousOn_fderiv_of_isOpen hU le_rfl
  exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp_continuousOn hd

/-- Measurability is proved on the open angular set of interior arcs before
zero extension. No boundary gradient representative is required. -/
lemma circleFluxIntegrand_aestronglyMeasurable {D : Set ℂ} {u v : ℂ → ℝ} {c : ℂ}
    {R r : ℝ} (hD : IsOpen D) (hr : 0 ≤ r) (hrR : r < R)
    (hu : HarmonicOn (D ∩ ball c R) u) (hv : HarmonicOn (D ∩ ball c R) v) :
    AEStronglyMeasurable (circleFluxIntegrand D u v c r) volume := by
  let A : Set ℝ := (arcParam c r) ⁻¹' D
  have hc : Continuous (arcParam c r) := by unfold arcParam; fun_prop
  have hA : MeasurableSet A := (hD.preimage hc).measurableSet
  have hmap : MapsTo (arcParam c r) A (D ∩ ball c R) := by
    intro t ht
    exact ⟨ht, by simpa [mem_ball, dist_eq_norm, norm_arcParam_sub c r t hr] using hrR⟩
  have huc : ContinuousOn (fun t => u (arcParam c r t)) A :=
    hu.2.1.continuousOn.comp hc.continuousOn hmap
  have hvc : ContinuousOn (fun t => v (arcParam c r t)) A :=
    hv.2.1.continuousOn.comp hc.continuousOn hmap
  have hug : ContinuousOn (fun t => gradient u (arcParam c r t)) A :=
    (continuousOn_gradient_of_contDiffOn hu.1 hu.2.1).comp hc.continuousOn hmap
  have hvg : ContinuousOn (fun t => gradient v (arcParam c r t)) A :=
    (continuousOn_gradient_of_contDiffOn hv.1 hv.2.1).comp hc.continuousOn hmap
  have hn : Continuous (inwardCircleNormal) := by unfold inwardCircleNormal; fun_prop
  have hf : ContinuousOn (fun t => normalFlux u v (arcParam c r t)
      (inwardCircleNormal t) * r) A :=
    ((huc.mul (hvg.inner hn.continuousOn)).sub
      (hvc.mul (hug.inner hn.continuousOn))).mul continuousOn_const
  change AEStronglyMeasurable (A.indicator (fun t => normalFlux u v (arcParam c r t)
    (inwardCircleNormal t) * r)) volume
  exact (aestronglyMeasurable_indicator_iff hA).mpr (hf.aestronglyMeasurable hA)

lemma circleFlux_bound {D : Set ℂ} {u v : ℂ → ℝ} {c : ℂ}
    {α C₁ C₂ δ r : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hu : ∀ z ∈ D, ‖z-c‖ < δ →
      |u z| ≤ C₁ * ‖z-c‖ ^ α ∧ ‖gradient u z‖ ≤ C₁ * ‖z-c‖ ^ (α-1))
    (hv : ∀ z ∈ D, ‖z-c‖ < δ →
      |v z| ≤ C₂ * ‖z-c‖ ^ α ∧ ‖gradient v z‖ ≤ C₂ * ‖z-c‖ ^ (α-1))
    (hr : 0 < r) (hrδ : r < δ) :
    |circleFlux D u v c r| ≤ (4 * Real.pi * C₁ * C₂) * r ^ (2 * α) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2 * Real.pi) (f := circleFluxIntegrand D u v c r)
    (fun t _ => by simpa only [Real.norm_eq_abs] using
      circleFluxIntegrand_bound hC₁ hC₂ hu hv hr hrδ t)
  calc
    |circleFlux D u v c r| ≤ (2 * C₁ * C₂) * r ^ (2 * α) * |2 * Real.pi - 0| := hb
    _ = _ := by rw [sub_zero, abs_of_pos (show 0 < 2 * Real.pi by positivity)]; ring

lemma circleFluxIntegrable_of_bound {D : Set ℂ} {u v : ℂ → ℝ} {c : ℂ}
    {R r K : ℝ} (hD : IsOpen D) (hr : 0 ≤ r) (hrR : r < R)
    (hu : HarmonicOn (D ∩ ball c R) u) (hv : HarmonicOn (D ∩ ball c R) v)
    (hb : ∀ t : ℝ, |circleFluxIntegrand D u v c r t| ≤ K) :
    IntervalIntegrable (circleFluxIntegrand D u v c r) volume 0 (2 * Real.pi) := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (show 0 ≤ 2 * Real.pi by positivity)).mpr
  have hm := circleFluxIntegrand_aestronglyMeasurable hD hr hrR hu hv
  exact (integrableOn_const (μ := volume) (s := Icc (0 : ℝ) (2 * Real.pi))
    (C := K) isCompact_Icc.measure_lt_top.ne).mono' hm.restrict (Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs] using hb t)

/-- The arclength estimate and positive exponent give the original corner
flux conclusion without any assumption on derivatives at the vertex. -/
theorem corner_circle_flux :
    Specs.D12Complex.Ch14.TruncatedGreenIdentity.corner_circle_flux_type := by
  intro D c θ R u v hD hθ hθ2 hchart hR hu hv huc hvc huz hvz
  obtain ⟨C₁, hC₁, δ₁, hδ₁, hδ₁R, huB⟩ :=
    CornerDecay.corner_decay D c θ R u hD hθ hθ2 hchart hR hu huc huz
  obtain ⟨C₂, hC₂, δ₂, hδ₂, hδ₂R, hvB⟩ :=
    CornerDecay.corner_decay D c θ R v hD hθ hθ2 hchart hR hv hvc hvz
  let δ := min δ₁ δ₂
  let C := 4 * Real.pi * C₁ * C₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hδR : δ ≤ R := (min_le_left _ _).trans hδ₁R
  have huB' : ∀ z ∈ D, ‖z-c‖ < δ →
      |u z| ≤ C₁ * ‖z-c‖ ^ (Real.pi / θ) ∧
      ‖gradient u z‖ ≤ C₁ * ‖z-c‖ ^ (Real.pi / θ-1) :=
    fun z hz hzn => huB z hz (hzn.trans_le (min_le_left _ _))
  have hvB' : ∀ z ∈ D, ‖z-c‖ < δ →
      |v z| ≤ C₂ * ‖z-c‖ ^ (Real.pi / θ) ∧
      ‖gradient v z‖ ≤ C₂ * ‖z-c‖ ^ (Real.pi / θ-1) :=
    fun z hz hzn => hvB z hz (hzn.trans_le (min_le_right _ _))
  have hb : ∀ r : ℝ, 0 < r → r < δ →
      |circleFlux D u v c r| ≤ C * r ^ (2 * (Real.pi / θ)) :=
    fun r hr hrδ => circleFlux_bound hC₁.le hC₂.le huB' hvB' hr hrδ
  refine ⟨C, by dsimp [C]; positivity, δ, hδ, hδR, ?_, ?_⟩
  · intro r hr hrδ
    exact ⟨circleFluxIntegrable_of_bound hD hr.le (hrδ.trans_le hδR) hu hv
      (circleFluxIntegrand_bound hC₁.le hC₂.le huB' hvB' hr hrδ), hb r hr hrδ⟩
  · have hp : 0 < 2 * (Real.pi / θ) := by positivity
    have hid : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left nhdsWithin_le_nhds
    have ht : Tendsto (fun r : ℝ => C * r ^ (2 * (Real.pi / θ)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [mul_zero] using (hid.rpow_const_nhds_zero hp).const_mul C
    apply squeeze_zero_norm' _ ht
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with r hr hrδ
    simpa only [Real.norm_eq_abs] using hb r hr hrδ

/-- A boundary cap can be chosen to avoid both interior poles. This restricts
only the neighborhood, never the functions' original hypotheses. -/
lemma boundary_cap_avoids_poles {D : Set ℂ} {a b c : ℂ} (hD : IsOpen D)
    (hc : c ∈ frontier D) (ha : a ∈ D) (hb : b ∈ D) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ ball c R, z ≠ a ∧ z ≠ b := by
  have hcD : c ∉ D := by simpa only [hD.interior_eq] using hc.2
  have hca : c ≠ a := fun h => hcD (h ▸ ha)
  have hcb : c ≠ b := fun h => hcD (h ▸ hb)
  have hmem : ({a}ᶜ ∩ {b}ᶜ : Set ℂ) ∈ 𝓝 c :=
    ((isClosed_singleton.isOpen_compl).inter isClosed_singleton.isOpen_compl).mem_nhds ⟨hca, hcb⟩
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  exact ⟨R, hR, fun z hz => hsub hz⟩

theorem normalized_pole_corner_flux :
    Specs.D12Complex.Ch14.TruncatedGreenIdentity.normalized_pole_corner_flux_type := by
  intro D corners hD hcorn a b u v ha hb hu hv c hc
  obtain ⟨θ, hθ, hθ2, hchart⟩ := hcorn.2.2 c hc
  obtain ⟨R, hR, hsub⟩ := boundary_cap_avoids_poles hD (hcorn.1 hc) ha hb
  have huH : HarmonicOn (D ∩ ball c R) u :=
    ⟨hD.inter isOpen_ball, hu.1.2.1.mono (fun z hz => ⟨hz.1, (hsub z hz.2).1⟩),
      fun z hz => hu.1.2.2 z ⟨hz.1, (hsub z hz.2).1⟩⟩
  have hvH : HarmonicOn (D ∩ ball c R) v :=
    ⟨hD.inter isOpen_ball, hv.1.2.1.mono (fun z hz => ⟨hz.1, (hsub z hz.2).2⟩),
      fun z hz => hv.1.2.2 z ⟨hz.1, (hsub z hz.2).2⟩⟩
  obtain ⟨_, _, _, _, _, _, ht⟩ := corner_circle_flux D c θ R u v hD hθ hθ2 hchart hR huH hvH
    (hu.2.1.mono (fun z hz => ⟨hz.1, (hsub z hz.2).1⟩))
    (hv.2.1.mono (fun z hz => ⟨hz.1, (hsub z hz.2).2⟩))
    (fun z hz => hu.2.2.1 z hz.1) (fun z hz => hv.2.2.1 z hz.1)
  exact ht

theorem normalized_pole_corner_flux_sum :
    Specs.D12Complex.Ch14.TruncatedGreenIdentity.normalized_pole_corner_flux_sum_type := by
  intro D corners hD hcorn a b u v ha hb hu hv ρ hρ
  have ht := tendsto_finsetSum corners (fun c hc =>
    (normalized_pole_corner_flux D corners hD hcorn a b u v ha hb hu hv c hc).comp (hρ c hc))
  simpa only [Finset.sum_const_zero, Function.comp_apply] using ht



lemma finite_disjoint_openBalls (J : Finset ℂ) (hJ : J.Nonempty) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ J, ∀ q ∈ J, p ≠ q →
      Disjoint (ball p r) (ball q r) := by
  classical
  let f : ℂ × ℂ → ℝ := fun pq => if pq.1 = pq.2 then 1 else dist pq.1 pq.2
  let d : ℝ := (J.product J).inf' (hJ.product hJ) f
  have hd : 0 < d := by
    apply (Finset.lt_inf'_iff _).mpr
    intro pq _
    simp only [f]
    split_ifs with he
    · norm_num
    · exact dist_pos.mpr he
  refine ⟨d / 3, by positivity, ?_⟩
  intro p hp q hq hpq
  apply ball_disjoint_ball
  have hpq' : d ≤ f (p, q) := Finset.inf'_le f (Finset.mem_product.mpr ⟨hp, hq⟩)
  simp only [f, hpq, ite_false] at hpq'
  linarith

lemma uniform_cut_geometry_of_separation {D : Set ℂ} {corners : Finset ℂ}
    {a b : ℂ} (hD : IsOpen D) (hc : (↑corners : Set ℂ) ⊆ frontier D)
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (hsep : ∃ r : ℝ, 0 < r ∧ ∀ p ∈ insert a (insert b corners),
      ∀ q ∈ insert a (insert b corners), p ≠ q →
        Disjoint (ball p r) (ball q r)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ra rb : ℝ) (ρ : ℂ → ℝ),
      0 < ra → ra < δ → 0 < rb → rb < δ →
      (∀ c ∈ corners, 0 < ρ c ∧ ρ c < δ) →
      closedBall a ra ⊆ D ∧ closedBall b rb ⊆ D ∧
      Disjoint (closedBall a ra) (closedBall b rb) ∧
      (∀ c ∈ corners,
        Disjoint (closedBall c (ρ c)) (closedBall a ra) ∧
        Disjoint (closedBall c (ρ c)) (closedBall b rb)) ∧
      (∀ c ∈ corners, ∀ d ∈ corners, c ≠ d →
        Disjoint (closedBall c (ρ c)) (closedBall d (ρ d))) := by
  classical
  obtain ⟨ea, hea, heaD⟩ := Metric.isOpen_iff.mp hD a ha
  obtain ⟨eb, heb, hebD⟩ := Metric.isOpen_iff.mp hD b hb
  obtain ⟨s, hs, hsep⟩ := hsep
  let δ := min ea (min eb s)
  have hδ : 0 < δ := lt_min hea (lt_min heb hs)
  have hδa : δ ≤ ea := min_le_left _ _
  have hδb : δ ≤ eb := (min_le_right _ _).trans (min_le_left _ _)
  have hδs : δ ≤ s := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  intro ra rb ρ _ hra _ hrb hρ
  have has : closedBall a ra ⊆ ball a s := closedBall_subset_ball (hra.trans_le hδs)
  have hbs : closedBall b rb ⊆ ball b s := closedBall_subset_ball (hrb.trans_le hδs)
  have hcs : ∀ c ∈ corners, closedBall c (ρ c) ⊆ ball c s := by
    intro c hc
    exact closedBall_subset_ball ((hρ c hc).2.trans_le hδs)
  have hca : ∀ c ∈ corners, c ≠ a := by
    intro c hcm hca
    have hcf : a ∈ frontier D := hca ▸ hc hcm
    exact (hD.frontier_eq ▸ hcf).2 ha
  have hcb : ∀ c ∈ corners, c ≠ b := by
    intro c hcm hcb
    have hcf : b ∈ frontier D := hcb ▸ hc hcm
    exact (hD.frontier_eq ▸ hcf).2 hb
  have ham : a ∈ insert a (insert b corners) := Finset.mem_insert_self _ _
  have hbm : b ∈ insert a (insert b corners) := by simp
  have hcm : ∀ c ∈ corners, c ∈ insert a (insert b corners) := by
    intro c hc
    simp only [Finset.mem_insert]
    exact Or.inr (Or.inr hc)
  refine ⟨(closedBall_subset_ball (hra.trans_le hδa)).trans heaD,
    (closedBall_subset_ball (hrb.trans_le hδb)).trans hebD,
    (hsep a ham b hbm hab).mono has hbs, ?_, ?_⟩
  · intro c hcc
    exact ⟨(hsep c (hcm c hcc) a ham (hca c hcc)).mono (hcs c hcc) has,
      (hsep c (hcm c hcc) b hbm (hcb c hcc)).mono (hcs c hcc) hbs⟩
  · intro c hcc d hdd hcd
    exact (hsep c (hcm c hcc) d (hcm d hdd) hcd).mono (hcs c hcc) (hcs d hdd)

lemma uniform_cut_geometry {D : Set ℂ} {corners : Finset ℂ}
    {a b : ℂ} (hD : IsOpen D) (hc : (↑corners : Set ℂ) ⊆ frontier D)
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ra rb : ℝ) (ρ : ℂ → ℝ),
      0 < ra → ra < δ → 0 < rb → rb < δ →
      (∀ c ∈ corners, 0 < ρ c ∧ ρ c < δ) →
      closedBall a ra ⊆ D ∧ closedBall b rb ⊆ D ∧
      Disjoint (closedBall a ra) (closedBall b rb) ∧
      (∀ c ∈ corners,
        Disjoint (closedBall c (ρ c)) (closedBall a ra) ∧
        Disjoint (closedBall c (ρ c)) (closedBall b rb)) ∧
      (∀ c ∈ corners, ∀ d ∈ corners, c ≠ d →
        Disjoint (closedBall c (ρ c)) (closedBall d (ρ d))) := by
  classical
  exact uniform_cut_geometry_of_separation hD hc ha hb hab
    (finite_disjoint_openBalls _ (Finset.insert_nonempty _ _))

lemma isOpen_cutDomain {D : Set ℂ} {a b : ℂ} {ra rb : ℝ}
    {corners : Finset ℂ} {ρ : ℂ → ℝ} (hD : IsOpen D) :
    IsOpen (cutDomain D a b ra rb corners ρ) := by
  apply hD.sdiff
  exact (isClosed_closedBall.union isClosed_closedBall).union
    (isClosed_biUnion_finset fun _ _ => isClosed_closedBall)

lemma closure_cutDomain_subset {D : Set ℂ} {a b : ℂ} {ra rb : ℝ}
    {corners : Finset ℂ} {ρ : ℂ → ℝ} :
    closure (cutDomain D a b ra rb corners ρ) ⊆ closure D :=
  closure_mono sdiff_subset

lemma closure_cutDomain_avoids_open_disks {D : Set ℂ} {a b : ℂ} {ra rb : ℝ}
    {corners : Finset ℂ} {ρ : ℂ → ℝ} :
    closure (cutDomain D a b ra rb corners ρ) ⊆
      (ball a ra ∪ ball b rb ∪ ⋃ c ∈ corners, ball c (ρ c))ᶜ := by
  apply closure_minimal
  · intro z hz hz'
    apply hz.2
    rcases hz' with (ha | hb) | hc
    · exact Or.inl (Or.inl (ball_subset_closedBall ha))
    · exact Or.inl (Or.inr (ball_subset_closedBall hb))
    · obtain ⟨c, hc, hz⟩ := mem_iUnion₂.mp hc
      exact Or.inr (mem_iUnion₂.mpr ⟨c, hc, ball_subset_closedBall hz⟩)
  · exact ((isOpen_ball.union isOpen_ball).union
      (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball)).isClosed_compl

lemma closure_cutDomain_avoids_centers {D : Set ℂ} {a b : ℂ} {ra rb : ℝ}
    {corners : Finset ℂ} {ρ : ℂ → ℝ} (hra : 0 < ra) (hrb : 0 < rb)
    (hρ : ∀ c ∈ corners, 0 < ρ c) :
    a ∉ closure (cutDomain D a b ra rb corners ρ) ∧
    b ∉ closure (cutDomain D a b ra rb corners ρ) ∧
    ∀ c ∈ corners, c ∉ closure (cutDomain D a b ra rb corners ρ) := by
  have h := @closure_cutDomain_avoids_open_disks D a b ra rb corners ρ
  refine ⟨fun ha => h ha (Or.inl (Or.inl (mem_ball_self hra))),
    fun hb => h hb (Or.inl (Or.inr (mem_ball_self hrb))), ?_⟩
  intro c hc hcc
  exact h hcc (Or.inr (mem_iUnion₂.mpr ⟨c, hc, mem_ball_self (hρ c hc)⟩))

lemma isCompact_closure_cutDomain {D : Set ℂ} {a b : ℂ} {ra rb : ℝ}
    {corners : Finset ℂ} {ρ : ℂ → ℝ} (hD : Bornology.IsBounded D) :
    IsCompact (closure (cutDomain D a b ra rb corners ρ)) :=
  (hD.subset sdiff_subset).isCompact_closure

lemma harmonicOn_cutDomain {D : Set ℂ} {a b : ℂ} {ra rb : ℝ}
    {corners : Finset ℂ} {ρ : ℂ → ℝ} {u v : ℂ → ℝ}
    (hD : IsOpen D) (hu : NormalizedPole D a u) (hv : NormalizedPole D b v)
    (hra : 0 ≤ ra) (hrb : 0 ≤ rb) :
    HarmonicOn (cutDomain D a b ra rb corners ρ) u ∧
    HarmonicOn (cutDomain D a b ra rb corners ρ) v := by
  have hua : cutDomain D a b ra rb corners ρ ⊆ D \ {a} := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    intro he
    have he' : z = a := mem_singleton_iff.mp he
    subst z
    exact hz.2 (Or.inl (Or.inl (mem_closedBall_self hra)))
  have hvb : cutDomain D a b ra rb corners ρ ⊆ D \ {b} := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    intro he
    have he' : z = b := mem_singleton_iff.mp he
    subst z
    exact hz.2 (Or.inl (Or.inr (mem_closedBall_self hrb)))
  exact ⟨⟨isOpen_cutDomain hD, hu.1.2.1.mono hua, fun z hz => hu.1.2.2 z (hua hz)⟩,
    ⟨isOpen_cutDomain hD, hv.1.2.1.mono hvb, fun z hz => hv.1.2.2 z (hvb hz)⟩⟩

/-- Every new boundary point lies on an original boundary piece or a deleting circle. -/
lemma frontier_cutDomain_subset {D : Set ℂ} {a b : ℂ} {ra rb : ℝ}
    {corners : Finset ℂ} {ρ : ℂ → ℝ} :
    frontier (cutDomain D a b ra rb corners ρ) ⊆
      frontier D ∪ sphere a ra ∪ sphere b rb ∪ ⋃ c ∈ corners, sphere c (ρ c) := by
  intro z hz
  let K := closedBall a ra ∪ closedBall b rb ∪ ⋃ c ∈ corners, closedBall c (ρ c)
  have hfr : z ∈ frontier D ∪ frontier K := by
    have hz' : z ∈ frontier (D ∩ Kᶜ) := hz
    rcases frontier_inter_subset D Kᶜ hz' with hzD | hzK
    · exact Or.inl hzD.1
    · exact Or.inr (by simpa only [frontier_compl] using hzK.2)
  rcases hfr with hzD | hzK
  · exact Or.inl (Or.inl (Or.inl hzD))
  · rcases frontier_union_subset _ _ hzK with hzab | hzc
    · rcases frontier_union_subset _ _ hzab.1 with hza | hzb
      · exact Or.inl (Or.inl (Or.inr (frontier_closedBall_subset_sphere hza.1)))
      · exact Or.inl (Or.inr (frontier_closedBall_subset_sphere hzb.2))
    · obtain ⟨c, hc, hz⟩ := mem_iUnion₂.mp
        (corners.frontier_biUnion_subset (fun c => closedBall c (ρ c)) hzc.2)
      exact Or.inr (mem_iUnion₂.mpr ⟨c, hc, frontier_closedBall_subset_sphere hz⟩)

/-- The fixed cut frontier is carried by the literal finite family of original
and deleting circles; a disjoint closed-arc decomposition is a further task. -/
lemma frontier_cut_diskUnion_subset_circles {s : Finset ℂ} {r : ℂ → ℝ}
    {a b : ℂ} {ra rb : ℝ} {corners : Finset ℂ} {ρ : ℂ → ℝ} :
    frontier (cutDomain (CircularExhaustion.diskUnion s r) a b ra rb corners ρ) ⊆
      (⋃ c ∈ s, sphere c (r c)) ∪ sphere a ra ∪ sphere b rb ∪
        ⋃ c ∈ corners, sphere c (ρ c) := by
  intro z hz
  rcases frontier_cutDomain_subset hz with ((hzD | hza) | hzb) | hzc
  · have hz' := s.frontier_biUnion_subset (fun c => ball c (r c)) hzD
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp hz'
    exact Or.inl (Or.inl (Or.inl
      (mem_iUnion₂.mpr ⟨c, hc, frontier_ball_subset_sphere hzc⟩)))
  · exact Or.inl (Or.inl (Or.inr hza))
  · exact Or.inl (Or.inr hzb)
  · exact Or.inr hzc



lemma circleFlux_integrable_of_harmonic_sphere {D H : Set ℂ} {u v : ℂ → ℝ}
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hHD : sphere c r ⊆ D)
    (hH : sphere c r ⊆ H) (hu : HarmonicOn H u) (hv : HarmonicOn H v) :
    IntervalIntegrable (circleFluxIntegrand D u v c r) volume 0 (2 * Real.pi) := by
  have hc : Continuous (arcParam c r) := by unfold arcParam; fun_prop
  have hs : ∀ t : ℝ, arcParam c r t ∈ sphere c r := by
    intro t
    simp only [mem_sphere, dist_eq_norm, norm_arcParam_sub c r t hr]
  have hmap : ∀ t, arcParam c r t ∈ H := fun t => hH (hs t)
  have huc : Continuous (fun t => u (arcParam c r t)) :=
    hu.2.1.continuousOn.comp_continuous hc hmap
  have hvc : Continuous (fun t => v (arcParam c r t)) :=
    hv.2.1.continuousOn.comp_continuous hc hmap
  have hug : Continuous (fun t => gradient u (arcParam c r t)) :=
    (continuousOn_gradient_of_contDiffOn hu.1 hu.2.1).comp_continuous hc hmap
  have hvg : Continuous (fun t => gradient v (arcParam c r t)) :=
    (continuousOn_gradient_of_contDiffOn hv.1 hv.2.1).comp_continuous hc hmap
  have hn : Continuous inwardCircleNormal := by unfold inwardCircleNormal; fun_prop
  have hf : Continuous (fun t => normalFlux u v (arcParam c r t) (inwardCircleNormal t) * r) :=
    ((huc.mul (hvg.inner hn)).sub (hvc.mul (hug.inner hn))).mul continuous_const
  have heq : circleFluxIntegrand D u v c r =
      fun t => normalFlux u v (arcParam c r t) (inwardCircleNormal t) * r := by
    funext t
    simp only [circleFluxIntegrand, ite_eq_left (hHD (hs t))]
  rw [heq]
  exact hf.intervalIntegrable 0 (2 * Real.pi)

lemma normalized_pole_flux_integrable {D : Set ℂ} {a b : ℂ} {u v : ℂ → ℝ}
    {ra rb : ℝ} (hu : NormalizedPole D a u) (hv : NormalizedPole D b v)
    (hra : 0 < ra) (hrb : 0 < rb)
    (hDa : closedBall a ra ⊆ D) (hDb : closedBall b rb ⊆ D)
    (hab : Disjoint (closedBall a ra) (closedBall b rb)) :
    IntervalIntegrable (circleFluxIntegrand D u v a ra) volume 0 (2 * Real.pi) ∧
    IntervalIntegrable (circleFluxIntegrand D u v b rb) volume 0 (2 * Real.pi) := by
  let H := D \ ({a} ∪ {b})
  have heq : H = (D \ {a}) ∩ (D \ {b}) := by ext z; simp [H]; tauto
  have hH : IsOpen H := heq ▸ (hu.1.1.inter hv.1.1)
  have hHa : H ⊆ D \ {a} := by intro z hz; exact ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
  have hHb : H ⊆ D \ {b} := by intro z hz; exact ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
  have huH : HarmonicOn H u := ⟨hH, hu.1.2.1.mono hHa, fun z hz => hu.1.2.2 z (hHa hz)⟩
  have hvH : HarmonicOn H v := ⟨hH, hv.1.2.1.mono hHb, fun z hz => hv.1.2.2 z (hHb hz)⟩
  have has : sphere a ra ⊆ H := by
    intro z hz
    refine ⟨hDa (sphere_subset_closedBall hz), ?_⟩
    rintro (rfl | rfl)
    · have he : (0 : ℝ) = ra := by simpa using mem_sphere.mp hz
      linarith
    · exact Set.disjoint_left.mp hab (sphere_subset_closedBall hz) (mem_closedBall_self hrb.le)
  have hbs : sphere b rb ⊆ H := by
    intro z hz
    refine ⟨hDb (sphere_subset_closedBall hz), ?_⟩
    rintro (rfl | rfl)
    · exact Set.disjoint_left.mp hab (mem_closedBall_self hra.le) (sphere_subset_closedBall hz)
    · have he : (0 : ℝ) = rb := by simpa using mem_sphere.mp hz
      linarith
  exact ⟨circleFlux_integrable_of_harmonic_sphere hra.le (sphere_subset_closedBall.trans hDa) has huH hvH,
    circleFlux_integrable_of_harmonic_sphere hrb.le (sphere_subset_closedBall.trans hDb) hbs huH hvH⟩

open scoped Manifold

lemma exists_smooth_extension_of_locally
    {S : Set ℂ} (hS : IsClosed S) (u : ℂ → ℝ)
    (hloc : ∀ x ∈ S, ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ ∃ g : ℂ → ℝ,
      ContDiffOn ℝ ∞ g U ∧ EqOn g u (S ∩ U)) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧ EqOn g u S := by
  classical
  let t : ℂ → Set ℝ := fun x => if x ∈ S then {u x} else univ
  have ht (x : ℂ) : Convex ℝ (t x) := by
    dsimp [t]
    split_ifs
    · exact convex_singleton _
    · exact convex_univ
  have hlocal : ∀ x : ℂ, ∃ U ∈ 𝓝 x, ∃ g : ℂ → ℝ,
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ g U ∧ ∀ y ∈ U, g y ∈ t y := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨U, hU, hxU, g, hg, heq⟩ := hloc x hx
      refine ⟨U, hU.mem_nhds hxU, g, ?_, ?_⟩
      · exact contMDiffOn_iff_contDiffOn.mpr hg
      · intro y hy
        dsimp [t]
        split_ifs with hyS
        · exact heq ⟨hyS, hy⟩
        · trivial
    · refine ⟨Sᶜ, hS.isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, ?_⟩
      intro y hy
      simp [t, show y ∉ S from hy]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    𝓘(ℝ, ℂ) ht hlocal
  refine ⟨g, ?_, ?_⟩
  · exact contMDiff_iff_contDiff.mp g.contMDiff
  · intro x hx
    simpa [t, hx] using hg x

open D12Complex D12Complex.TruncatedGreenIdentity

lemma normalizedPole_local_extension
    {D S : Set ℂ} {corners : Finset ℂ} {a : ℂ} {u : ℂ → ℝ}
    (hD : IsOpen D) (hcorn : CornerSet D corners) (hu : NormalizedPole D a u)
    (hSD : S ⊆ closure D) (hSa : a ∉ S)
    (hSc : ∀ c ∈ corners, c ∉ S) :
    ∀ x ∈ S, ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ ∃ g : ℂ → ℝ,
      ContDiffOn ℝ ∞ g U ∧ EqOn g u (S ∩ U) := by
  intro x hxS
  by_cases hxD : x ∈ D
  · let U : Set ℂ := D \ {a}
    have hU : IsOpen U := hD.sdiff isClosed_singleton
    have hxU : x ∈ U := ⟨hxD, fun h => hSa (h ▸ hxS)⟩
    exact ⟨U, hU, hxU, u,
      LocalConjugateRegularity.harmonic_smooth _ _ hu.1, fun _ _ => rfl⟩
  · have hxF : x ∈ frontier D := by
      rw [hD.frontier_eq]
      exact ⟨hSD hxS, hxD⟩
    have hxC : x ∉ corners := fun h => hSc x h hxS
    have hxa : x ≠ a := fun h => hSa (h ▸ hxS)
    obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp
      (isClosed_singleton.isOpen_compl.mem_nhds hxa : ({a}ᶜ : Set ℂ) ∈ 𝓝 x)
    have huH : HarmonicOn (D ∩ ball x R) u :=
      ⟨hD.inter isOpen_ball, hu.1.2.1.mono (fun z hz => ⟨hz.1, hsub hz.2⟩),
        fun z hz => hu.1.2.2 z ⟨hz.1, hsub hz.2⟩⟩
    obtain ⟨r, hr, _, g, _, hg, heq⟩ := CornerDecay.smooth_boundary_extension
      D x R u hD (hcorn.2.1 x hxF hxC) hR huH
      (hu.2.1.mono (fun z hz => ⟨hz.1, hsub hz.2⟩))
      (fun z hz => hu.2.2.1 z hz.1)
    refine ⟨ball x r, isOpen_ball, mem_ball_self hr, g, hg, ?_⟩
    intro z hz
    exact heq ⟨hSD hz.1, hz.2⟩

lemma normalizedPole_smooth_extension
    {D S : Set ℂ} {corners : Finset ℂ} {a : ℂ} {u : ℂ → ℝ}
    (hD : IsOpen D) (hcorn : CornerSet D corners) (hu : NormalizedPole D a u)
    (hS : IsClosed S) (hSD : S ⊆ closure D) (hSa : a ∉ S)
    (hSc : ∀ c ∈ corners, c ∉ S) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧ EqOn g u S :=
  exists_smooth_extension_of_locally hS u
    (normalizedPole_local_extension hD hcorn hu hSD hSa hSc)

lemma center_not_mem_closure_of_removed_ball {K : Set ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hK : K ⊆ (closedBall c r)ᶜ) : c ∉ closure K := by
  have hsub : closure K ⊆ (ball c r)ᶜ :=
    closure_minimal (fun z hz hzball => hK hz (ball_subset_closedBall hzball))
      isOpen_ball.isClosed_compl
  exact fun hc => hsub hc (mem_ball_self hr)

lemma normalizedPole_cut_smooth_extension
    {D : Set ℂ} {corners : Finset ℂ} {a b : ℂ} {u : ℂ → ℝ}
    (hD : IsOpen D) (hcorn : CornerSet D corners) (hu : NormalizedPole D a u)
    (ra rb : ℝ) (ρ : ℂ → ℝ) (hra : 0 < ra)
    (hρ : ∀ c ∈ corners, 0 < ρ c) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧
      EqOn g u (closure (cutDomain D a b ra rb corners ρ)) := by
  apply normalizedPole_smooth_extension hD hcorn hu isClosed_closure
  · exact closure_mono (fun z hz => hz.1)
  · apply center_not_mem_closure_of_removed_ball hra
    intro z hz hza
    exact hz.2 (Or.inl (Or.inl hza))
  · intro c hc
    apply center_not_mem_closure_of_removed_ball (hρ c hc)
    intro z hz hzc
    exact hz.2 (Or.inr (mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨hc, hzc⟩⟩))

lemma harmonicOn_congr_open {U : Set ℂ} {g u : ℂ → ℝ}
    (hu : HarmonicOn U u) (heq : EqOn g u U) : HarmonicOn U g := by
  have heqAt (z : ℂ) (hz : z ∈ U) : g =ᶠ[𝓝 z] u :=
    Filter.eventually_of_mem (hu.1.mem_nhds hz) (fun w hw => heq hw)
  rw [HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U g hu.1]
  have huN := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U u hu.1).mp hu
  intro z hz
  exact (InnerProductSpace.harmonicAt_congr_nhds (heqAt z hz)).mpr (huN z hz)

lemma eqOn_gradient_on_open {U : Set ℂ} (hU : IsOpen U) {g u : ℂ → ℝ}
    (heq : EqOn g u U) : EqOn (gradient g) (gradient u) U := by
  intro z hz
  have h : g =ᶠ[𝓝 z] u := Filter.eventually_of_mem (hU.mem_nhds hz) (fun w hw => heq hw)
  exact h.gradient_eq

lemma eqOn_gradient_closure_inter {K V : Set ℂ} {g u : ℂ → ℝ}
    (hK : IsOpen K) (hV : IsOpen V) (hKV : K ⊆ V)
    (hg : ContDiffOn ℝ 2 g V) (hu : ContDiffOn ℝ 2 u V)
    (heq : EqOn g u K) :
    EqOn (gradient g) (gradient u) (closure K ∩ V) := by
  apply (eqOn_gradient_on_open hK heq).of_subset_closure
  · exact (continuousOn_gradient_of_contDiffOn hV hg).mono inter_subset_right
  · exact (continuousOn_gradient_of_contDiffOn hV hu).mono inter_subset_right
  · exact fun z hz => ⟨subset_closure hz, hKV hz⟩
  · exact inter_subset_left

lemma normalizedPole_cut_smooth_extension_full
    {D : Set ℂ} {corners : Finset ℂ} {a b : ℂ} {u : ℂ → ℝ}
    (hD : IsOpen D) (hcorn : CornerSet D corners) (hu : NormalizedPole D a u)
    (ra rb : ℝ) (ρ : ℂ → ℝ) (hra : 0 < ra)
    (hρ : ∀ c ∈ corners, 0 < ρ c) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧
      EqOn g u (closure (cutDomain D a b ra rb corners ρ)) ∧
      EqOn (gradient g) (gradient u)
        (closure (cutDomain D a b ra rb corners ρ) ∩ (D \ {a})) ∧
      HarmonicOn (cutDomain D a b ra rb corners ρ) g := by
  let K := cutDomain D a b ra rb corners ρ
  have hK : IsOpen K := isOpen_cutDomain hD
  have hKV : K ⊆ D \ {a} := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    intro heq
    have hzaeq : z = a := heq
    have hza : z ∈ closedBall a ra := by simpa only [mem_closedBall, hzaeq, dist_self] using hra.le
    exact hz.2 (Or.inl (Or.inl hza))
  obtain ⟨g, hg, heq⟩ := normalizedPole_cut_smooth_extension hD hcorn hu ra rb ρ hra hρ
  have heqK : EqOn g u K := fun z hz => heq (subset_closure hz)
  refine ⟨g, hg, heq, ?_, ?_⟩
  · exact eqOn_gradient_closure_inter hK hu.1.1 hKV
      (hg.of_le (by simp)).contDiffOn hu.1.2.1 heqK
  · apply harmonicOn_congr_open (u := u) _ heqK
    exact ⟨hK, hu.1.2.1.mono hKV, fun z hz => hu.1.2.2 z (hKV hz)⟩



lemma continuousOn_gradient_of_C1 {U : Set ℂ} {u : ℂ → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U) : ContinuousOn (gradient u) U := by
  have hd := hu.continuousOn_fderiv_of_isOpen hU le_rfl
  exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp_continuousOn hd

/-- The function and its derivatives are bounded uniformly on the fixed compact
rounding neighborhoods. The normal may vary over all unit vectors. -/
lemma compact_normalFlux_bound {K U : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    (hU : IsOpen U) {u v : ℂ → ℝ}
    (hu : ContDiffOn ℝ 1 u U) (hv : ContDiffOn ℝ 1 v U) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ K, ∀ ν : ℂ, ‖ν‖ ≤ 1 → |normalFlux u v z ν| ≤ M := by
  let A := fun z => |u z| * ‖gradient v z‖ + |v z| * ‖gradient u z‖
  have hA : ContinuousOn A K := by
    exact ((hu.continuousOn.abs.mul (continuousOn_gradient_of_C1 hU hv).norm).add
      (hv.continuousOn.abs.mul (continuousOn_gradient_of_C1 hU hu).norm)).mono hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hA
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro z hz ν hν
  calc
    |normalFlux u v z ν| ≤ A z := normalFlux_bound u v z ν hν
    _ ≤ ‖A z‖ := le_abs_self _
    _ ≤ C := hC z hz
    _ ≤ max C 0 + 1 := by linarith [le_max_left C 0]

/-- A parametrized boundary flux is controlled by the actual arclength integral.
All assumptions concern the literal scalar Lebesgue integrals. -/
lemma flux_integral_bound_by_length {u v : ℂ → ℝ} {K : Set ℂ} {M a b : ℝ}
    {γ ν : ℝ → ℂ} (hab : a ≤ b)
    (hM : ∀ z ∈ K, ∀ n : ℂ, ‖n‖ ≤ 1 → |normalFlux u v z n| ≤ M)
    (hγK : MapsTo γ (Icc a b) K) (hν : ∀ t ∈ Icc a b, ‖ν t‖ ≤ 1)
    (hf : IntervalIntegrable (fun t => normalFlux u v (γ t) (ν t) * ‖deriv γ t‖)
      volume a b)
    (hγ : IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b) :
    |∫ t in a..b, normalFlux u v (γ t) (ν t) * ‖deriv γ t‖| ≤
      M * ∫ t in a..b, ‖deriv γ t‖ := by
  calc
    _ ≤ ∫ t in a..b, ‖normalFlux u v (γ t) (ν t) * ‖deriv γ t‖‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, M * ‖deriv γ t‖ := by
      apply intervalIntegral.integral_mono_on hab hf.norm (hγ.const_mul M)
      intro t ht
      simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using
        mul_le_mul_of_nonneg_right (hM _ (hγK ht) _ (hν t ht)) (norm_nonneg (deriv γ t))
    _ = _ := intervalIntegral.integral_const_mul M _

/-- Smooth extensions and a C1 parametrization supply the integrability needed
in the arclength bound; normal continuity is enough. -/
lemma flux_integral_integrable_C1 {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℝ} (hu : ContDiffOn ℝ 1 u U) (hv : ContDiffOn ℝ 1 v U)
    {a b : ℝ} (hab : a ≤ b) {γ ν : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hγU : MapsTo γ (Icc a b) U) (hν : ContinuousOn ν (Icc a b)) :
    IntervalIntegrable (fun t => normalFlux u v (γ t) (ν t) * ‖deriv γ t‖)
        volume a b ∧
      IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b := by
  have huc := hu.continuousOn.comp hγ.continuous.continuousOn hγU
  have hvc := hv.continuousOn.comp hγ.continuous.continuousOn hγU
  have hug := (continuousOn_gradient_of_C1 hU hu).comp hγ.continuous.continuousOn hγU
  have hvg := (continuousOn_gradient_of_C1 hU hv).comp hγ.continuous.continuousOn hγU
  have hs : ContinuousOn (fun t => ‖deriv γ t‖) (Icc a b) :=
    hγ.continuous_deriv_one.norm.continuousOn
  have hf : ContinuousOn (fun t => normalFlux u v (γ t) (ν t) * ‖deriv γ t‖)
      (Icc a b) :=
    ((huc.mul (hvg.inner hν)).sub (hvc.mul (hug.inner hν))).mul hs
  exact ⟨hf.intervalIntegrable_of_Icc hab, hs.intervalIntegrable_of_Icc hab⟩

/-- Local equality on the original open domain transfers the actual gradients,
so extension flux agrees with the original flux at every interior arc point. -/
lemma normalFlux_congr_of_eqOn_open {D : Set ℂ} (hD : IsOpen D)
    {u₁ u₂ v₁ v₂ : ℂ → ℝ} (hu : EqOn u₁ u₂ D) (hv : EqOn v₁ v₂ D)
    {z : ℂ} (hz : z ∈ D) (ν : ℂ) :
    normalFlux u₁ v₁ z ν = normalFlux u₂ v₂ z ν := by
  have hue : u₁ =ᶠ[𝓝 z] u₂ := by
    filter_upwards [hD.mem_nhds hz] with w hw using hu hw
  have hve : v₁ =ᶠ[𝓝 z] v₂ := by
    filter_upwards [hD.mem_nhds hz] with w hw using hv hw
  unfold normalFlux
  rw [hu hz, hv hz, hue.gradient_eq, hve.gradient_eq]

/-- This is the analytic rounding limit once the actual changed boundary pieces
are parametrized and their arclength integrals tend to zero. -/
lemma flux_integral_tendsto_zero_of_length {ι : Type*} {l : Filter ι}
    {u v : ℂ → ℝ} {K U : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U) (hv : ContDiffOn ℝ 1 v U)
    {a b : ι → ℝ} {γ ν : ι → ℝ → ℂ} (hab : ∀ i, a i ≤ b i)
    (hγK : ∀ i, MapsTo (γ i) (Icc (a i) (b i)) K)
    (hν : ∀ i t, t ∈ Icc (a i) (b i) → ‖ν i t‖ ≤ 1)
    (hf : ∀ i, IntervalIntegrable
      (fun t => normalFlux u v (γ i t) (ν i t) * ‖deriv (γ i) t‖) volume (a i) (b i))
    (hγ : ∀ i, IntervalIntegrable (fun t => ‖deriv (γ i) t‖) volume (a i) (b i))
    (hlen : Tendsto (fun i => ∫ t in (a i)..(b i), ‖deriv (γ i) t‖) l (𝓝 0)) :
    Tendsto (fun i => ∫ t in (a i)..(b i),
      normalFlux u v (γ i t) (ν i t) * ‖deriv (γ i) t‖) l (𝓝 0) := by
  obtain ⟨M, hMpos, hM⟩ := compact_normalFlux_bound hK hKU hU hu hv
  have ht : Tendsto (fun i => M * ∫ t in (a i)..(b i), ‖deriv (γ i) t‖) l (𝓝 0) := by
    simpa only [mul_zero] using hlen.const_mul M
  apply squeeze_zero_norm' _ ht
  exact Eventually.of_forall fun i => by
    simpa only [Real.norm_eq_abs] using
      flux_integral_bound_by_length (hab i) hM (hγK i) (hν i) (hf i) (hγ i)



lemma finite_uniform_small_scale {α : Type*} (s : Finset α) {P : α → ℝ → Prop}
    (hP : ∀ c ∈ s, ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ → P c r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c ∈ s, ∀ r : ℝ, 0 < r → r < δ → P c r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert c s hc ih =>
    obtain ⟨δ₁, hδ₁, h₁⟩ := hP c (Finset.mem_insert_self _ _)
    obtain ⟨δ₂, hδ₂, h₂⟩ := ih (fun d hd => hP d (Finset.mem_insert_of_mem hd))
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    intro d hd r hr hrδ
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact h₁ r hr (hrδ.trans_le (min_le_left _ _))
    · exact h₂ d hd r hr (hrδ.trans_le (min_le_right _ _))

lemma normalized_pole_corner_integrable {D : Set ℂ} {corners : Finset ℂ}
    {a b : ℂ} {u v : ℂ → ℝ} (hD : IsOpen D) (hcorn : CornerSet D corners)
    (ha : a ∈ D) (hb : b ∈ D) (hu : NormalizedPole D a u) (hv : NormalizedPole D b v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c ∈ corners, ∀ r : ℝ, 0 < r → r < δ →
      IntervalIntegrable (circleFluxIntegrand D u v c r) volume 0 (2 * Real.pi) := by
  apply finite_uniform_small_scale corners
  intro c hc
  obtain ⟨θ, hθ, hθ2, hchart⟩ := hcorn.2.2 c hc
  obtain ⟨R, hR, hsub⟩ := boundary_cap_avoids_poles hD (hcorn.1 hc) ha hb
  have huH : HarmonicOn (D ∩ ball c R) u :=
    ⟨hD.inter isOpen_ball, hu.1.2.1.mono (fun z hz => ⟨hz.1, (hsub z hz.2).1⟩),
      fun z hz => hu.1.2.2 z ⟨hz.1, (hsub z hz.2).1⟩⟩
  have hvH : HarmonicOn (D ∩ ball c R) v :=
    ⟨hD.inter isOpen_ball, hv.1.2.1.mono (fun z hz => ⟨hz.1, (hsub z hz.2).2⟩),
      fun z hz => hv.1.2.2 z ⟨hz.1, (hsub z hz.2).2⟩⟩
  obtain ⟨_, _, δ, hδ, _, hI, _⟩ := corner_circle_flux D c θ R u v hD hθ hθ2 hchart hR huH hvH
    (hu.2.1.mono (fun z hz => ⟨hz.1, (hsub z hz.2).1⟩))
    (hv.2.1.mono (fun z hz => ⟨hz.1, (hsub z hz.2).2⟩))
    (fun z hz => hu.2.2.1 z hz.1) (fun z hz => hv.2.2.1 z hz.1)
  exact ⟨δ, hδ, fun r hr hrδ => (hI r hr hrδ).1⟩

/-- These are all the fixed-cut preconditions of the full target. The total
boundary-flux equation is not asserted by this partial result. -/
theorem fixed_cut_preconditions :
    Specs.D12Complex.Ch14.TruncatedGreenIdentity.fixed_cut_preconditions_type := by
  intro Ω s r _ j D corners hcorn a b u v ha hb hab hu hv
  have hD : IsOpen D := diskUnion_open _ _
  obtain ⟨δ₁, hδ₁, hgeom⟩ := uniform_cut_geometry hD hcorn.1 ha hb hab
  obtain ⟨δ₂, hδ₂, hcorner⟩ := normalized_pole_corner_integrable hD hcorn ha hb hu hv
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro ra rb ρ hra hraδ hrb hrbδ hρ
  obtain ⟨hDa, hDb, hdisj, hcp, hcc⟩ := hgeom ra rb ρ hra
    (hraδ.trans_le (min_le_left _ _)) hrb (hrbδ.trans_le (min_le_left _ _))
    (fun c hc => ⟨(hρ c hc).1, (hρ c hc).2.trans_le (min_le_left _ _)⟩)
  obtain ⟨huH, hvH⟩ := harmonicOn_cutDomain hD hu hv hra.le hrb.le
  obtain ⟨hIa, hIb⟩ := normalized_pole_flux_integrable hu hv hra hrb hDa hDb hdisj
  exact ⟨hDa, hDb, hdisj, hcp, hcc, huH, hvH, hIa, hIb,
    fun c hc => hcorner c hc (ρ c) (hρ c hc).1
      ((hρ c hc).2.trans_le (min_le_right _ _))⟩

/-- Reflection and a partition of unity supply the literal near-closure C²
hypothesis of D04, even at every new join of a fixed cut. -/
theorem smooth_cut_extensions :
    Specs.D12Complex.Ch14.TruncatedGreenIdentity.smooth_cut_extensions_type := by
  intro D corners hD hcorn a b u v hu hv ra rb ρ hra hrb hρ
  obtain ⟨haK, hbK, hcK⟩ := @closure_cutDomain_avoids_centers D a b ra rb corners ρ hra hrb hρ
  obtain ⟨u₀, hu₀, heu⟩ := normalizedPole_smooth_extension hD hcorn hu isClosed_closure
    closure_cutDomain_subset haK hcK
  obtain ⟨v₀, hv₀, hev⟩ := normalizedPole_smooth_extension hD hcorn hv isClosed_closure
    closure_cutDomain_subset hbK hcK
  obtain ⟨huH, hvH⟩ := harmonicOn_cutDomain hD hu hv hra.le hrb.le
  exact ⟨u₀, v₀, hu₀, hv₀, heu, hev,
    harmonicOn_congr_open huH (fun z hz => heu (subset_closure hz)),
    harmonicOn_congr_open hvH (fun z hz => hev (subset_closure hz))⟩



/-- Every interior point of a deleting circle is an actual boundary point of
the remaining open set, when all other deleted closed sets are disjoint. -/
lemma sphere_inter_subset_frontier_remove {D K : Set ℂ} {c : ℂ} {r : ℝ}
    (hD : IsOpen D) (hK : IsClosed K) (hr : 0 < r)
    (hdisj : Disjoint (closedBall c r) K) :
    sphere c r ∩ D ⊆ frontier (D \ (closedBall c r ∪ K)) := by
  intro z hz
  have hzK : z ∉ K := fun h => Set.disjoint_left.mp hdisj
    (sphere_subset_closedBall hz.1) h
  have hE : IsOpen (D \ K) := hD.sdiff hK
  have hzE : z ∈ D \ K := ⟨hz.2, hzK⟩
  have hzF : z ∈ frontier ((closedBall c r)ᶜ) := by
    rw [frontier_compl, frontier_closedBall c hr.ne']
    exact hz.1
  have hlocal := frontier_inter_open_inter (s := (closedBall c r)ᶜ) hE
  have hz' : z ∈ frontier ((closedBall c r)ᶜ ∩ (D \ K)) :=
    ((Set.ext_iff.mp hlocal z).mpr ⟨hzF, hzE⟩).1
  have heq : (closedBall c r)ᶜ ∩ (D \ K) = D \ (closedBall c r ∪ K) := by
    ext w
    simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff, mem_union]
    tauto
  exact heq ▸ hz'

lemma pole_spheres_subset_frontier_cutDomain {D : Set ℂ} {a b : ℂ}
    {ra rb : ℝ} {corners : Finset ℂ} {ρ : ℂ → ℝ}
    (hD : IsOpen D) (hra : 0 < ra) (hrb : 0 < rb)
    (hab : Disjoint (closedBall a ra) (closedBall b rb))
    (hcp : ∀ c ∈ corners,
      Disjoint (closedBall c (ρ c)) (closedBall a ra) ∧
      Disjoint (closedBall c (ρ c)) (closedBall b rb)) :
    sphere a ra ∩ D ⊆ frontier (cutDomain D a b ra rb corners ρ) ∧
    sphere b rb ∩ D ⊆ frontier (cutDomain D a b ra rb corners ρ) := by
  have hclosed : IsClosed (⋃ c ∈ corners, closedBall c (ρ c)) :=
    isClosed_biUnion_finset fun _ _ => isClosed_closedBall
  constructor
  · have hdisj : Disjoint (closedBall a ra)
        (closedBall b rb ∪ ⋃ c ∈ corners, closedBall c (ρ c)) := by
      rw [disjoint_union_right]
      refine ⟨hab, Set.disjoint_left.mpr ?_⟩
      intro z hza hzc
      obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp hzc
      exact Set.disjoint_left.mp (hcp c hc).1 hzc hza
    have heq : D \ (closedBall a ra ∪
        (closedBall b rb ∪ ⋃ c ∈ corners, closedBall c (ρ c))) =
        cutDomain D a b ra rb corners ρ := by
      ext z
      simp only [cutDomain, Set.mem_sdiff, mem_union]
      tauto
    rw [← heq]
    exact sphere_inter_subset_frontier_remove hD
      (isClosed_closedBall.union hclosed) hra hdisj
  · have hdisj : Disjoint (closedBall b rb)
        (closedBall a ra ∪ ⋃ c ∈ corners, closedBall c (ρ c)) := by
      rw [disjoint_union_right]
      refine ⟨hab.symm, Set.disjoint_left.mpr ?_⟩
      intro z hzb hzc
      obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp hzc
      exact Set.disjoint_left.mp (hcp c hc).2 hzc hzb
    have heq : D \ (closedBall b rb ∪
        (closedBall a ra ∪ ⋃ c ∈ corners, closedBall c (ρ c))) =
        cutDomain D a b ra rb corners ρ := by
      ext z
      simp only [cutDomain, Set.mem_sdiff, mem_union]
      tauto
    rw [← heq]
    exact sphere_inter_subset_frontier_remove hD
      (isClosed_closedBall.union hclosed) hrb hdisj

lemma corner_sphere_subset_frontier_cutDomain {D : Set ℂ} {a b c : ℂ}
    {ra rb : ℝ} {corners : Finset ℂ} {ρ : ℂ → ℝ}
    (hD : IsOpen D) (hc : c ∈ corners) (hrc : 0 < ρ c)
    (hca : Disjoint (closedBall c (ρ c)) (closedBall a ra))
    (hcb : Disjoint (closedBall c (ρ c)) (closedBall b rb))
    (hcc : ∀ d ∈ corners, c ≠ d →
      Disjoint (closedBall c (ρ c)) (closedBall d (ρ d))) :
    sphere c (ρ c) ∩ D ⊆ frontier (cutDomain D a b ra rb corners ρ) := by
  classical
  let K := closedBall a ra ∪ closedBall b rb ∪
    ⋃ d ∈ corners.erase c, closedBall d (ρ d)
  have hK : IsClosed K :=
    (isClosed_closedBall.union isClosed_closedBall).union
      (isClosed_biUnion_finset fun _ _ => isClosed_closedBall)
  have hdisj : Disjoint (closedBall c (ρ c)) K := by
    rw [show K = _ from rfl, disjoint_union_right, disjoint_union_right]
    refine ⟨⟨hca, hcb⟩, Set.disjoint_left.mpr ?_⟩
    intro z hzc hzd
    obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp hzd
    exact Set.disjoint_left.mp (hcc d (Finset.mem_erase.mp hd).2
      (Finset.mem_erase.mp hd).1.symm) hzc hzd
  have hunion : closedBall c (ρ c) ∪ K =
      closedBall a ra ∪ closedBall b rb ∪ ⋃ d ∈ corners, closedBall d (ρ d) := by
    ext z
    simp only [K, mem_union, mem_iUnion, Finset.mem_erase]
    constructor
    · rintro (hzc | (hzab | ⟨d, ⟨hdc, hd⟩, hzd⟩))
      · exact Or.inr ⟨c, hc, hzc⟩
      · exact Or.inl hzab
      · exact Or.inr ⟨d, hd, hzd⟩
    · rintro (hzab | ⟨d, hd, hzd⟩)
      · exact Or.inr (Or.inl hzab)
      · by_cases hdc : d = c
        · subst d; exact Or.inl hzd
        · exact Or.inr (Or.inr ⟨d, ⟨hdc, hd⟩, hzd⟩)
  have heq : D \ (closedBall c (ρ c) ∪ K) =
      cutDomain D a b ra rb corners ρ := by rw [hunion]; rfl
  rw [← heq]
  exact sphere_inter_subset_frontier_remove hD hK hrc hdisj


/-- The exterior of the deleted disk has an actual conformal smooth-boundary
chart. Its chart records the cut side of the circle. -/
lemma exterior_closedBall_sector_chart (c p : ℂ) (R : ℝ) (hR : 0 < R)
    (hp : dist p c = R) : SectorChart ((closedBall c R)ᶜ) p Real.pi := by
  apply CircularExhaustion.sectorChart_of_geometry
  let q := 2 * c - p
  have hpq : p ≠ q := by
    intro h
    have hpc : p = c := by dsimp [q] at h; linear_combination h / 2
    have : R = 0 := by simpa [hpc] using hp.symm
    linarith
  let f := fun z => Complex.I * (z - p) / (z - q)
  let g := fun w => (w * q - Complex.I * p) / (w - Complex.I)
  have hpair := DiskUnionBoundarySectors.rational_chart p q Complex.I hpq (by simp)
  refine ⟨{z | z ≠ q}, {w | w ≠ Complex.I}, f, g, hpq, hpair, ?_, ?_, ?_⟩
  · simp [f]
  · have hd := DiskUnionBoundarySectors.rational_chart_derivative p q Complex.I p hpq
    rw [hd.deriv]
    exact div_ne_zero (mul_ne_zero (by simp) (sub_ne_zero.mpr hpq))
      (pow_ne_zero _ (sub_ne_zero.mpr hpq))
  · intro z hz
    rw [← DiskUnionBoundarySectors.upper_half_plane_iff_polar]
    change z ∈ (closedBall c R)ᶜ ↔ 0 < (Complex.I * (z - p) / (z - q)).im
    have him : (Complex.I * (z - p) / (z - q)).im =
        -((-Complex.I * (z - p) / (z - q)).im) := by
      rw [← Complex.neg_im]
      congr 1
      ring
    rw [him, DiskUnionBoundarySectors.disk_rational_im c p z R hp hz]
    have hden : 0 < ‖z - (2 * c - p)‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
    simp only [Set.mem_compl_iff, mem_closedBall, not_le]
    rw [neg_pos, div_lt_iff₀ hden, zero_mul, dist_eq_norm]
    constructor <;> intro h <;> nlinarith [norm_nonneg (z - c)]

lemma sectorChart_of_local_eq {D E W : Set ℂ} {p : ℂ} {θ : ℝ}
    (h : SectorChart E p θ) (hW : IsOpen W) (hp : p ∈ W)
    (hlocal : ∀ z ∈ W, z ∈ D ↔ z ∈ E) : SectorChart D p θ := by
  obtain ⟨U, V, f, g, hpU, hpair, hf0, hdf, heq⟩ := h
  have hnew := DiskUnionBoundarySectors.restrict_biholomorphicPair hpair
    (hpair.1.1.inter hW) (show U ∩ W ⊆ U from inter_subset_left)
  refine ⟨U ∩ W, V ∩ g ⁻¹' (U ∩ W), f, g, ⟨hpU, hp⟩, hnew, hf0, hdf, ?_⟩
  intro z hz
  exact (hlocal z hz.2).trans (heq z hz.1)

/-- Removing a closed set which avoids the point preserves the sector chart
of the disk exterior. All hypotheses concern literal sets. -/
lemma sectorChart_sdiff_closedBall {D K : Set ℂ} {c p : ℂ} {R : ℝ}
    (hD : IsOpen D) (hK : IsClosed K) (hpD : p ∈ D) (hpK : p ∉ K)
    (hR : 0 < R) (hp : p ∈ sphere c R) :
    SectorChart (D \ (closedBall c R ∪ K)) p Real.pi := by
  apply sectorChart_of_local_eq
    (exterior_closedBall_sector_chart c p R hR (mem_sphere.mp hp))
    (hD.inter hK.isOpen_compl) ⟨hpD, hpK⟩
  intro z hz
  simp only [Set.mem_sdiff, mem_union, Set.mem_compl_iff]
  exact ⟨fun h => fun hzc => h.2 (Or.inl hzc),
    fun h => ⟨hz.1, fun hc => hc.elim h hz.2⟩⟩

lemma sectorChart_cutDomain_pole_a {D : Set ℂ} {a b p : ℂ} {ra rb : ℝ}
    {corners : Finset ℂ} {ρ : ℂ → ℝ} (hD : IsOpen D)
    (hra : 0 < ra) (hp : p ∈ sphere a ra) (hpD : p ∈ D)
    (hab : Disjoint (closedBall a ra) (closedBall b rb))
    (hc : ∀ c ∈ corners, Disjoint (closedBall c (ρ c)) (closedBall a ra)) :
    SectorChart (cutDomain D a b ra rb corners ρ) p Real.pi := by
  let K := closedBall b rb ∪ ⋃ c ∈ corners, closedBall c (ρ c)
  have hK : IsClosed K := isClosed_closedBall.union
    (isClosed_biUnion_finset fun _ _ => isClosed_closedBall)
  have hpK : p ∉ K := by
    rintro (hpb | hpc)
    · exact Set.disjoint_left.mp hab (sphere_subset_closedBall hp) hpb
    · obtain ⟨c, hc', hpc'⟩ := mem_iUnion₂.mp hpc
      exact Set.disjoint_left.mp (hc c hc') hpc' (sphere_subset_closedBall hp)
  have hlocal := sectorChart_sdiff_closedBall hD hK hpD hpK hra hp
  have heq : D \ (closedBall a ra ∪ K) = cutDomain D a b ra rb corners ρ := by
    simp only [cutDomain, K, union_assoc]
  exact heq ▸ hlocal

lemma sectorChart_cutDomain_pole_b {D : Set ℂ} {a b p : ℂ} {ra rb : ℝ}
    {corners : Finset ℂ} {ρ : ℂ → ℝ} (hD : IsOpen D)
    (hrb : 0 < rb) (hp : p ∈ sphere b rb) (hpD : p ∈ D)
    (hab : Disjoint (closedBall a ra) (closedBall b rb))
    (hc : ∀ c ∈ corners, Disjoint (closedBall c (ρ c)) (closedBall b rb)) :
    SectorChart (cutDomain D a b ra rb corners ρ) p Real.pi := by
  have h := sectorChart_cutDomain_pole_a hD hrb hp hpD hab.symm hc
  have heq : cutDomain D b a rb ra corners ρ = cutDomain D a b ra rb corners ρ := by
    simp only [cutDomain, union_comm (closedBall b rb) (closedBall a ra)]
  exact heq ▸ h

lemma sectorChart_cutDomain_corner_circle {D : Set ℂ} {a b c p : ℂ} {ra rb : ℝ}
    {corners : Finset ℂ} {ρ : ℂ → ℝ} (hD : IsOpen D) (hc : c ∈ corners)
    (hρc : 0 < ρ c) (hp : p ∈ sphere c (ρ c)) (hpD : p ∈ D)
    (hca : Disjoint (closedBall c (ρ c)) (closedBall a ra))
    (hcb : Disjoint (closedBall c (ρ c)) (closedBall b rb))
    (hcd : ∀ d ∈ corners, c ≠ d → Disjoint (closedBall c (ρ c)) (closedBall d (ρ d))) :
    SectorChart (cutDomain D a b ra rb corners ρ) p Real.pi := by
  let K := closedBall a ra ∪ closedBall b rb ∪
    ⋃ d ∈ corners.erase c, closedBall d (ρ d)
  have hK : IsClosed K := (isClosed_closedBall.union isClosed_closedBall).union
    (isClosed_biUnion_finset fun _ _ => isClosed_closedBall)
  have hpK : p ∉ K := by
    rintro ((hpa | hpb) | hpd)
    · exact Set.disjoint_left.mp hca (sphere_subset_closedBall hp) hpa
    · exact Set.disjoint_left.mp hcb (sphere_subset_closedBall hp) hpb
    · obtain ⟨d, hd, hpd'⟩ := mem_iUnion₂.mp hpd
      obtain ⟨hdc, hd⟩ := Finset.mem_erase.mp hd
      exact Set.disjoint_left.mp (hcd d hd hdc.symm) (sphere_subset_closedBall hp) hpd'
  have hlocal := sectorChart_sdiff_closedBall hD hK hpD hpK hρc hp
  have hcorners : (⋃ d ∈ corners, closedBall d (ρ d)) =
      closedBall c (ρ c) ∪ ⋃ d ∈ corners.erase c, closedBall d (ρ d) := by
    ext z
    constructor
    · intro hz
      obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp hz
      by_cases hdc : d = c
      · exact Or.inl (hdc ▸ hzd)
      · exact Or.inr (mem_iUnion₂.mpr ⟨d, Finset.mem_erase.mpr ⟨hdc, hd⟩, hzd⟩)
    · rintro (hzc | hzd)
      · exact mem_iUnion₂.mpr ⟨c, hc, hzc⟩
      · obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp hzd
        exact mem_iUnion₂.mpr ⟨d, (Finset.mem_erase.mp hd).2, hzd⟩
  have heq : D \ (closedBall c (ρ c) ∪ K) = cutDomain D a b ra rb corners ρ := by
    ext z
    simp only [cutDomain, hcorners, K, Set.mem_sdiff, mem_union]
    tauto
  exact heq ▸ hlocal

/-- Retained original smooth arcs keep their original conformal chart when
all deleting disks are absent from a neighborhood. -/
lemma sectorChart_cutDomain_retained {D : Set ℂ} {a b p : ℂ} {ra rb : ℝ}
    {corners : Finset ℂ} {ρ : ℂ → ℝ} (hcorners : CornerSet D corners)
    (hp : p ∈ frontier D) (hpn : p ∉ corners)
    (hpa : p ∉ closedBall a ra) (hpb : p ∉ closedBall b rb)
    (hpc : ∀ c ∈ corners, p ∉ closedBall c (ρ c)) :
    SectorChart (cutDomain D a b ra rb corners ρ) p Real.pi := by
  let K := closedBall a ra ∪ closedBall b rb ∪ ⋃ c ∈ corners, closedBall c (ρ c)
  have hK : IsClosed K := (isClosed_closedBall.union isClosed_closedBall).union
    (isClosed_biUnion_finset fun _ _ => isClosed_closedBall)
  have hpK : p ∉ K := by
    rintro ((hpa' | hpb') | hpc')
    · exact hpa hpa'
    · exact hpb hpb'
    · obtain ⟨c, hc, hpc'⟩ := mem_iUnion₂.mp hpc'
      exact hpc c hc hpc'
  apply sectorChart_of_local_eq (hcorners.2.1 p hp hpn) hK.isOpen_compl hpK
  intro z hz
  exact and_iff_left hz


/-- Closed-set agreement transfers flux at a boundary point provided both
functions are C² on an open ambient set containing the approaching cut. -/
lemma normalFlux_congr_closure_inter {K V : Set ℂ}
    (hK : IsOpen K) (hV : IsOpen V) (hKV : K ⊆ V)
    {g₁ g₂ u v : ℂ → ℝ}
    (hg₁ : ContDiffOn ℝ 2 g₁ V) (hg₂ : ContDiffOn ℝ 2 g₂ V)
    (hu : ContDiffOn ℝ 2 u V) (hv : ContDiffOn ℝ 2 v V)
    (h₁ : EqOn g₁ u (closure K)) (h₂ : EqOn g₂ v (closure K))
    {z : ℂ} (hz : z ∈ closure K ∩ V) (ν : ℂ) :
    normalFlux g₁ g₂ z ν = normalFlux u v z ν := by
  have hgrad₁ := eqOn_gradient_closure_inter hK hV hKV hg₁ hu
    (fun w hw => h₁ (subset_closure hw)) hz
  have hgrad₂ := eqOn_gradient_closure_inter hK hV hKV hg₂ hv
    (fun w hw => h₂ (subset_closure hw)) hz
  simp only [normalFlux, h₁ hz.1, h₂ hz.1, hgrad₁, hgrad₂]

/-- Transfer from a smooth extension to the original normalized-pole functions
on the part of the fixed cut closure still inside D. -/
lemma normalFlux_cut_extension {D : Set ℂ} {corners : Finset ℂ}
    {a b : ℂ} {ra rb : ℝ} {ρ : ℂ → ℝ}
    (hD : IsOpen D) (hra : 0 < ra) (hrb : 0 < rb)
    {u v g₁ g₂ : ℂ → ℝ}
    (hu : NormalizedPole D a u) (hv : NormalizedPole D b v)
    (hg₁ : ContDiff ℝ ∞ g₁) (hg₂ : ContDiff ℝ ∞ g₂)
    (h₁ : EqOn g₁ u (closure (cutDomain D a b ra rb corners ρ)))
    (h₂ : EqOn g₂ v (closure (cutDomain D a b ra rb corners ρ)))
    {z : ℂ} (hz : z ∈ closure (cutDomain D a b ra rb corners ρ))
    (hzD : z ∈ D) (ν : ℂ) :
    normalFlux g₁ g₂ z ν = normalFlux u v z ν := by
  let V := (D \ {a}) ∩ (D \ {b})
  have hV : IsOpen V := hu.1.1.inter hv.1.1
  have hKV : cutDomain D a b ra rb corners ρ ⊆ V := by
    intro w hw
    refine ⟨⟨hw.1, ?_⟩, ⟨hw.1, ?_⟩⟩
    · rintro rfl
      exact hw.2 (Or.inl (Or.inl (mem_closedBall_self hra.le)))
    · rintro rfl
      exact hw.2 (Or.inl (Or.inr (mem_closedBall_self hrb.le)))
  have havoid := @closure_cutDomain_avoids_open_disks D a b ra rb corners ρ z hz
  have hza : z ∉ ({a} : Set ℂ) := by
    rintro rfl
    exact havoid (Or.inl (Or.inl (mem_ball_self hra)))
  have hzb : z ∉ ({b} : Set ℂ) := by
    rintro rfl
    exact havoid (Or.inl (Or.inr (mem_ball_self hrb)))
  exact normalFlux_congr_closure_inter (isOpen_cutDomain hD) hV hKV
    ((hg₁.of_le (by simp)).contDiffOn) ((hg₂.of_le (by simp)).contDiffOn)
    (hu.1.2.1.mono inter_subset_left) (hv.1.2.1.mono inter_subset_right)
    h₁ h₂ ⟨hz, ⟨⟨hzD, hza⟩, ⟨hzD, hzb⟩⟩⟩ ν

lemma circleFluxIntegrand_cut_extension {D : Set ℂ} {corners : Finset ℂ}
    {a b c : ℂ} {ra rb r : ℝ} {ρ : ℂ → ℝ}
    (hD : IsOpen D) (hra : 0 < ra) (hrb : 0 < rb) (hr : 0 ≤ r)
    {u v g₁ g₂ : ℂ → ℝ}
    (hu : NormalizedPole D a u) (hv : NormalizedPole D b v)
    (hg₁ : ContDiff ℝ ∞ g₁) (hg₂ : ContDiff ℝ ∞ g₂)
    (h₁ : EqOn g₁ u (closure (cutDomain D a b ra rb corners ρ)))
    (h₂ : EqOn g₂ v (closure (cutDomain D a b ra rb corners ρ)))
    (hcircle : sphere c r ∩ D ⊆ closure (cutDomain D a b ra rb corners ρ)) :
    circleFluxIntegrand D g₁ g₂ c r = circleFluxIntegrand D u v c r := by
  funext t
  unfold circleFluxIntegrand
  split_ifs with hzD
  · have hz : arcParam c r t ∈ sphere c r := by
      simp only [mem_sphere, dist_eq_norm, norm_arcParam_sub c r t hr]
    rw [normalFlux_cut_extension hD hra hrb hu hv hg₁ hg₂ h₁ h₂
      (hcircle ⟨hz, hzD⟩) hzD]
  · rfl

lemma circleFlux_cut_extension {D : Set ℂ} {corners : Finset ℂ}
    {a b c : ℂ} {ra rb r : ℝ} {ρ : ℂ → ℝ}
    (hD : IsOpen D) (hra : 0 < ra) (hrb : 0 < rb) (hr : 0 ≤ r)
    {u v g₁ g₂ : ℂ → ℝ}
    (hu : NormalizedPole D a u) (hv : NormalizedPole D b v)
    (hg₁ : ContDiff ℝ ∞ g₁) (hg₂ : ContDiff ℝ ∞ g₂)
    (h₁ : EqOn g₁ u (closure (cutDomain D a b ra rb corners ρ)))
    (h₂ : EqOn g₂ v (closure (cutDomain D a b ra rb corners ρ)))
    (hcircle : sphere c r ∩ D ⊆ closure (cutDomain D a b ra rb corners ρ)) :
    circleFlux D g₁ g₂ c r = circleFlux D u v c r := by
  unfold circleFlux
  rw [circleFluxIntegrand_cut_extension hD hra hrb hr hu hv hg₁ hg₂ h₁ h₂ hcircle]

/-- The retained original frontier contributes zero even when the extension's
normal derivatives there are not identified with the original total functions. -/
lemma normalFlux_cut_extension_zero_on_frontier {D K : Set ℂ} {a b : ℂ}
    {u v g₁ g₂ : ℂ → ℝ}
    (hu : NormalizedPole D a u) (hv : NormalizedPole D b v)
    (h₁ : EqOn g₁ u (closure K)) (h₂ : EqOn g₂ v (closure K))
    {z : ℂ} (hz : z ∈ closure K) (hzfront : z ∈ frontier D) (ν : ℂ) :
    normalFlux g₁ g₂ z ν = 0 := by
  simp only [normalFlux, h₁ hz, h₂ hz, hu.2.2.1 z hzfront,
    hv.2.2.1 z hzfront, zero_mul, sub_zero]


/-- The transfer hypotheses on every deleting circle follow from actual
frontier membership, rather than from a presumed boundary display. -/
theorem smooth_cut_flux_transfer :
    Specs.D12Complex.Ch14.TruncatedGreenIdentity.smooth_cut_flux_transfer_type := by
  intro D corners hD hcorn a b u v hu hv ra rb ρ hra hrb hρ hab hcp hcc
  obtain ⟨u₀, v₀, hu₀, hv₀, heu, hev, huH, hvH⟩ :=
    smooth_cut_extensions D corners hD hcorn a b u v hu hv ra rb ρ hra hrb hρ
  obtain ⟨hsa, hsb⟩ := pole_spheres_subset_frontier_cutDomain hD hra hrb hab hcp
  refine ⟨u₀, v₀, hu₀, hv₀, heu, hev, huH, hvH, ?_, ?_, ?_, ?_⟩
  · exact circleFlux_cut_extension hD hra hrb hra.le hu hv hu₀ hv₀ heu hev
      (hsa.trans frontier_subset_closure)
  · exact circleFlux_cut_extension hD hra hrb hrb.le hu hv hu₀ hv₀ heu hev
      (hsb.trans frontier_subset_closure)
  · intro c hc
    exact circleFlux_cut_extension hD hra hrb (hρ c hc).le hu hv hu₀ hv₀ heu hev
      ((corner_sphere_subset_frontier_cutDomain hD hc (hρ c hc)
        (hcp c hc).1 (hcp c hc).2 (hcc c hc)).trans frontier_subset_closure)
  · intro z hz ν
    exact normalFlux_cut_extension_zero_on_frontier hu hv heu hev hz.2 hz.1 ν

lemma parametrized_length_comp_le {g : ℂ → ℂ} {V : Set ℂ} {L a b : ℝ}
    {γ : ℝ → ℂ} (hV : IsOpen V) (hg : ContDiffOn ℝ 1 g V)
    (hγ : ContDiff ℝ 1 γ) (hab : a ≤ b) (hmap : MapsTo γ (Icc a b) V)
    (hL : ∀ t ∈ Icc a b, ‖fderiv ℝ g (γ t)‖ ≤ L) :
    (∫ t in a..b, ‖deriv (g ∘ γ) t‖) ≤ L * ∫ t in a..b, ‖deriv γ t‖ := by
  have hW : IsOpen (γ ⁻¹' V) := hV.preimage hγ.continuous
  have hcomp : ContDiffOn ℝ 1 (g ∘ γ) (γ ⁻¹' V) :=
    hg.comp hγ.contDiffOn (fun _ ht => ht)
  have hderiv : ContinuousOn (fun t => ‖deriv (g ∘ γ) t‖) (Icc a b) :=
    (hcomp.continuousOn_deriv_of_isOpen hW le_rfl).norm.mono hmap
  have hbound : ∀ t ∈ Icc a b, ‖deriv (g ∘ γ) t‖ ≤ L * ‖deriv γ t‖ := by
    intro t ht
    have hgd : DifferentiableAt ℝ g (γ t) :=
      ((hg _ (hmap ht)).contDiffAt (hV.mem_nhds (hmap ht))).differentiableAt (by norm_num)
    rw [fderiv_comp_deriv t hgd (hγ.differentiable (by norm_num) t)]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hL t ht) (norm_nonneg _))
  calc
    _ ≤ ∫ t in a..b, L * ‖deriv γ t‖ := by
      apply intervalIntegral.integral_mono_on hab
        (hderiv.intervalIntegrable_of_Icc hab)
        ((hγ.continuous_deriv_one.norm.intervalIntegrable a b).const_mul L)
      exact hbound
    _ = _ := intervalIntegral.integral_const_mul L _

open CircularCornerRounding

/-- A genuine parameter-arclength estimate after the inverse corner chart.
This uses the derivative chain rule; no Hausdorff/arclength identification is assumed. -/
lemma chart_roundingArc_length_le {g : ℂ → ℂ} {L : ℝ≥0} {R ε θ : ℝ}
    (hg : ContDiffOn ℝ 1 g (ball (0 : ℂ) R))
    (hgLip : LipschitzOnWith L g (closedBall (0 : ℂ) R))
    (hε : 0 < ε) (hεR : ε < R) (hθ : 0 < θ) :
    (∫ t in (0 : ℝ)..1, ‖deriv (g ∘ roundingArc ε θ) t‖) ≤
      (L : ℝ) * (Real.pi / 2 + 6 * θ) * ε := by
  have hmap : MapsTo (roundingArc ε θ) (Icc (0 : ℝ) 1) (ball (0 : ℂ) R) := by
    intro t ht
    apply mem_ball.mpr
    rw [dist_zero_right, norm_roundingArc hε.le ht]
    nlinarith [(radialProfile_bounds ht).2]
  calc
    _ ≤ (L : ℝ) * ∫ t in (0 : ℝ)..1, ‖deriv (roundingArc ε θ) t‖ := by
      apply parametrized_length_comp_le isOpen_ball hg
        ((contDiff_roundingArc ε θ).of_le (by simp)) (by norm_num) hmap
      intro t ht
      exact norm_fderiv_le_of_lipschitzOn ℝ
        (closedBall_mem_nhds_of_mem (hmap ht)) hgLip
    _ ≤ (L : ℝ) * ((Real.pi / 2 + 6 * θ) * ε) :=
      mul_le_mul_of_nonneg_left (roundingArc_length_le hε hθ) L.coe_nonneg
    _ = _ := by ring

/-- The actual scalar flux and speed integrals are integrable for a C1 curve
on an open parameter neighborhood of the closed integration interval. -/
lemma flux_integral_integrable_C1On {U : Set ℂ} (hU : IsOpen U)
    {J : Set ℝ} (hJ : IsOpen J)
    {u v : ℂ → ℝ} (hu : ContDiffOn ℝ 1 u U) (hv : ContDiffOn ℝ 1 v U)
    {a b : ℝ} (hab : a ≤ b) {γ ν : ℝ → ℂ}
    (hγ : ContDiffOn ℝ 1 γ J) (hIJ : Icc a b ⊆ J)
    (hγU : MapsTo γ (Icc a b) U) (hν : ContinuousOn ν (Icc a b)) :
    IntervalIntegrable (fun t => normalFlux u v (γ t) (ν t) * ‖deriv γ t‖)
        volume a b ∧
      IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b := by
  have hγc := hγ.continuousOn.mono hIJ
  have huc := hu.continuousOn.comp hγc hγU
  have hvc := hv.continuousOn.comp hγc hγU
  have hug := (continuousOn_gradient_of_C1 hU hu).comp hγc hγU
  have hvg := (continuousOn_gradient_of_C1 hU hv).comp hγc hγU
  have hs : ContinuousOn (fun t => ‖deriv γ t‖) (Icc a b) :=
    (hγ.continuousOn_deriv_of_isOpen hJ le_rfl).norm.mono hIJ
  have hf : ContinuousOn (fun t => normalFlux u v (γ t) (ν t) * ‖deriv γ t‖)
      (Icc a b) :=
    ((huc.mul (hvg.inner hν)).sub (hvc.mul (hug.inner hν))).mul hs
  exact ⟨hf.intervalIntegrable_of_Icc hab, hs.intervalIntegrable_of_Icc hab⟩

/-- Quantitative first rounding-limit control for the actual pulled-back
rounding arc, for every continuous unit-bounded normal field. -/
lemma chart_roundingArc_flux_bound {g : ℂ → ℂ} {L : ℝ≥0} {R ε θ M : ℝ}
    {K U : Set ℂ} {u v : ℂ → ℝ} {ν : ℝ → ℂ}
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) (hv : ContDiffOn ℝ 1 v U)
    (hg : ContDiffOn ℝ 1 g (ball (0 : ℂ) R))
    (hgLip : LipschitzOnWith L g (closedBall (0 : ℂ) R))
    (hgK : MapsTo g (closedBall (0 : ℂ) R) K)
    (hε : 0 < ε) (hεR : ε < R) (hθ : 0 < θ) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ K, ∀ n : ℂ, ‖n‖ ≤ 1 → |normalFlux u v z n| ≤ M)
    (hνc : ContinuousOn ν (Icc (0 : ℝ) 1))
    (hν : ∀ t ∈ Icc (0 : ℝ) 1, ‖ν t‖ ≤ 1) :
    |∫ t in (0 : ℝ)..1,
      normalFlux u v ((g ∘ roundingArc ε θ) t) (ν t) *
        ‖deriv (g ∘ roundingArc ε θ) t‖| ≤
      M * (L : ℝ) * (Real.pi / 2 + 6 * θ) * ε := by
  let J := roundingArc ε θ ⁻¹' ball (0 : ℂ) R
  have hc : ContDiff ℝ 1 (roundingArc ε θ) :=
    (contDiff_roundingArc ε θ).of_le (by simp)
  have hJ : IsOpen J := isOpen_ball.preimage hc.continuous
  have hmap : MapsTo (roundingArc ε θ) (Icc (0 : ℝ) 1) (ball (0 : ℂ) R) := by
    intro t ht
    rw [mem_ball, dist_zero_right, norm_roundingArc hε.le ht]
    nlinarith [(radialProfile_bounds ht).2]
  have hγ : ContDiffOn ℝ 1 (g ∘ roundingArc ε θ) J :=
    hg.comp hc.contDiffOn (fun _ ht => ht)
  have hγK : MapsTo (g ∘ roundingArc ε θ) (Icc (0 : ℝ) 1) K :=
    fun t ht => hgK (ball_subset_closedBall (hmap ht))
  obtain ⟨hf, hs⟩ := flux_integral_integrable_C1On hU hJ hu hv
    (by norm_num : (0 : ℝ) ≤ 1) hγ hmap (fun t ht => hKU (hγK ht)) hνc
  calc
    _ ≤ M * ∫ t in (0 : ℝ)..1, ‖deriv (g ∘ roundingArc ε θ) t‖ :=
      flux_integral_bound_by_length (by norm_num) hbound hγK hν hf hs
    _ ≤ M * ((L : ℝ) * (Real.pi / 2 + 6 * θ) * ε) :=
      mul_le_mul_of_nonneg_left (chart_roundingArc_length_le hg hgLip hε hεR hθ) hM
    _ = _ := by ring

/-- At a fixed cut, compact smooth-extension bounds give the actual first
rounding limit on each explicitly parametrized inserted arc. -/
lemma chart_roundingArc_flux_tendsto_zero {g : ℂ → ℂ} {L : ℝ≥0} {R θ : ℝ}
    {K U : Set ℂ} {u v : ℂ → ℝ} {ν : ℝ → ℝ → ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hv : ContDiffOn ℝ 1 v U)
    (hg : ContDiffOn ℝ 1 g (ball (0 : ℂ) R))
    (hgLip : LipschitzOnWith L g (closedBall (0 : ℂ) R))
    (hgK : MapsTo g (closedBall (0 : ℂ) R) K) (hR : 0 < R) (hθ : 0 < θ)
    (hνc : ∀ ε : ℝ, 0 < ε → ε < R → ContinuousOn (ν ε) (Icc (0 : ℝ) 1))
    (hν : ∀ ε : ℝ, 0 < ε → ε < R → ∀ t ∈ Icc (0 : ℝ) 1, ‖ν ε t‖ ≤ 1) :
    Tendsto (fun ε : ℝ => ∫ t in (0 : ℝ)..1,
      normalFlux u v ((g ∘ roundingArc ε θ) t) (ν ε t) *
        ‖deriv (g ∘ roundingArc ε θ) t‖) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hM, hbound⟩ := compact_normalFlux_bound hK hKU hU hu hv
  have hlim : Tendsto (fun ε : ℝ =>
      (M * (L : ℝ) * (Real.pi / 2 + 6 * θ)) * ε) (𝓝[>] 0) (𝓝 0) := by
    have H : Tendsto (fun ε : ℝ =>
        (M * (L : ℝ) * (Real.pi / 2 + 6 * θ)) * ε) (𝓝 0)
        (𝓝 ((M * (L : ℝ) * (Real.pi / 2 + 6 * θ)) * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    simpa only [mul_zero] using H.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hlim
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hs : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp, hs] with ε hε hεR
  simpa only [Real.norm_eq_abs] using
    chart_roundingArc_flux_bound hU hKU hu hv hg hgLip hgK hε hεR hθ hM.le
      hbound (hνc ε hε hεR) (hν ε hε hεR)


/-- Two upper half-planes with positively ordered normals meet in a sector
whose angle is strictly between zero and π. -/
lemma intersection_halfplanes_sector {p : ℂ} (hp : 0 < p.im) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧ ∀ w : ℂ,
      (0 < w.im ∧ 0 < (p * w).im) ↔
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ t : ℝ, 0 < t ∧ t < θ ∧
        w = (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
  let φ := p.arg
  have hφ : 0 < φ := by
    have hn : 0 ≤ p.arg := Complex.arg_nonneg_iff.mpr hp.le
    by_contra h
    have he : p.arg = 0 := le_antisymm (not_lt.mp h) hn
    have hs := Complex.norm_mul_sin_arg p
    rw [he, Real.sin_zero, mul_zero] at hs
    linarith
  have hφπ : φ < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hp.ne')
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have hnp : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  have him (ρ t : ℝ) :
      (p * ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I))).im =
        (‖p‖ * ρ) * Real.sin (t + φ) := by
    have he : p * ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) =
        ((‖p‖ * ρ : ℝ) : ℂ) * Complex.exp (((t + φ : ℝ) : ℂ) * Complex.I) := by
      calc
        _ = ((‖p‖ : ℂ) * Complex.exp ((p.arg : ℂ) * Complex.I)) *
            ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) := by
          rw [Complex.norm_mul_exp_arg_mul_I]
        _ = _ := by
          dsimp [φ]
          push_cast
          rw [add_mul, Complex.exp_add]
          ring
    have polar_im (r s : ℝ) :
        ((r : ℂ) * Complex.exp ((s : ℂ) * Complex.I)).im = r * Real.sin s := by
      rw [Complex.exp_mul_I]
      simp [← Complex.ofReal_sin, ← Complex.ofReal_cos]
    rw [he, polar_im]
  have hsign {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (htπ : t < Real.pi) :
      (0 < (p * ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I))).im) ↔ t < Real.pi - φ := by
    rw [him, mul_pos_iff_of_pos_left (mul_pos hnp hρ)]
    constructor
    · intro hs
      by_contra hn
      have hlow : Real.pi ≤ t + φ := by linarith [not_lt.mp hn]
      have hhigh : t + φ ≤ 2 * Real.pi := by linarith
      have hs' := Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (show t + φ - 2 * Real.pi ≤ 0 by linarith)
        (show -Real.pi ≤ t + φ - 2 * Real.pi by linarith)
      have hn : Real.sin (t + φ) ≤ 0 := by simpa using hs'
      linarith
    · intro htφ
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  refine ⟨Real.pi - φ, by linarith, by linarith, ?_⟩
  intro w
  constructor
  · rintro ⟨hw, hpw⟩
    obtain ⟨ρ, hρ, t, ht, htπ, he⟩ :=
      (DiskUnionBoundarySectors.upper_half_plane_iff_polar w).mp hw
    refine ⟨ρ, hρ, t, ht, ?_, he⟩
    exact (hsign hρ ht htπ).mp (he ▸ hpw)
  · rintro ⟨ρ, hρ, t, ht, htθ, rfl⟩
    have htπ : t < Real.pi := by linarith
    exact ⟨(DiskUnionBoundarySectors.upper_half_plane_iff_polar _).mpr
      ⟨ρ, hρ, t, ht, htπ, rfl⟩, (hsign hρ ht htπ).mpr htθ⟩

/-- An actual rational local coordinate whose two strict linear sides have
positively ordered normals yields an actual conformal sector chart. -/
lemma sectorChart_of_straightened_halfplanes
    {D : Set ℂ} (ξ K A B : ℂ) (hA : A ≠ 0) (hp : 0 < (B / A).im)
    (hside : ∀ z : ℂ, 1 + K * (z - ξ) ≠ 0 →
      (z ∈ D ↔
        0 < (A * ((z - ξ) / (1 + K * (z - ξ)))).im ∧
        0 < (B * ((z - ξ) / (1 + K * (z - ξ)))).im)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧ SectorChart D ξ θ := by
  obtain ⟨θ, hθ, hθπ, hpolar⟩ := intersection_halfplanes_sector hp
  refine ⟨θ, hθ, hθπ, CircularExhaustion.sectorChart_of_geometry ?_⟩
  let f := fun z => A * (z - ξ) / (1 + K * (z - ξ))
  let g := fun w => ξ + w / (A - K * w)
  have hpair := DiskUnionBoundarySectors.straightening_chart ξ K A hA
  refine ⟨{z | 1 + K * (z - ξ) ≠ 0}, {w | A - K * w ≠ 0},
    f, g, by simp, hpair, by simp [f], ?_, ?_⟩
  · have hd := DiskUnionBoundarySectors.straightening_chart_derivative ξ K A ξ (by simp)
    rw [hd.deriv]
    simpa using hA
  · intro z hz
    rw [← hpolar, hside z hz]
    have hfirst : f z = A * ((z - ξ) / (1 + K * (z - ξ))) := by dsimp [f]; ring
    rw [hfirst]
    have hsecond : B / A * (A * ((z - ξ) / (1 + K * (z - ξ)))) =
        B * ((z - ξ) / (1 + K * (z - ξ))) := by field_simp
    rw [hsecond]

/-- The strict exterior side of a circle is sent to the other open half-plane
by the same simultaneous circle-straightening coordinate. -/
lemma straightening_exterior_side (ξ c K z : ℂ) (R : ℝ) (hR : 0 < R)
    (hξ : dist ξ c = R) (hK : 2 * ((ξ - c) * K).re = 1)
    (hz : 1 + K * (z - ξ) ≠ 0) :
    z ∉ closedBall c R ↔
      0 < (Complex.I * conj (ξ - c) * ((z - ξ) / (1 + K * (z - ξ)))).im := by
  have he : ‖z - c‖ ^ 2 - R ^ 2 = ‖z - ξ‖ ^ 2 +
      2 * (conj (ξ - c) * (z - ξ)).re := by
    have hnorm : ‖ξ - c‖ ^ 2 = R ^ 2 := by rw [← dist_eq_norm, hξ]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im] at hnorm ⊢
    nlinarith
  have hden : 0 < ‖1 + K * (z - ξ)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hid := DiskUnionBoundarySectors.straightening_real_identity (ξ - c) K (z - ξ) hK
  rw [← he] at hid
  have him : (Complex.I * conj (ξ - c) * ((z - ξ) / (1 + K * (z - ξ)))).im =
      (conj (ξ - c) * ((z - ξ) / (1 + K * (z - ξ)))).re := by
    rw [mul_assoc]
    simp
  rw [him]
  simp only [mem_closedBall, not_le, dist_eq_norm]
  constructor
  · intro h
    have : 0 < (‖z - c‖ ^ 2 - R ^ 2) / ‖1 + K * (z - ξ)‖ ^ 2 :=
      div_pos (by nlinarith [norm_nonneg (z - c)]) hden
    linarith
  · intro h
    have : 0 < (‖z - c‖ ^ 2 - R ^ 2) / ‖1 + K * (z - ξ)‖ ^ 2 := by linarith
    have := (div_pos_iff_of_pos_right hden).mp this
    nlinarith [norm_nonneg (z - c)]

/-- A transverse original circle and deleting circle meet in a genuine
conformal corner of the literal cut side, with angle strictly below π. -/
lemma two_circle_cut_sector_chart {c d ξ : ℂ} {R S : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hξc : dist ξ c = R) (hξd : dist ξ d = S)
    (hext : dist c d ≠ R + S) (hint : dist c d ≠ |R - S|) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧
      SectorChart (ball c R \ closedBall d S) ξ θ := by
  let a := ξ - c
  let b := ξ - d
  have ha : a ≠ 0 := by
    intro h
    have : dist ξ c = 0 := by simpa [a, dist_eq_norm] using congrArg norm h
    linarith
  have hb : b ≠ 0 := by
    intro h
    have : dist ξ d = 0 := by simpa [b, dist_eq_norm] using congrArg norm h
    linarith
  have hdet := DiskUnionBoundarySectors.two_circle_transverse hR hS hξc hξd hext hint
  obtain ⟨K, hKa, hKb⟩ :=
    DiskUnionBoundarySectors.simultaneous_straightening_coefficient hdet
  let A := -Complex.I * conj a
  let B := Complex.I * conj b
  have hA : A ≠ 0 := mul_ne_zero (by simp) (by simpa using ha)
  have hB : B ≠ 0 := mul_ne_zero (by simp) (by simpa using hb)
  have hratio : B / A = -conj b / conj a := by
    dsimp [A, B]
    field_simp
  have him : (B / A).im = (a.re * b.im - a.im * b.re) / Complex.normSq a := by
    rw [hratio, Complex.div_im]
    simp only [Complex.neg_im, Complex.neg_re, Complex.conj_im, Complex.conj_re,
      Complex.normSq_conj]
    ring
  have hpne : (B / A).im ≠ 0 := by
    rw [him]
    exact div_ne_zero hdet ((Complex.normSq_pos.mpr ha).ne')
  have hside : ∀ z : ℂ, 1 + K * (z - ξ) ≠ 0 →
      (z ∈ ball c R \ closedBall d S ↔
        0 < (A * ((z - ξ) / (1 + K * (z - ξ)))).im ∧
        0 < (B * ((z - ξ) / (1 + K * (z - ξ)))).im) := by
    intro z hz
    exact and_congr
      (DiskUnionBoundarySectors.straightening_disk_side ξ c K z R hR hξc hKa hz)
      (straightening_exterior_side ξ d K z S hS hξd hKb hz)
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · have hq : A / B = (B / A)⁻¹ := by
      simp [div_eq_mul_inv]
    have hp0 : B / A ≠ 0 := div_ne_zero hB hA
    have hqpos : 0 < (A / B).im := by
      rw [hq, Complex.inv_im]
      exact div_pos (neg_pos.mpr hpneg) (Complex.normSq_pos.mpr hp0)
    apply sectorChart_of_straightened_halfplanes ξ K B A hB hqpos
    intro z hz
    exact (hside z hz).trans and_comm
  · exact sectorChart_of_straightened_halfplanes ξ K A B hA hppos hside

/-- The literal cut has the mixed-circle chart whenever its original boundary
is locally a single disk and the other removed closed set is absent. -/
lemma sectorChart_sdiff_at_circle_join {D W K : Set ℂ} {c d ξ : ℂ} {R S : ℝ}
    (hW : IsOpen W) (hξW : ξ ∈ W)
    (hlocal : ∀ z ∈ W, z ∈ D ↔ z ∈ ball c R)
    (hK : IsClosed K) (hξK : ξ ∉ K)
    (hR : 0 < R) (hS : 0 < S) (hξc : dist ξ c = R) (hξd : dist ξ d = S)
    (hext : dist c d ≠ R + S) (hint : dist c d ≠ |R - S|) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧
      SectorChart (D \ (closedBall d S ∪ K)) ξ θ := by
  obtain ⟨θ, hθ, hθπ, U, V, f, g, hξU, hpair, hf0, hdf, hsector⟩ :=
    two_circle_cut_sector_chart hR hS hξc hξd hext hint
  have hopen : IsOpen (U ∩ W ∩ Kᶜ) := (hpair.1.1.inter hW).inter hK.isOpen_compl
  have hnew := DiskUnionBoundarySectors.restrict_biholomorphicPair hpair hopen
    (show U ∩ W ∩ Kᶜ ⊆ U from fun z hz => hz.1.1)
  refine ⟨θ, hθ, hθπ, U ∩ W ∩ Kᶜ, V ∩ g ⁻¹' (U ∩ W ∩ Kᶜ),
    f, g, ⟨⟨hξU, hξW⟩, hξK⟩, hnew, hf0, hdf, ?_⟩
  intro z hz
  have heq : z ∈ D \ (closedBall d S ∪ K) ↔ z ∈ ball c R \ closedBall d S := by
    simp only [Set.mem_sdiff, mem_union, hlocal z hz.1.2]
    exact ⟨fun h => ⟨h.1, fun hc => h.2 (Or.inl hc)⟩,
      fun h => ⟨h.1, fun hc => hc.elim h.2 hz.2⟩⟩
  exact heq.trans (hsector z hz.1.1)


/-- The two removed model short rays have unit directions 1 and exp(iθ).
This bound works uniformly for either, and even for every shorter direction. -/
lemma chart_shortRay_length_le {g : ℂ → ℂ} {L : ℝ≥0} {R ε : ℝ} {ξ : ℂ}
    (hg : ContDiffOn ℝ 1 g (ball (0 : ℂ) R))
    (hgLip : LipschitzOnWith L g (closedBall (0 : ℂ) R))
    (hε : 0 < ε) (hεR : ε < R) (hξ : ‖ξ‖ ≤ 1) :
    (∫ t in (0 : ℝ)..1, ‖deriv (g ∘ (fun s : ℝ => (ε * s) • ξ)) t‖) ≤
      (L : ℝ) * ε := by
  let γ := fun t : ℝ => (ε * t) • ξ
  have hγ : ContDiff ℝ 1 γ := by
    change ContDiff ℝ 1 (fun t : ℝ => (ε * t) • ξ)
    exact (contDiff_const.mul contDiff_id).smul contDiff_const
  have hn : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≤ ε := by
    intro t ht
    change ‖(ε * t) • ξ‖ ≤ ε
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hε.le ht.1)]
    calc
      _ ≤ (ε * t) * 1 := mul_le_mul_of_nonneg_left hξ (mul_nonneg hε.le ht.1)
      _ ≤ ε := by nlinarith [ht.2]
  have hmap : MapsTo γ (Icc (0 : ℝ) 1) (ball (0 : ℂ) R) := by
    intro t ht
    rw [mem_ball, dist_zero_right]
    exact (hn t ht).trans_lt hεR
  have hd (t : ℝ) : deriv γ t = ε • ξ := by
    simpa only [γ, id_eq, mul_one] using
      (((hasDerivAt_id t).const_mul ε).smul_const ξ).deriv
  have hlen : (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ≤ ε := by
    calc
      _ = ε * ‖ξ‖ := by simp [hd, Real.norm_eq_abs, abs_of_pos hε]
      _ ≤ ε := mul_le_of_le_one_right hε.le hξ
  calc
    _ ≤ (L : ℝ) * ∫ t in (0 : ℝ)..1, ‖deriv γ t‖ := by
      apply parametrized_length_comp_le isOpen_ball hg hγ (by norm_num) hmap
      intro t ht
      exact norm_fderiv_le_of_lipschitzOn ℝ
        (closedBall_mem_nhds_of_mem (hmap ht)) hgLip
    _ ≤ (L : ℝ) * ε := mul_le_mul_of_nonneg_left hlen L.coe_nonneg

lemma chart_shortRay_flux_bound {g : ℂ → ℂ} {L : ℝ≥0} {R ε M : ℝ} {ξ : ℂ}
    {K U : Set ℂ} {u v : ℂ → ℝ} {ν : ℝ → ℂ}
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) (hv : ContDiffOn ℝ 1 v U)
    (hg : ContDiffOn ℝ 1 g (ball (0 : ℂ) R))
    (hgLip : LipschitzOnWith L g (closedBall (0 : ℂ) R))
    (hgK : MapsTo g (closedBall (0 : ℂ) R) K)
    (hε : 0 < ε) (hεR : ε < R) (hξ : ‖ξ‖ ≤ 1) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ K, ∀ n : ℂ, ‖n‖ ≤ 1 → |normalFlux u v z n| ≤ M)
    (hνc : ContinuousOn ν (Icc (0 : ℝ) 1))
    (hν : ∀ t ∈ Icc (0 : ℝ) 1, ‖ν t‖ ≤ 1) :
    |∫ t in (0 : ℝ)..1,
      normalFlux u v ((g ∘ (fun s : ℝ => (ε * s) • ξ)) t) (ν t) *
        ‖deriv (g ∘ (fun s : ℝ => (ε * s) • ξ)) t‖| ≤
      M * (L : ℝ) * ε := by
  let γ := fun t : ℝ => (ε * t) • ξ
  let J := γ ⁻¹' ball (0 : ℂ) R
  have hc : ContDiff ℝ 1 γ := by
    change ContDiff ℝ 1 (fun t : ℝ => (ε * t) • ξ)
    exact (contDiff_const.mul contDiff_id).smul contDiff_const
  have hJ : IsOpen J := isOpen_ball.preimage hc.continuous
  have hmap : MapsTo γ (Icc (0 : ℝ) 1) (ball (0 : ℂ) R) := by
    intro t ht
    rw [mem_ball, dist_zero_right]
    change ‖(ε * t) • ξ‖ < R
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hε.le ht.1)]
    calc
      _ ≤ (ε * t) * 1 := mul_le_mul_of_nonneg_left hξ (mul_nonneg hε.le ht.1)
      _ < R := by nlinarith [ht.2]
  have hγ : ContDiffOn ℝ 1 (g ∘ γ) J :=
    hg.comp hc.contDiffOn (fun _ ht => ht)
  have hγK : MapsTo (g ∘ γ) (Icc (0 : ℝ) 1) K :=
    fun t ht => hgK (ball_subset_closedBall (hmap ht))
  obtain ⟨hf, hs⟩ := flux_integral_integrable_C1On hU hJ hu hv
    (by norm_num : (0 : ℝ) ≤ 1) hγ hmap (fun t ht => hKU (hγK ht)) hνc
  calc
    _ ≤ M * ∫ t in (0 : ℝ)..1, ‖deriv (g ∘ γ) t‖ :=
      flux_integral_bound_by_length (by norm_num) hbound hγK hν hf hs
    _ ≤ M * ((L : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left (chart_shortRay_length_le hg hgLip hε hεR hξ) hM
    _ = _ := by ring

lemma chart_shortRay_flux_tendsto_zero {g : ℂ → ℂ} {L : ℝ≥0} {R : ℝ} {ξ : ℂ}
    {K U : Set ℂ} {u v : ℂ → ℝ} {ν : ℝ → ℝ → ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hv : ContDiffOn ℝ 1 v U)
    (hg : ContDiffOn ℝ 1 g (ball (0 : ℂ) R))
    (hgLip : LipschitzOnWith L g (closedBall (0 : ℂ) R))
    (hgK : MapsTo g (closedBall (0 : ℂ) R) K) (hR : 0 < R) (hξ : ‖ξ‖ ≤ 1)
    (hνc : ∀ ε : ℝ, 0 < ε → ε < R → ContinuousOn (ν ε) (Icc (0 : ℝ) 1))
    (hν : ∀ ε : ℝ, 0 < ε → ε < R → ∀ t ∈ Icc (0 : ℝ) 1, ‖ν ε t‖ ≤ 1) :
    Tendsto (fun ε : ℝ => ∫ t in (0 : ℝ)..1,
      normalFlux u v ((g ∘ (fun s : ℝ => (ε * s) • ξ)) t) (ν ε t) *
        ‖deriv (g ∘ (fun s : ℝ => (ε * s) • ξ)) t‖) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hM, hbound⟩ := compact_normalFlux_bound hK hKU hU hu hv
  have hlim : Tendsto (fun ε : ℝ => (M * (L : ℝ)) * ε) (𝓝[>] 0) (𝓝 0) := by
    have H : Tendsto (fun ε : ℝ => (M * (L : ℝ)) * ε) (𝓝 0)
        (𝓝 ((M * (L : ℝ)) * 0)) := tendsto_const_nhds.mul tendsto_id
    simpa only [mul_zero] using H.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hlim
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hs : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp, hs] with ε hε hεR
  simpa only [Real.norm_eq_abs] using
    chart_shortRay_flux_bound hU hKU hu hv hg hgLip hgK hε hεR hξ hM.le
      hbound (hνc ε hε hεR) (hν ε hε hεR)


open CircularCutGeometry CircularCornerRounding


/-- A single radius function combines the two pole radii and all corner radii. -/
def poleCornerRadii (a b : ℂ) (ra rb : ℝ) (ρ : ℂ → ℝ) : ℂ → ℝ :=
  fun c => if c = a then ra else if c = b then rb else ρ c

lemma poleCornerRadii_apply_left (a b : ℂ) (ra rb : ℝ) (ρ : ℂ → ℝ) :
    poleCornerRadii a b ra rb ρ a = ra := by simp [poleCornerRadii]

lemma poleCornerRadii_apply_right {a b : ℂ} (hab : a ≠ b)
    (ra rb : ℝ) (ρ : ℂ → ℝ) :
    poleCornerRadii a b ra rb ρ b = rb := by simp [poleCornerRadii, hab.symm]

lemma poleCornerRadii_apply_corner {a b c : ℂ} (hca : c ≠ a) (hcb : c ≠ b)
    (ra rb : ℝ) (ρ : ℂ → ℝ) :
    poleCornerRadii a b ra rb ρ c = ρ c := by simp [poleCornerRadii,hca,hcb]

lemma corner_ne_poles {D : Set ℂ} {corners : Finset ℂ} (hD : IsOpen D)
    (hcorn : (↑corners : Set ℂ) ⊆ frontier D) {a b : ℂ} (ha : a ∈ D) (hb : b ∈ D) :
    ∀ c ∈ corners, c ≠ a ∧ c ≠ b := by
  intro c hc
  have hcfront : c ∈ frontier D := hcorn hc
  rw [hD.frontier_eq] at hcfront
  have hnot : c ∉ D := hcfront.2
  exact ⟨fun h => hnot (h.symm ▸ ha), fun h => hnot (h.symm ▸ hb)⟩

lemma cutDomain_eq_circularCut {D : Set ℂ} {corners : Finset ℂ} {a b : ℂ}
    (hab : a ≠ b) (hcorn : ∀ c ∈ corners, c ≠ a ∧ c ≠ b)
    (ra rb : ℝ) (ρ : ℂ → ℝ) :
    cutDomain D a b ra rb corners ρ =
      circularCut D ({a,b} ∪ corners) (poleCornerRadii a b ra rb ρ) := by
  ext z
  simp only [cutDomain,circularCut, Set.mem_sdiff, mem_union, mem_iUnion,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hz,hcut⟩
    refine ⟨hz,?_⟩
    rintro ⟨c,hc,hzc⟩
    rcases hc with (rfl | rfl) | hc
    · exact hcut (Or.inl (Or.inl (by simpa [poleCornerRadii] using hzc)))
    · exact hcut (Or.inl (Or.inr (by simpa [poleCornerRadii,hab.symm] using hzc)))
    · exact hcut (Or.inr ⟨c,hc,by simpa [poleCornerRadii,(hcorn c hc).1,(hcorn c hc).2] using hzc⟩)
  · rintro ⟨hz,hcut⟩
    refine ⟨hz,?_⟩
    rintro ((hza | hzb) | ⟨c,hc,hzc⟩)
    · exact hcut ⟨a,Or.inl (Or.inl rfl),by simpa [poleCornerRadii] using hza⟩
    · exact hcut ⟨b,Or.inl (Or.inr rfl),by simpa [poleCornerRadii,hab.symm] using hzb⟩
    · exact hcut ⟨c,Or.inr hc,by simpa [poleCornerRadii,(hcorn c hc).1,(hcorn c hc).2] using hzc⟩

/-- A sum over the combined deletion centers is the stated pair of pole terms
plus the sum over the original corner set. -/
lemma sum_poleCornerRadii {D : Set ℂ} {corners : Finset ℂ} (hD : IsOpen D)
    (hcorn : (↑corners : Set ℂ) ⊆ frontier D) {a b : ℂ}
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (ra rb : ℝ) (ρ : ℂ → ℝ) (F : ℂ → ℝ → ℝ) :
    (∑ c ∈ ({a,b} : Finset ℂ) ∪ corners, F c (poleCornerRadii a b ra rb ρ c)) =
      F a ra + F b rb + ∑ c ∈ corners, F c (ρ c) := by
  classical
  have hne := corner_ne_poles hD hcorn ha hb
  have hd : Disjoint ({a,b} : Finset ℂ) corners := by
    apply Finset.disjoint_left.mpr
    intro c hc hc'
    simp only [Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with hca | hcb
    · exact (hne c hc').1 hca
    · exact (hne c hc').2 hcb
  rw [Finset.sum_union hd]
  rw [Finset.sum_pair hab]
  simp only [poleCornerRadii_apply_left,poleCornerRadii_apply_right hab]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  rw [poleCornerRadii_apply_corner (hne c hc).1 (hne c hc).2]

/-- Every sufficiently small pole and corner deletion has the exact rounding
geometry and labeled circular boundary supplied by the accepted cut theorem. -/
lemma fixed_cut_circular_display (s : Finset ℂ) (r : ℂ → ℝ)
    (hG : GeneralPosition s r) (corners : Finset ℂ)
    (hcorn : CornerSet (diskUnion s r) corners)
    (a b : ℂ) (ha : a ∈ diskUnion s r) (hb : b ∈ diskUnion s r) (hab : a ≠ b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ra rb : ℝ) (ρ : ℂ → ℝ),
      0 < ra → ra < δ → 0 < rb → rb < δ →
      (∀ c ∈ corners, 0 < ρ c ∧ ρ c < δ) →
      ∃ J : Finset ℂ,
        RoundingGeometry (cutDomain (diskUnion s r) a b ra rb corners ρ) J ∧
        SignedCircularDisplay (diskUnion s r)
          (cutDomain (diskUnion s r) a b ra rb corners ρ) s r
          ({a,b} ∪ corners) (poleCornerRadii a b ra rb ρ) := by
  classical
  have hcorn_ne := corner_ne_poles (diskUnion_open s r) hcorn.1 ha hb
  obtain ⟨δ,hδ,hcut⟩ := cut_circular_geometry s r hG corners {a,b}
    hcorn.1 hcorn.2.1 hcorn.2.2 (by
      intro c hc
      simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> assumption)
  refine ⟨δ,hδ,?_⟩
  intro ra rb ρ hra hraδ hrb hrbδ hρ
  have hq : ∀ c ∈ ({a,b} : Finset ℂ) ∪ corners,
      0 < poleCornerRadii a b ra rb ρ c ∧ poleCornerRadii a b ra rb ρ c < δ := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · simpa only [poleCornerRadii_apply_left] using And.intro hra hraδ
      · simpa only [poleCornerRadii_apply_right hab] using And.intro hrb hrbδ
    · simpa only [poleCornerRadii_apply_corner (hcorn_ne c hc).1 (hcorn_ne c hc).2]
        using hρ c hc
  obtain ⟨_,_,J,hJ,hdisplay⟩ := hcut (poleCornerRadii a b ra rb ρ) hq
  rw [← cutDomain_eq_circularCut hab hcorn_ne ra rb ρ] at hJ hdisplay
  exact ⟨J,hJ,hdisplay⟩


lemma exp_mul_I_periodic : Function.Periodic
    (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) (2 * Real.pi) := by
  intro t
  simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, add_mul]
    using (Complex.exp_periodic ((t : ℂ) * Complex.I))

lemma circle_flux_density_periodic (u v : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    Function.Periodic (fun t =>
      normalFlux u v (arcParam c r t) (inwardCircleNormal t) * r) (2 * Real.pi) := by
  intro t
  simp only [arcParam, inwardCircleNormal, exp_mul_I_periodic t]

lemma circle_flux_density_integrable (u v : ℂ → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (c : ℂ) (r a b : ℝ) :
    IntervalIntegrable (fun t =>
      normalFlux u v (arcParam c r t) (inwardCircleNormal t) * r) volume a b := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by simp)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by simp)
  have hgu : Continuous (gradient u) := by
    exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp (hu2.continuous_fderiv (by norm_num))
  have hgv : Continuous (gradient v) := by
    exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp (hv2.continuous_fderiv (by norm_num))
  have hγ : Continuous (arcParam c r) := by unfold arcParam; fun_prop
  have hν : Continuous inwardCircleNormal := by unfold inwardCircleNormal; fun_prop
  exact ((((hu.continuous.comp hγ).mul ((hgv.comp hγ).inner hν)).sub
    ((hv.continuous.comp hγ).mul ((hgu.comp hγ).inner hν))).mul_const r).intervalIntegrable a b

/-- The actual signed circular display and Green rounding theorem imply that
all deleting-circle fluxes sum to zero; retained original arcs vanish. -/
lemma signedCircularDisplay_green
    {D K : Set ℂ} {s centers : Finset ℂ} {r q : ℂ → ℝ} {J : Finset ℂ}
    (hgeom : CircularCornerRounding.RoundingGeometry K J)
    (hdisp : CircularCutGeometry.SignedCircularDisplay D K s r centers q)
    {u v : ℂ → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (huH : HarmonicOn K u) (hvH : HarmonicOn K v)
    (hzero : ∀ z ∈ frontier D ∩ closure K, ∀ ν : ℂ, normalFlux u v z ν = 0) :
    (∑ c ∈ centers, circleFlux D u v c (q c)) = 0 := by
  classical
  obtain ⟨n, center, radius, start, stop, sign, label,
    hrange, hlabel, hcover, hdisj, hinj, hside, hang⟩ := hdisp
  have hsign : ∀ i, sign i = 1 ∨ sign i = -1 := by
    intro i
    cases hl : label i with
    | inl c =>
        have hli := hlabel i
        rw [hl] at hli
        exact Or.inl hli.2.2.1
    | inr c =>
        have hli := hlabel i
        rw [hl] at hli
        exact Or.inr hli.2.2.1
  obtain ⟨hint, hgreen⟩ := PiecewiseCircularGreen.piecewise_circular_green
    K J hgeom n center radius start stop sign
    (fun i => ⟨(hrange i).1, (hrange i).2.2.1, by linarith [(hrange i).2.1, (hrange i).2.2.2]⟩)
    hsign hcover hdisj hinj hside Set.univ isOpen_univ (subset_univ _)
    u v (hu.of_le (by simp)).contDiffOn (hv.of_le (by simp)).contDiffOn
    huH.2.2 hvH.2.2
  let F : Fin n → ℝ → ℝ := fun i t =>
    normalFlux u v (arcParam (center i) (radius i) t)
      (sign i • Complex.exp ((t : ℂ) * Complex.I)) * radius i
  change (∑ i, ∫ t in start i..stop i, F i t) = 0 at hgreen
  have horiginal : ∀ i, ∀ c : ↥s, label i = Sum.inl c →
      (∫ t in start i..stop i, F i t) = 0 := by
    intro i c hl
    have hli := hlabel i
    simp only [hl] at hli
    calc
      _ = ∫ t in start i..stop i, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htcc : t ∈ Icc (start i) (stop i) := by
          simpa only [uIcc_of_le (hrange i).2.2.1.le] using ht
        have hzD : arcParam (center i) (radius i) t ∈ frontier D :=
          hli.2.2.2 (mem_image_of_mem _ htcc)
        have hzK : arcParam (center i) (radius i) t ∈ closure K := by
          apply frontier_subset_closure
          rw [hcover]
          exact mem_iUnion.mpr ⟨i, mem_image_of_mem _ htcc⟩
        simp only [F, hzero _ ⟨hzD, hzK⟩ _, zero_mul]
      _ = 0 := by simp
  have hdelete : ∀ c : ↥centers,
      (∑ i ∈ Finset.univ.filter (fun i => label i = Sum.inr c),
        ∫ t in start i..stop i, F i t) = circleFlux D u v c (q c) := by
    intro c
    obtain ⟨_, E, hE, hinside, hpair, hadd⟩ := hang c
    let f : ℝ → ℝ := fun t =>
      normalFlux u v (arcParam c (q c) t) (inwardCircleNormal t) * q c
    have hFi : ∀ i, label i = Sum.inr c → F i = f := by
      intro i hl
      have hli := hlabel i
      simp only [hl] at hli
      funext t
      simp [F, f, hli.1, hli.2.1, hli.2.2.1, inwardCircleNormal]
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i => label i = Sum.inr c),
          ∫ t in start i..stop i, f t := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hFi i (Finset.mem_filter.mp hi).2]
      _ = ∫ t in (0 : ℝ)..(2 * Real.pi),
          ({t : ℝ | arcParam c (q c) t ∈ D}).indicator f t :=
        hadd f (circle_flux_density_periodic u v c (q c))
          (circle_flux_density_integrable u v hu hv c (q c) _ _)
          (fun i _ => circle_flux_density_integrable u v hu hv c (q c) _ _)
      _ = circleFlux D u v c (q c) := by
        rfl
  have hgroup : (∑ c : ↥centers,
      ∑ i ∈ Finset.univ.filter (fun i => label i = Sum.inr c),
        ∫ t in start i..stop i, F i t) =
      ∑ i, ∫ t in start i..stop i, F i t := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    cases hl : label i with
    | inl c => simp [horiginal i c hl]
    | inr c => simp
  have hsubtype : (∑ c : ↥centers, circleFlux D u v c (q c)) = 0 := by
    simp_rw [← hdelete]
    exact hgroup.trans hgreen
  rw [← Finset.sum_attach centers (fun c => circleFlux D u v c (q c))]
  exact hsubtype


/-- The literal fixed-cut Green identity, with the outward normal pointing into
all deleted disks. Smooth reflection supplies the near-closure hypotheses;
the piecewise circular theorem takes the rounding limit before any corner cut
is allowed to shrink. -/
theorem truncated_green_identity :
    Specs.D12Complex.Ch14.TruncatedGreenIdentity.truncated_green_identity_type := by
  intro Ω s r hex j D corners hcorn a b u v ha hb hab hu hv
  have hD : IsOpen D := diskUnion_open _ _
  obtain ⟨δ₁, hδ₁, hpre⟩ := fixed_cut_preconditions Ω s r hex j corners hcorn
    a b u v ha hb hab hu hv
  obtain ⟨δ₂, hδ₂, hdisplay⟩ := fixed_cut_circular_display (s j) (r j)
    (hex.1 j).1 corners hcorn a b ha hb hab
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro ra rb ρ hra hraδ hrb hrbδ hρ
  obtain ⟨hDa, hDb, hdisj, hcp, hcc, huH, hvH, hIa, hIb, hIc⟩ :=
    hpre ra rb ρ hra (hraδ.trans_le (min_le_left _ _))
      hrb (hrbδ.trans_le (min_le_left _ _))
      (fun c hc => ⟨(hρ c hc).1, (hρ c hc).2.trans_le (min_le_left _ _)⟩)
  obtain ⟨J, hgeom, hdisp⟩ := hdisplay ra rb ρ
    hra (hraδ.trans_le (min_le_right _ _))
    hrb (hrbδ.trans_le (min_le_right _ _))
    (fun c hc => ⟨(hρ c hc).1, (hρ c hc).2.trans_le (min_le_right _ _)⟩)
  obtain ⟨u₀, v₀, hu₀, hv₀, heu, hev, hu₀H, hv₀H, hfa, hfb, hfc, hzero⟩ :=
    smooth_cut_flux_transfer D corners hD hcorn a b u v hu hv ra rb ρ hra hrb
      (fun c hc => (hρ c hc).1) hdisj hcp hcc
  have hsum := signedCircularDisplay_green hgeom hdisp hu₀ hv₀ hu₀H hv₀H hzero
  rw [sum_poleCornerRadii hD hcorn.1 ha hb hab ra rb ρ (circleFlux D u₀ v₀),
    hfa, hfb] at hsum
  have hec : (∑ c ∈ corners, circleFlux D u₀ v₀ c (ρ c)) =
      ∑ c ∈ corners, circleFlux D u v c (ρ c) := Finset.sum_congr rfl hfc
  rw [hec] at hsum
  exact ⟨hDa, hDb, hdisj, hcp, hcc, huH, hvH, hIa, hIb, hIc, hsum⟩

end D12Complex.TruncatedGreenIdentity
