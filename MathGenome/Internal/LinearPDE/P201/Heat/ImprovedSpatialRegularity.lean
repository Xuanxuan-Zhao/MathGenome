import MathGenome.Internal.LinearPDE.P201Specs.Heat.ImprovedSpatialRegularity
import MathGenome.Internal.LinearPDE.P201.Heat.ImprovedEnergy
import MathGenome.Internal.LinearPDE.P201.Elliptic.GlobalH2
import MathGenome.Internal.LinearPDE.P201.Elliptic.DirichletResolvent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
universe u v
namespace P201.Heat.ImprovedSpatialRegularity
open ExpandedFA.Evolution HilbertTripleSpec HilbertTripleTraceSpec
open MildEnergyAgreement ImprovedEnergy
open P201Specs

/-- The complete abstract assertion is reused without spatial restrictions. -/
theorem improved_energy : ImprovedEnergyTheorem.{u,v} := ImprovedEnergy.improved_energy

lemma energy_iff_weak {m : ℕ} (Ω : Domain (m + 1))
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (d : CoerciveForm (H10 ℝ Ω) (Lp ℝ Ω 2)) (hd : IsDirichletForm Ω A d)
    (hA : ContinuousOn A Ω) (M : ℝ) (hM : ∀ x ∈ Ω, ‖A x‖ ≤ M)
    (u : H10 ℝ Ω) (f : Lp ℝ Ω 2) :
    (∀ w, d.a u w = inner ℝ (d.j w) f) ↔ InteriorH2.WeakEquation Ω A u.val f := by
  constructor
  · intro hu φ
    let w := P201.DirichletResolvent.testClass Ω φ
    have hw : hZeroUnderlying Ω w = P102.U4.testToDomainLp Ω 2 φ :=
      P201.DirichletResolvent.testClass_underlying Ω φ
    have hg := P201.InteriorTesting.smooth_gradient_ae Ω w.val φ hw
    calc
      _ = d.a u w := by
        rw [hd.2]
        apply integral_congr_ae
        filter_upwards [hg] with x hx
        rw [hx]
      _ = inner ℝ (d.j w) f := hu w
      _ = _ := by
        rw [hd.1, hw, real_inner_comm, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [P102.U4.testToDomainLp_ae Ω 2 φ] with x hx
        simp [RCLike.inner_apply, hx, mul_comm]
  · intro hu w
    rw [hd.2, hd.1, L2.inner_def]
    simpa only [RCLike.inner_apply, conj_trivial] using
      P201.InteriorH2.weakEquation_energy (by omega) Ω A u.val f hA hM hu w

theorem canonical_graph : CanonicalGraphStatement := by
  intro m Ω A d hd hA M hM x f
  rw [d.mem_graph]
  constructor
  · rintro ⟨u, hu, hf⟩
    exact ⟨u, hd.1 ▸ hu, (energy_iff_weak Ω A d hd hA M hM u f).mp hf⟩
  · rintro ⟨u, hu, hf⟩
    exact ⟨u, hd.1.symm ▸ hu, (energy_iff_weak Ω A d hd hA M hM u f).mpr hf⟩

/-- The shifted resolvent, followed by elliptic regularity, is bounded
into H². This proves measurability by a continuous linear map; it requires
no separability or measurable choice of pointwise elliptic lifts. -/
theorem shifted_h2_map {m : ℕ} (Ω : Domain (m + 1))
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (d : CoerciveForm (H10 ℝ Ω) (Lp ℝ Ω 2)) (hd : IsDirichletForm Ω A d)
    (hA : ContinuousOn A Ω) (M : ℝ) (hM : ∀ x ∈ Ω, ‖A x‖ ≤ M)
    (C : ℝ) (hC : 0 < C)
    (hell : ∀ (u : H10 ℝ Ω) (f : Lp ℝ Ω 2), InteriorH2.WeakEquation Ω A u.val f →
      ∃ w : H ℝ Ω 2, hUnderlying Ω 2 w = hZeroUnderlying Ω u ∧
        ‖w‖ ≤ C * (‖f‖ + ‖u‖)) :
    ∃ R : Lp ℝ Ω 2 →L[ℝ] H ℝ Ω 2,
      ∀ x h : Lp ℝ Ω 2, (x, h) ∈ d.operator.graph → hUnderlying Ω 2 (R (h + x)) = x := by
  obtain ⟨_, _, _, K, hK, hgraph, _⟩ := d.representation
  have hg (f : Lp ℝ Ω 2) : (d.j (K f), f - d.j (K f)) ∈ d.operator.graph :=
    (hgraph _ _).mpr rfl
  have heq (f : Lp ℝ Ω 2) : InteriorH2.WeakEquation Ω A (K f).val (f - d.j (K f) : Lp ℝ Ω 2) :=
    (energy_iff_weak Ω A d hd hA M hM _ _).mp ((d.mem_graph_at _ _).mp (hg f))
  choose W hW hb using fun f => hell (K f) (f - d.j (K f)) (heq f)
  have hW' (f) : hUnderlying Ω 2 (W f) = d.j (K f) := by rw [hd.1]; exact hW f
  let R₀ : Lp ℝ Ω 2 →ₗ[ℝ] H ℝ Ω 2 :=
    { toFun := W
      map_add' := by
        intro f g
        apply P201.hilbertUnderlyingInjective Ω 2
        simp only [map_add, hW']
      map_smul' := by
        intro c f
        apply P201.hilbertUnderlyingInjective Ω 2
        simp only [map_smul, hW', RingHom.id_apply] }
  have hb' (f : Lp ℝ Ω 2) :
      ‖R₀ f‖ ≤ (C * (1 + ‖d.j‖ * ‖K‖ + ‖K‖)) * ‖f‖ := by
    calc
      ‖R₀ f‖ ≤ C * (‖f - d.j (K f)‖ + ‖K f‖) := hb f
      _ ≤ C * ((‖f‖ + ‖d.j‖ * (‖K‖ * ‖f‖)) + ‖K‖ * ‖f‖) := by
        have hj := (d.j.le_opNorm (K f)).trans
          (mul_le_mul_of_nonneg_left (K.le_opNorm f) (norm_nonneg d.j))
        exact mul_le_mul_of_nonneg_left
          (add_le_add ((norm_sub_le _ _).trans (add_le_add_right hj _)) (K.le_opNorm f)) hC.le
      _ = _ := by ring
  refine ⟨R₀.mkContinuous _ hb', ?_⟩
  intro x h hx
  change hUnderlying Ω 2 (W (h + x)) = x
  rw [hW']
  apply (hgraph x (h + x)).mp
  simpa only [add_sub_cancel_right] using hx

/-- Integrate a sum estimate with precisely the same elliptic constant. -/
lemma lp_norm_sum_bound {E F G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (w : MeasureTheory.Lp E 2 μ) (f : MeasureTheory.Lp F 2 μ) (g : MeasureTheory.Lp G 2 μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ t ∂μ, ‖w t‖ ≤ C * (‖f t‖ + ‖g t‖)) :
    ‖w‖ ≤ C * (‖f‖ + ‖g‖) := by
  let F₀ : MeasureTheory.Lp ℝ 2 μ := (Lp.memLp f).norm.toLp (fun t => ‖f t‖)
  let G₀ : MeasureTheory.Lp ℝ 2 μ := (Lp.memLp g).norm.toLp (fun t => ‖g t‖)
  have hF : (F₀ : X → ℝ) =ᵐ[μ] fun t => ‖f t‖ := MemLp.coeFn_toLp _
  have hG : (G₀ : X → ℝ) =ᵐ[μ] fun t => ‖g t‖ := MemLp.coeFn_toLp _
  have hFn : ‖F₀‖ ≤ ‖f‖ := Lp.norm_le_norm_of_ae_le (hF.mono (by intro t ht; simp [ht]))
  have hGn : ‖G₀‖ ≤ ‖g‖ := Lp.norm_le_norm_of_ae_le (hG.mono (by intro t ht; simp [ht]))
  calc
    ‖w‖ ≤ C * ‖F₀ + G₀‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [hb, hF, hG, Lp.coeFn_add F₀ G₀] with t ht hf hg ha
      simpa only [ha, Pi.add_apply, hf, hg, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using ht
    _ ≤ C * (‖f‖ + ‖g‖) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hFn hGn)) hC

/-- A strongly measurable, square-integrable H² lift of a time-dependent
canonical graph, with the unchanged integrated elliptic estimate. -/
theorem time_h2_lift {m : ℕ} (Ω : Domain (m + 1))
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (d : CoerciveForm (H10 ℝ Ω) (Lp ℝ Ω 2)) (hd : IsDirichletForm Ω A d)
    (hA : ContinuousOn A Ω) (M : ℝ) (hM : ∀ x ∈ Ω, ‖A x‖ ≤ M)
    (C : ℝ) (hC : 0 < C)
    (hell : ∀ (u : H10 ℝ Ω) (f : Lp ℝ Ω 2), InteriorH2.WeakEquation Ω A u.val f →
      ∃ w : H ℝ Ω 2, hUnderlying Ω 2 w = hZeroUnderlying Ω u ∧
        ‖w‖ ≤ C * (‖f‖ + ‖u‖))
    (T : ℝ) (u : timeLpValue (H10 ℝ Ω) 2 T) (g : timeLpValue (Lp ℝ Ω 2) 2 T)
    (hg : ∀ᵐ t ∂timeMeasureValue T, (d.j (u t), g t) ∈ d.operator.graph) :
    ∃ w : timeLpValue (H ℝ Ω 2) 2 T,
      (∀ᵐ t ∂timeMeasureValue T, hUnderlying Ω 2 (w t) = d.j (u t)) ∧
      (∀ᵐ t ∂timeMeasureValue T, ‖w t‖ ≤ C * (‖g t‖ + ‖u t‖)) ∧
      ‖w‖ ≤ C * (‖g‖ + ‖u‖) := by
  obtain ⟨R, hR⟩ := shifted_h2_map Ω A d hd hA M hM C hC hell
  let q := g + d.j.compLp u
  let w := R.compLp q
  have hw : ∀ᵐ t ∂timeMeasureValue T, hUnderlying Ω 2 (w t) = d.j (u t) := by
    filter_upwards [R.coeFn_compLp q, Lp.coeFn_add g (d.j.compLp u),
      d.j.coeFn_compLp u, hg] with t ht hq hj hg
    change hUnderlying Ω 2 (w t) = _
    rw [ht, hq, Pi.add_apply, hj]
    exact hR _ _ hg
  have hb : ∀ᵐ t ∂timeMeasureValue T, ‖w t‖ ≤ C * (‖g t‖ + ‖u t‖) := by
    filter_upwards [hw, hg] with t ht hg
    have heq := (energy_iff_weak Ω A d hd hA M hM (u t) (g t)).mp
      ((d.mem_graph_at _ _).mp hg)
    obtain ⟨v, hv, hb⟩ := hell (u t) (g t) heq
    have hvw : v = w t := P201.hilbertUnderlyingInjective Ω 2 (hv.trans ((hd.1 ▸ ht).symm))
    rwa [hvw] at hb
  exact ⟨w, hw, hb, lp_norm_sum_bound w g u C hC.le hb⟩

/-- Coercivity controls the full V norm by the operator value on its graph. -/
lemma graph_norm_control {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (d : CoerciveForm V H) (α : ℝ) (hα : 0 < α)
    (hco : ∀ v, α * ‖v‖ ^ 2 ≤ d.a v v)
    (v : V) (h : H) (hv : (d.j v, h) ∈ d.operator.graph) :
    ‖v‖ ≤ (‖d.j‖ / α) * ‖h‖ := by
  have ha := (d.mem_graph_at _ _).mp hv v
  have hb : α * ‖v‖ ^ 2 ≤ ‖d.j‖ * ‖v‖ * ‖h‖ :=
    (hco v).trans (ha ▸ (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (d.j.le_opNorm v) (norm_nonneg h)))
  by_cases hz : ‖v‖ = 0
  · rw [hz]; positivity
  · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hb' : α * ‖v‖ ≤ ‖d.j‖ * ‖h‖ := by nlinarith
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hα).mpr
    simpa only [div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using hb'


/-- Full spatial conclusion for the canonical Dirichlet operator, including
strong H² measurability, the integrated elliptic estimate, and a data bound
uniform in the length of the time interval. -/
theorem spatial_regularity : SpatialTheorem := by
  intro m Ω hb hc M L theta htheta
  obtain ⟨C, hC, hell⟩ := P201.GlobalH2.globalEstimate Ω hb hc M L theta htheta
  refine ⟨C, hC, ?_⟩
  intro A hA hsym d hd
  obtain ⟨α, hα, hco⟩ := d.coercive
  obtain ⟨Cdata, hCdata, henergy⟩ := improved_energy ‖d.a‖ α (ContinuousLinearMap.opNorm_nonneg d.a) hα
  let K : ℝ := ‖d.j‖ / α
  have hK : 0 ≤ K := div_nonneg (norm_nonneg _) hα.le
  refine ⟨Cdata, (C * (1 + K)) ^ 2 * Cdata, hCdata, by positivity, ?_⟩
  intro T hT u₀ f z
  obtain ⟨r, hr⟩ := henergy d le_rfl hco T hT u₀ f z
  have hg : ∀ᵐ t ∂timeMeasureValue T,
      (d.j (z.value t), r.operatorValue t) ∈ d.operator.graph := by
    filter_upwards [z.represents, r.graph] with t ht hg
    rwa [ht] at hg
  obtain ⟨w, hw, hpoint, hnorm⟩ := time_h2_lift Ω A d hd hA.2.1.continuousOn
    M hA.1 C hC (hell A hA hsym) T z.value r.operatorValue hg
  have hwcurve : ∀ᵐ t ∂timeMeasureValue T,
      hUnderlying Ω 2 (w t) = extendCurve z.curve t := by
    filter_upwards [hw, z.represents] with t ht he
    exact ht.trans he.symm
  have hz : ‖z.value‖ ≤ K * ‖r.operatorValue‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hg] with t ht
    exact graph_norm_control d α hα hco (z.value t) (r.operatorValue t) ht
  have hwb : ‖w‖ ≤ (C * (1 + K)) * ‖r.operatorValue‖ := by
    calc
      ‖w‖ ≤ C * (‖r.operatorValue‖ + ‖z.value‖) := hnorm
      _ ≤ C * (‖r.operatorValue‖ + K * ‖r.operatorValue‖) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hz _) hC.le
      _ = _ := by ring
  have hs : 0 ≤ supremumSquare r.lift := by
    let t₀ : Icc 0 T := ⟨0, by simp [hT.le]⟩
    exact (sq_nonneg ‖r.lift t₀‖).trans (le_csSup r.lift_bounded ⟨t₀, rfl⟩)
  have hop : ‖r.operatorValue‖ ^ 2 ≤ Cdata * (‖u₀‖ ^ 2 + ‖f‖ ^ 2) := by
    linarith [sq_nonneg ‖r.velocity‖]
  refine ⟨⟨r, w, hr, (Lp.memLp w).aestronglyMeasurable, hwcurve, hpoint, hnorm⟩,
    w, hwcurve, ?_⟩
  calc
    ‖w‖ ^ 2 ≤ ((C * (1 + K)) * ‖r.operatorValue‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hwb 2
    _ = (C * (1 + K)) ^ 2 * ‖r.operatorValue‖ ^ 2 := mul_pow _ _ _
    _ ≤ (C * (1 + K)) ^ 2 * (Cdata * (‖u₀‖ ^ 2 + ‖f‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hop (sq_nonneg _)
    _ = _ := by ring

end P201.Heat.ImprovedSpatialRegularity
