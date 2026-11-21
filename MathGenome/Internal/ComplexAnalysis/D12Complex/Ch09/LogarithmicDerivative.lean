import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch09.LogarithmicDerivative
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.LocalQuotientsArithmetic
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.Residue

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.LogarithmicDerivative

def coefficient (F : ℂ → RiemannSphere) : ℂ → ℂ := logDeriv (scalarFinitePart F)
def filled (F : ℂ → RiemannSphere) : ℂ → RiemannSphere :=
  LocalQuotientsArithmetic.fill (coefficient F)

/-- Differentiate the integer-power factorization on a punctured neighborhood.
This includes negative orders without differentiating the filler at the pole. -/
theorem expansion_germ {f : ℂ → ℂ} {a : ℂ} {m : ℤ}
    (hf : MeromorphicAt f a) (hm : meromorphicOrderAt f a = (m : WithTop ℤ)) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
      logDeriv f =ᶠ[𝓝[≠] a] (fun z => (m : ℂ) / (z - a) + h z) := by
  obtain ⟨u, hu, hu0, heq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hm
  refine ⟨logDeriv u, hu.deriv.div hu hu0, ?_⟩
  have he := logDeriv_congr_nhdsNE heq
  filter_upwards [he, hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hu.continuousAt.eventually_ne hu0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hzu hzu0 hza
  have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
  rw [hz]
  change logDeriv (fun w => (w - a) ^ m * u w) z = _
  rw [logDeriv_fun_mul (f := fun w => (w - a) ^ m) (g := u) z
    (zpow_ne_zero m hza') hzu0
    ((differentiableAt_id.sub_const a).zpow (Or.inl hza')) hzu.differentiableAt,
    logDeriv_fun_zpow (f := fun w : ℂ => w - a) (x := z) (by fun_prop) m]
  simp [logDeriv_apply, div_eq_mul_inv]

theorem local_expansion :
    Specs.D12Complex.Ch09.LogarithmicDerivative.local_expansion_type := by
  intro Ω F hF a ha m hm
  obtain ⟨h, hh, he⟩ := expansion_germ
    (LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF a ha) hm
  have he' : ∀ᶠ z in 𝓝 a, z ≠ a → coefficient F z = (m : ℂ) / (z - a) + h z :=
    eventually_nhdsWithin_iff.mp he
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    ((show ∀ᶠ z in 𝓝 a, z ∈ Ω from hF.1.mem_nhds ha).and
      (hh.eventually_analyticAt.and he'))
  refine ⟨r, hr, fun z hz => (hball (Metric.mem_ball.mp hz)).1, h,
    ⟨Metric.isOpen_ball, fun z hz => (hball (Metric.mem_ball.mp hz)).2.1.differentiableAt⟩,
    fun z hz => ?_⟩
  exact (hball (by simpa only [dist_eq_norm] using hz.2)).2.2
    (sub_ne_zero.mp (norm_pos_iff.mp hz.1))

theorem filled_meromorphic :
    Specs.D12Complex.Ch09.LogarithmicDerivative.filled_meromorphic_type := by
  intro Ω F hF
  exact LocalQuotientsArithmetic.scalarMeromorphicOn_fill Ω hF.1 _
    ((show MeromorphicOn (scalarFinitePart F) Ω from
      LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF).logDeriv)


/-- Compute the project's residue directly from a local simple principal part.
The values of the representative at the center play no role. -/
theorem residue_of_expansion {f h : ℂ → ℂ} {a c : ℂ} {r : ℝ}
    (hr : 0 < r) (hh : HolomorphicOn (Metric.ball a r) h)
    (he : ∀ z ∈ puncturedDisk a r, f z = c / (z - a) + h z) :
    Residue.residue f a = c := by
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hr)] with ρ hρ hρr
  change 0 < ρ at hρ
  change ρ < r at hρr
  have hsub : Metric.closedBall a ρ ⊆ Metric.ball a r :=
    Metric.closedBall_subset_ball hρr
  have hcont : ContinuousOn h (Metric.closedBall a ρ) :=
    fun z hz => (hh.2 z (hsub hz)).continuousAt.continuousWithinAt
  have hi : circleIntegral h a ρ = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le
      countable_empty hcont (fun z hz => hh.2 z
        (hsub (Metric.ball_subset_closedBall hz.1)))
  have hne : ∀ z ∈ Metric.sphere a ρ, z - a ≠ 0 := by
    intro z hz
    have hd : dist z a = ρ := Metric.mem_sphere.mp hz
    exact sub_ne_zero.mpr (fun h => by simp [h] at hd; linarith)
  have hc : ContinuousOn (fun z : ℂ => c / (z - a)) (Metric.sphere a ρ) :=
    continuousOn_const.div (continuousOn_id.sub continuousOn_const) hne
  have heq : circleIntegral f a ρ =
      circleIntegral (fun z => c / (z - a) + h z) a ρ := by
    apply circleIntegral.integral_congr hρ.le
    intro z hz
    apply he z
    have hz' : ‖z - a‖ = ρ := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz
    exact ⟨by rw [hz']; exact hρ, by rw [hz']; exact hρr⟩
  rw [heq, circleIntegral.integral_add (hc.circleIntegrable hρ.le)
    ((hcont.mono Metric.sphere_subset_closedBall).circleIntegrable hρ.le), hi, add_zero]
  simp only [div_eq_mul_inv]
  rw [circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball_self hρ)]
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  field_simp

theorem residue_eq_order :
    Specs.D12Complex.Ch09.LogarithmicDerivative.residue_eq_order_type := by
  intro Ω F hF a ha m hm
  obtain ⟨r, hr, _, h, hh, he⟩ := local_expansion Ω F hF a ha m hm
  have hres := residue_of_expansion hr hh he
  exact ⟨hres, (Residue.differentialResidue_differential _ _).trans hres⟩

/-- A finite signed order gives either a genuine simple pole, or a removable
germ when that order is zero. -/
theorem local_pole_classification :
    Specs.D12Complex.Ch09.LogarithmicDerivative.local_pole_classification_type := by
  intro Ω F hF a ha m hm
  have hf := LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF a ha
  have hld : MeromorphicAt (coefficient F) a := hf.logDeriv
  change meromorphicOrderAt (scalarFinitePart F) a = (m : WithTop ℤ) at hm
  have hp (hn : m ≠ 0) : meromorphicOrderAt (coefficient F) a = -1 := by
    exact meromorphicOrderAt_logDeriv_eq_neg_one hf (by simpa [hm] using hn)
      (by simp [hm])
  have hz (hm0 : m = 0) : 0 ≤ meromorphicOrderAt (coefficient F) a := by
    exact meromorphicOrderAt_logDeriv_nonneg hf (by simpa [hm0] using hm)
  refine ⟨?_, fun hn => LocalQuotientsArithmetic.poleOfOrder_of_order hld 1 (by norm_num)
    (hp hn), ?_⟩
  · change LocalQuotientsArithmetic.fill (coefficient F) a = sphereInfty ↔ m ≠ 0
    rw [LocalQuotientsArithmetic.fill_eq_infty_iff]
    constructor
    · intro h hn
      exact (not_lt.mpr (hz hn)) h
    · intro hn
      rw [hp hn]
      exact WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0)
  · intro hm0
    obtain ⟨r, hr, _, h, hh, he⟩ := local_expansion Ω F hF a ha m hm
    have he' : ∀ z ∈ puncturedDisk a r, coefficient F z = h z := by
      simpa [hm0, coefficient, Specs.D12Complex.Ch09.LogarithmicDerivative.Objects.coefficient] using he
    have hopen : IsOpen (puncturedDisk a r) := by
      have hset : puncturedDisk a r = Metric.ball a r \ {a} := by
        ext z
        simp [puncturedDisk, Metric.mem_ball, dist_eq_norm, norm_pos_iff, sub_ne_zero]
        tauto
      rw [hset]
      exact Metric.isOpen_ball.sdiff isClosed_singleton
    have hhol : HolomorphicOn (puncturedDisk a r) (coefficient F) := by
      refine ⟨hopen, fun z hz => ?_⟩
      have hg := hh.2 z (by simpa [Metric.mem_ball, dist_eq_norm] using hz.2)
      exact hg.congr_of_eventuallyEq
        (Filter.eventually_of_mem (hopen.mem_nhds hz) (fun w hw => he' w hw))
    exact ⟨⟨r, hr, hhol⟩, r, hr, h, hh, he'⟩


/-- Nonvanishing on the particular connected component rules out the zero germ.
No condition is imposed on the other components. -/
theorem finite_order_on_component {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F) {a : ℂ} (ha : a ∈ Ω)
    (hn : ¬ EqOn F (fun _ => sphereFinite 0) (connectedComponentIn Ω a)) :
    ∃ m : ℤ, scalarSignedOrder F a = some m := by
  have hnot : meromorphicOrderAt (scalarFinitePart F) a ≠ ⊤ := by
    intro ho
    apply hn
    intro b hb
    have hC : MeromorphicOn (scalarFinitePart F) (connectedComponentIn Ω a) :=
      (show MeromorphicOn (scalarFinitePart F) Ω from
        LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF).mono_set
          (connectedComponentIn_subset Ω a)
    have hob := hC.meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_connectedComponentIn (mem_connectedComponentIn ha) hb ho
    exact (LocalQuotientsArithmetic.scalar_eq_fill Ω F hF
      (connectedComponentIn_subset Ω a hb)).trans
        (LocalQuotientsArithmetic.fill_of_order_top hob)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hnot
  exact ⟨m, hm.symm⟩

/-- Order zero is exactly a finite nonzero scalar value. -/
theorem order_zero_iff_regular {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F) {a : ℂ} (ha : a ∈ Ω) :
    scalarSignedOrder F a = some 0 ↔ F a ≠ sphereFinite 0 ∧ F a ≠ sphereInfty := by
  constructor
  · intro ho
    change meromorphicOrderAt (scalarFinitePart F) a = 0 at ho
    have hf := LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF a ha
    have hne := hf.meromorphicOrderAt_eq_zero_iff_toMeromorphicNFAt_ne_zero.mp ho
    have hval : F a = sphereFinite (toMeromorphicNFAt (scalarFinitePart F) a a) := by
      rw [LocalQuotientsArithmetic.scalar_eq_fill Ω F hF ha,
        Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects.fill, ho]
      simp
    rw [hval]
    exact ⟨fun h => hne (sphereFinite_injective h), OnePoint.coe_ne_infty _⟩
  · rintro ⟨hz, hi⟩
    obtain hinf | ⟨c, hc⟩ := sphere_eq_infty_or_finite (F a)
    · exact (hi hinf).elim
    · exact scalarSignedOrder_regular Ω F hF a ha c hc
        (fun hc0 => hz (hc.trans (congrArg sphereFinite hc0)))

theorem filled_poles :
    Specs.D12Complex.Ch09.LogarithmicDerivative.filled_poles_type := by
  intro Ω F hF a ha hn
  obtain ⟨m, hm⟩ := finite_order_on_component hF ha hn
  obtain ⟨hiff, _, _⟩ := local_pole_classification Ω F hF a ha m hm
  have hm0 : m = 0 ↔ F a ≠ sphereFinite 0 ∧ F a ≠ sphereInfty := by
    rw [← order_zero_iff_regular hF ha, hm]
    exact Option.some_inj.symm
  refine ⟨?_, ?_⟩
  · rw [hiff, ne_eq, hm0]
    tauto
  · intro hp
    have hf := LocalQuotientsArithmetic.scalar_meromorphicAt Ω F hF a ha
    have horder : meromorphicOrderAt (coefficient F) a = -1 :=
      meromorphicOrderAt_logDeriv_eq_neg_one hf
        (by change meromorphicOrderAt (scalarFinitePart F) a ≠ 0
            rw [show meromorphicOrderAt (scalarFinitePart F) a = (m : WithTop ℤ) from hm]
            simpa using hiff.mp hp)
        (by change meromorphicOrderAt (scalarFinitePart F) a ≠ ⊤
            rw [show meromorphicOrderAt (scalarFinitePart F) a = (m : WithTop ℤ) from hm]
            simp)
    have hmero := LocalQuotientsArithmetic.scalar_meromorphicAt Ω _
      (filled_meromorphic Ω F hF) a ha
    have hgerm : scalarFinitePart (filled F) =ᶠ[𝓝[≠] a] coefficient F :=
      LocalQuotientsArithmetic.finitePart_fill_germ hf.logDeriv
    apply LocalQuotientsArithmetic.poleOfOrder_of_order hmero 1 (by norm_num)
    exact (meromorphicOrderAt_congr hgerm).trans horder

end D12Complex.LogarithmicDerivative
