import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.DividedDifferenceRegularity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyDerivatives
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex.DividedDifferenceRegularity

abbrev q : Specs.D12Complex.Ch04.DividedDifferenceRegularity.dividedDifference_type :=
  dividedDifference
abbrev qZ : Specs.D12Complex.Ch04.DividedDifferenceRegularity.partialZ_type := partialZ

lemma dividedDifference_eq_dslope (f : ℂ → ℂ) (z w : ℂ) :
    dividedDifference f z w = dslope f w z := by
  classical
  by_cases h : z = w
  · subst z
    simp [dividedDifference]
  · rw [dividedDifference, ite_eq_right h, dslope_of_ne f h]
    simp only [slope_def_field]
    rw [← neg_sub (f z) (f w), ← neg_sub z w, neg_div_neg_eq]

theorem holomorphicOn_slice :
    Specs.D12Complex.Ch04.DividedDifferenceRegularity.holomorphicOn_slice_type := by
  intro U f hf w hw
  refine ⟨hf.1, ?_⟩
  have hd : DifferentiableOn ℂ (dslope f w) U :=
    (Complex.differentiableOn_dslope (hf.1.mem_nhds hw)).mpr
      (fun z hz => (hf.2 z hz).differentiableWithinAt)
  intro z hz
  simpa only [dividedDifference_eq_dslope] using hd.differentiableAt (hf.1.mem_nhds hz)

theorem hasDerivAt_slice :
    Specs.D12Complex.Ch04.DividedDifferenceRegularity.hasDerivAt_slice_type := by
  intro U f hf z hz w hw
  exact ((holomorphicOn_slice U f hf w hw).2 z hz).hasDerivAt

private lemma boundary_kernel_continuous (a z : ℂ) (r : ℝ) (f : ℂ → ℂ)
    (hz : z ∈ ball a r) (hc : ContinuousOn f (sphere a r)) :
    ContinuousOn (fun ζ => f ζ / (ζ - z)) (sphere a r) := by
  exact hc.div (continuousOn_id.sub continuousOn_const)
    (fun ζ hζ => sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hζ hz))

theorem common_circle_formula :
    Specs.D12Complex.Ch04.DividedDifferenceRegularity.common_circle_formula_type := by
  intro U f hf a r hr hU z hz w hw
  have hc : ContinuousOn f (sphere a r) := fun ζ hζ =>
    (hf.2 ζ (hU (sphere_subset_closedBall hζ))).continuousAt.continuousWithinAt
  have hcz := boundary_kernel_continuous a z r f hz hc
  have hcw := boundary_kernel_continuous a w r f hw hc
  have hdenz : ∀ ζ ∈ sphere a r, ζ-z ≠ 0 :=
    fun ζ hζ => sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hζ hz)
  have hdenw : ∀ ζ ∈ sphere a r, ζ-w ≠ 0 :=
    fun ζ hζ => sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hζ hw)
  have hck : ContinuousOn (fun ζ => f ζ / ((ζ-z)*(ζ-w))) (sphere a r) :=
    hc.div ((continuousOn_id.sub continuousOn_const).mul
      (continuousOn_id.sub continuousOn_const))
      (fun ζ hζ => mul_ne_zero (hdenz ζ hζ) (hdenw ζ hζ))
  rw [DiskCauchyFormula.integral_eq_circleIntegral a r _ hr.le hck]
  by_cases h : z = w
  · subst w
    simp only [dividedDifference, ite_true]
    have hd := DiskCauchyDerivatives.disk_cauchy_derivatives a z r U f hr hf hU
      (mem_ball_iff_norm.mp hz) 1
    simp only [Nat.reduceAdd] at hd
    have hc2 : ContinuousOn (fun ζ => f ζ / (ζ-z)^2) (sphere a r) :=
      hc.div ((continuousOn_id.sub continuousOn_const).pow 2)
        (fun ζ hζ => pow_ne_zero _ (hdenz ζ hζ))
    rw [DiskCauchyFormula.integral_eq_circleIntegral a r (fun ζ => f ζ / (ζ-z)^2)
      hr.le hc2] at hd
    simpa [iteratedDeriv_one, pow_two] using hd
  · have hzformula := DiskCauchyFormula.disk_cauchy_formula a z r U f hr hf hU
      (mem_ball_iff_norm.mp hz)
    have hwformula := DiskCauchyFormula.disk_cauchy_formula a w r U f hr hf hU
      (mem_ball_iff_norm.mp hw)
    rw [DiskCauchyFormula.integral_eq_circleIntegral a r _ hr.le hcz] at hzformula
    rw [DiskCauchyFormula.integral_eq_circleIntegral a r _ hr.le hcw] at hwformula
    have heq : circleIntegral (fun ζ => f ζ / ((ζ-z)*(ζ-w))) a r =
        (circleIntegral (fun ζ => f ζ / (ζ-w)) a r -
          circleIntegral (fun ζ => f ζ / (ζ-z)) a r) / (w-z) := by
      rw [← circleIntegral.integral_sub (hcw.circleIntegrable hr.le)
        (hcz.circleIntegrable hr.le)]
      simp only [div_eq_mul_inv]
      have hm : (circleIntegral (fun ζ => f ζ * (ζ-w)⁻¹ - f ζ * (ζ-z)⁻¹) a r) *
          (w-z)⁻¹ = circleIntegral
            (fun ζ => (f ζ * (ζ-w)⁻¹ - f ζ * (ζ-z)⁻¹) * (w-z)⁻¹) a r := by
        simpa only [smul_eq_mul] using
          (circleIntegral.integral_smul_const
            (fun ζ => f ζ * (ζ-w)⁻¹ - f ζ * (ζ-z)⁻¹) (w-z)⁻¹ a r).symm
      rw [hm]
      apply circleIntegral.integral_congr hr.le
      intro ζ hζ
      field_simp [hdenz ζ hζ, hdenw ζ hζ, sub_ne_zero.mpr (Ne.symm h)]
      ; ring
    rw [dividedDifference, ite_eq_right h, heq, hwformula, hzformula]
    ring


/-- Continuity of a parameterized circle integral from joint continuity on
an open parameter set times its fixed compact circle. -/
private lemma continuousOn_circleIntegral (V : Set (ℂ × ℂ)) (hV : IsOpen V)
    (g : (ℂ × ℂ) → ℂ → ℂ) (a : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hg : ContinuousOn (fun x : (ℂ × ℂ) × ℂ => g x.1 x.2)
      (V ×ˢ sphere a r)) :
    ContinuousOn (fun p => circleIntegral (g p) a r) V := by
  let : CompactSpace (sphere a r) := isCompact_iff_compactSpace.mp (isCompact_sphere a r)
  intro p hp
  have hgs : ContinuousOn (fun x : (ℂ × ℂ) × sphere a r => g x.1 x.2)
      (V ×ˢ univ) := by
    apply hg.comp (show ContinuousOn
      (fun x : (ℂ × ℂ) × sphere a r => (x.1, (x.2 : ℂ))) _ from by fun_prop)
    intro x hx
    exact ⟨hx.1, x.2.property⟩
  have hu : TendstoUniformlyOn g (g p) (𝓝 p) (sphere a r) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    exact hgs.tendstoUniformly (hV.mem_nhds hp)
  apply ContinuousAt.continuousWithinAt
  apply hu.tendsto_circleIntegral_of_continuousOn hr
  filter_upwards [hV.mem_nhds hp] with x hx
  exact hg.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun ζ hζ => ⟨hx, hζ⟩)

private lemma common_circle_formula' (U : Set ℂ) (f : ℂ → ℂ) (hf : HolomorphicOn U f)
    (a : ℂ) (r : ℝ) (hr : 0 < r) (hU : closedBall a r ⊆ U)
    (z w : ℂ) (hz : z ∈ ball a r) (hw : w ∈ ball a r) :
    dividedDifference f z w = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      circleIntegral (fun ζ => f ζ / ((ζ-z)*(ζ-w))) a r := by
  rw [common_circle_formula U f hf a r hr hU z hz w hw]
  congr 1
  apply DiskCauchyFormula.integral_eq_circleIntegral a r _ hr.le
  have hc : ContinuousOn f (sphere a r) := fun ζ hζ =>
    (hf.2 ζ (hU (sphere_subset_closedBall hζ))).continuousAt.continuousWithinAt
  refine hc.div
    ((continuousOn_id.sub continuousOn_const).mul (continuousOn_id.sub continuousOn_const)) ?_
  intro ζ hζ
  exact mul_ne_zero
    (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hζ hz))
    (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hζ hw))

private lemma continuousOn_local_kernel (U : Set ℂ) (f : ℂ → ℂ) (hf : HolomorphicOn U f)
    (a : ℂ) (r : ℝ) (hr : 0 < r) (hU : closedBall a r ⊆ U) :
    ContinuousOn (fun p : ℂ × ℂ => dividedDifference f p.1 p.2)
      (ball a r ×ˢ ball a r) := by
  have hg : ContinuousOn
      (fun x : (ℂ × ℂ) × ℂ => f x.2 / ((x.2-x.1.1)*(x.2-x.1.2)))
      ((ball a r ×ˢ ball a r) ×ˢ sphere a r) := by
    apply ((show ContinuousOn f (sphere a r) from fun ζ hζ =>
      (hf.2 ζ (hU (sphere_subset_closedBall hζ))).continuousAt.continuousWithinAt).comp
        continuous_snd.continuousOn (fun x hx => hx.2)).div (by fun_prop)
    intro x hx
    exact mul_ne_zero
      (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hx.2 hx.1.1))
      (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hx.2 hx.1.2))
  have hc := (continuousOn_circleIntegral (ball a r ×ˢ ball a r) (isOpen_ball.prod isOpen_ball)
    (fun p ζ => f ζ / ((ζ-p.1)*(ζ-p.2))) a r hr.le hg).const_mul
    (2 * Real.pi * Complex.I : ℂ)⁻¹
  exact hc.congr (fun p hp => common_circle_formula' U f hf a r hr hU p.1 p.2 hp.1 hp.2)

theorem local_common_circle :
    Specs.D12Complex.Ch04.DividedDifferenceRegularity.local_common_circle_type := by
  intro U f hf a ha
  obtain ⟨r, hr, hU⟩ := Metric.mem_nhds_iff.mp (hf.1.mem_nhds ha)
  refine ⟨r/2, half_pos hr, ?_, ?_⟩
  · exact (closedBall_subset_ball (by linarith)).trans hU
  · exact common_circle_formula U f hf a (r/2) (half_pos hr)
      ((closedBall_subset_ball (by linarith)).trans hU)

theorem continuousOn_dividedDifference :
    Specs.D12Complex.Ch04.DividedDifferenceRegularity.continuousOn_dividedDifference_type := by
  intro U f hf p hp
  apply ContinuousAt.continuousWithinAt
  by_cases h : p.1 = p.2
  · obtain ⟨r, hr, hU, _⟩ := local_common_circle U f hf p.1 hp.1
    have hpball : p ∈ ball p.1 r ×ˢ ball p.1 r := by simp [← h, hr]
    exact (continuousOn_local_kernel U f hf p.1 r hr hU).continuousAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hpball)
  · have hc : ContinuousAt (fun x : ℂ × ℂ => (f x.2 - f x.1) / (x.2-x.1)) p :=
      (((hf.2 p.2 hp.2).continuousAt.comp continuousAt_snd).sub
        ((hf.2 p.1 hp.1).continuousAt.comp continuousAt_fst)).div
        (continuousAt_snd.sub continuousAt_fst) (sub_ne_zero.mpr (Ne.symm h))
    apply hc.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne_fun continuous_fst continuous_snd).mem_nhds h] with x hx
    simp only [dividedDifference, ite_eq_right hx]

private lemma partialZ_circle_formula (U : Set ℂ) (f : ℂ → ℂ) (hf : HolomorphicOn U f)
    (a : ℂ) (r : ℝ) (hr : 0 < r) (hU : closedBall a r ⊆ U)
    (z w : ℂ) (hz : z ∈ ball a r) (hw : w ∈ U) :
    partialZ f z w = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      circleIntegral (fun ζ => dividedDifference f ζ w / (ζ-z)^2) a r := by
  have hd := DiskCauchyDerivatives.disk_cauchy_derivatives a z r U
    (fun ζ => dividedDifference f ζ w) hr (holomorphicOn_slice U f hf w hw) hU
    (mem_ball_iff_norm.mp hz) 1
  simp only [Nat.reduceAdd] at hd
  have hqs : ContinuousOn (fun ζ => dividedDifference f ζ w) (sphere a r) :=
    fun ζ hζ => ((holomorphicOn_slice U f hf w hw).2 ζ
      (hU (sphere_subset_closedBall hζ))).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun ζ => dividedDifference f ζ w / (ζ-z)^2) (sphere a r) :=
    hqs.div ((continuousOn_id.sub continuousOn_const).pow 2)
      (fun ζ hζ => pow_ne_zero _
        (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hζ hz)))
  rw [DiskCauchyFormula.integral_eq_circleIntegral a r
    (fun ζ => dividedDifference f ζ w / (ζ-z)^2) hr.le hc] at hd
  simpa only [partialZ, iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_div] using hd

theorem continuousOn_partialZ :
    Specs.D12Complex.Ch04.DividedDifferenceRegularity.continuousOn_partialZ_type := by
  intro U f hf p hp
  obtain ⟨r, hr, hU, _⟩ := local_common_circle U f hf p.1 hp.1
  have hq := continuousOn_dividedDifference U f hf
  have hg : ContinuousOn
      (fun x : (ℂ × ℂ) × ℂ => dividedDifference f x.2 x.1.2 / (x.2-x.1.1)^2)
      ((ball p.1 r ×ˢ U) ×ˢ sphere p.1 r) := by
    have hcomp : ContinuousOn (fun x : (ℂ × ℂ) × ℂ => dividedDifference f x.2 x.1.2)
        ((ball p.1 r ×ˢ U) ×ˢ sphere p.1 r) :=
      hq.comp (show ContinuousOn (fun x : (ℂ × ℂ) × ℂ => (x.2, x.1.2))
        ((ball p.1 r ×ˢ U) ×ˢ sphere p.1 r) from by fun_prop)
        (fun x hx => ⟨hU (sphere_subset_closedBall hx.2), hx.1.2⟩)
    exact hcomp.div (by fun_prop) (fun x hx => pow_ne_zero _
      (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hx.2 hx.1.1)))
  have hc := (continuousOn_circleIntegral (ball p.1 r ×ˢ U) (isOpen_ball.prod hf.1)
    (fun x ζ => dividedDifference f ζ x.2 / (ζ-x.1)^2) p.1 r hr.le hg).const_mul
      (2 * Real.pi * Complex.I : ℂ)⁻¹
  have hpc : ContinuousOn (fun x : ℂ × ℂ => partialZ f x.1 x.2) (ball p.1 r ×ˢ U) :=
    hc.congr (fun x hx => partialZ_circle_formula U f hf p.1 r hr hU x.1 x.2 hx.1 hx.2)
  exact (hpc.continuousAt ((isOpen_ball.prod hf.1).mem_nhds
    ⟨mem_ball_self hr, hp.2⟩)).continuousWithinAt

/-- Compactness of the jointly continuous derivative gives a common mean-value
remainder bound for all parameters and all nearby base points. -/
theorem uniform_differenceQuotients :
    Specs.D12Complex.Ch04.DividedDifferenceRegularity.uniform_differenceQuotients_type := by
  intro U f hf z₀ hz₀ K hK hKU
  obtain ⟨R, hR, hRU, _⟩ := local_common_circle U f hf z₀ hz₀
  have hhalf : closedBall z₀ (R/2) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hRU
  have hquarter : closedBall z₀ (R/4) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hRU
  refine ⟨R/4, by positivity, hquarter, ?_⟩
  have huc : UniformContinuousOn (fun p : ℂ × ℂ => partialZ f p.1 p.2)
      (closedBall z₀ (R/2) ×ˢ K) :=
    ((isCompact_closedBall z₀ (R/2)).prod hK).uniformContinuousOn_of_continuous
      ((continuousOn_partialZ U f hf).mono (prod_mono hhalf hKU))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp huc (ε/2) (half_pos hε)
  have hev : ∀ᶠ h : ℂ in 𝓝[≠] 0, ‖h‖ < min δ (R/4) := by
    apply mem_nhdsWithin_of_mem_nhds
    filter_upwards [ball_mem_nhds (0 : ℂ) (show 0 < min δ (R/4) from lt_min hδ (by positivity))]
      with h hh
    exact mem_ball_zero_iff.mp hh
  filter_upwards [hev, self_mem_nhdsWithin] with h hh hne
  have hh0 : h ≠ 0 := hne
  intro p hp
  rcases p with ⟨z, w⟩
  have hz : z ∈ closedBall z₀ (R/4) := hp.1
  have hw : w ∈ K := hp.2
  have hwh : w ∈ U := hKU hw
  have hnorm : ‖h‖ < R/4 := lt_of_lt_of_le hh (min_le_right _ _)
  have hsmall : ‖h‖ < δ := lt_of_lt_of_le hh (min_le_left _ _)
  have hlocal : closedBall z ‖h‖ ⊆ closedBall z₀ (R/2) := by
    apply closedBall_subset_closedBall'
    have hzdist := mem_closedBall.mp hz
    linarith
  have hzbig : z ∈ closedBall z₀ (R/2) :=
    closedBall_subset_closedBall (by linarith) hz
  have hbound : ∀ t ∈ closedBall z ‖h‖,
      ‖partialZ f t w - partialZ f z w‖ ≤ ε/2 := by
    intro t ht
    have hd : dist (t,w) (z,w) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg : 0 ≤ dist t z)] using
        (mem_closedBall.mp ht).trans_lt hsmall
    simpa only [dist_eq_norm] using (hu (t,w) ⟨hlocal ht, hw⟩ (z,w) ⟨hzbig, hw⟩ hd).le
  have hder : ∀ t ∈ closedBall z ‖h‖,
      HasDerivWithinAt
        (fun t => dividedDifference f t w - t * partialZ f z w)
        (partialZ f t w - partialZ f z w) (closedBall z ‖h‖) t := by
    intro t ht
    convert ((hasDerivAt_slice U f hf t (hhalf (hlocal ht)) w hwh).sub
      ((hasDerivAt_id t).mul_const (partialZ f z w))).hasDerivWithinAt using 1 <;> first | rfl | simp
  have hm := (convex_closedBall z ‖h‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (mem_closedBall_self (norm_nonneg h))
    (show z+h ∈ closedBall z ‖h‖ from by simp [mem_closedBall, dist_eq_norm])
  rw [dist_comm, dist_eq_norm]
  have heq : (dividedDifference f (z+h) w - dividedDifference f z w) / h - partialZ f z w =
      ((dividedDifference f (z+h) w - (z+h)*partialZ f z w) -
        (dividedDifference f z w - z*partialZ f z w)) / h := by
    field_simp
    ; ring
  rw [heq, norm_div]
  calc
    _ ≤ ε/2 := (div_le_iff₀ (norm_pos_iff.mpr hh0)).mpr (by simpa only [add_sub_cancel_left] using hm)
    _ < ε := half_lt_self hε

end D12Complex.DividedDifferenceRegularity
