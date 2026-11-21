import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.StateDerivative
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolutionMap
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.CommonInterval
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.OpenDomain
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.DerivativeCriterion
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.LinearVolterra

/-! Autonomous initial-state dependence, paper.tex d13:06:c1-dependence.

The variation is first constructed using the continuous linear Volterra theorem
in the space of continuous linear endomorphisms. A compact tube and a convex
mean value estimate give a uniform Taylor remainder. An oriented Gronwall
estimate then identifies the variation as the Fréchet derivative. Uniform
linear dependence supplies joint continuity, and compact enclosures assemble
the result on the actual maximal domain. No derivative of the flow is an input.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace D13Unified.Ch06.StateDerivative
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma flow_ivp (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    {ξ : E} (hξ : ξ ∈ F.domain) :
    classicalIVPOnValue F.toODE (flowInterval F ξ) (fun t => flow F t ξ) 0 ξ := by
  obtain ⟨hx, hs, hi, _⟩ := ODE.canonical_solution F.toODE
    (F.locallyLipschitzInState_of_contDiffOn hF) 0 ξ hξ
  exact ⟨hx, hs, hi⟩

lemma continuousOn_coefficient (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {ξ : E} (hξ : ξ ∈ F.domain)
    {a b : ℝ} (hJ : Icc a b ⊆ (flowInterval F ξ).carrier) :
    ContinuousOn (coefficient F ξ) (Icc a b) := by
  have hx := (flow_ivp F hF hξ).1
  exact (hF.continuousOn_fderiv_of_isOpen F.isOpen_domain le_rfl).comp
    (hx.1.continuousOn.mono hJ) (fun t ht => hx.2.1 t (hJ ht))

/-- Construction in the Banach space of operators; the coefficient acts by
left composition. Its existence uses only continuous coefficients. -/
theorem variational_existence :
    Specs.D13Unified.Ch06.StateDerivative.VariationalExistence.{u} := by
  intro E _ _ _ F hF ξ hξ a b h0 hJ
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hA := continuousOn_coefficient F hF hξ hJ
  let A : ℝ → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    fun t => ContinuousLinearMap.compL ℝ E E E (coefficient F ξ t)
  have hAc : ContinuousOn A (Icc a b) :=
    (ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn hA
  obtain ⟨Y, hY, hu⟩ := LinearVolterra.existence a b 0 A (fun _ => 0)
    (ContinuousLinearMap.id ℝ E) h0 hAc continuousOn_const
  have hd := (LinearVolterra.differential_equivalence a b 0 A (fun _ => 0)
    (ContinuousLinearMap.id ℝ E) Y h0 hAc continuousOn_const).mp hY
  refine ⟨Y, ?_, hd.2.1, ?_, ?_⟩
  · simpa [IsVariation, LinearVolterra.IsIntegralSolution, A,
      ContinuousLinearMap.compL_apply] using hY
  · simpa [A, ContinuousLinearMap.compL_apply] using hd.2.2
  · intro Z hZ
    apply hu Z
    simpa [IsVariation, LinearVolterra.IsIntegralSolution, A,
      ContinuousLinearMap.compL_apply] using hZ

/-- A whole compact interval persists for all sufficiently close states, with
one uniform state error bound and a compact tube inside the original domain. -/
lemma compact_control (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    {ξ : E} (hξ : ξ ∈ F.domain) {a b : ℝ} (h0 : 0 ∈ Icc a b)
    (hJ : Icc a b ⊆ (flowInterval F ξ).carrier) :
    ∃ ρ L : ℝ, 0 < ρ ∧ 0 ≤ L ∧
      IsCompact (closedTube (fun t => flow F t ξ) a b ρ) ∧
      closedTube (fun t => flow F t ξ) a b ρ ⊆ F.toODE.domain ∧
      ∀ η : E, Real.exp (L*(b-a))*‖η-ξ‖ < ρ/2 →
        η ∈ F.domain ∧ Icc a b ⊆ (flowInterval F η).carrier ∧
        ∀ t ∈ Icc a b, ‖flow F t η-flow F t ξ‖ ≤ Real.exp (L*(b-a))*‖η-ξ‖ := by
  have hx := flow_ivp F hF hξ
  have hLip := F.locallyLipschitzInState_of_contDiffOn hF
  obtain ⟨ρ, L, hρ, hL, hK, hdom, hlip⟩ := compact_solution_tube
    F.toODE hLip (flowInterval F ξ) (fun t => flow F t ξ) hx.1 a b
    (h0.1.trans h0.2) hJ
  refine ⟨ρ, L, hρ, hL, hK, hdom, ?_⟩
  intro η hη
  have hsmall : Real.exp (L*(b-a))*(‖η-flow F 0 ξ‖ + 0*(b-a)) < ρ/2 := by
    simpa [hx.2.2] using hη
  have h := Ch05.OpenDomain.persistence F.toODE F.toODE hLip
    (flowInterval F ξ) (fun t => flow F t ξ) hx.1 hρ hL le_rfl hJ h0 hK
    hdom hdom hlip (by intro q hq; simp) hsmall
  change η ∈ F.domain ∧ Icc a b ⊆ (flowInterval F η).carrier ∧
    ∀ t ∈ Icc a b, ‖flow F t η-flow F t ξ‖ ≤
      Real.exp (L*(b-a))*(‖η-flow F 0 ξ‖ + 0*(b-a)) at h
  simpa only [hx.2.2, zero_mul, add_zero] using h

/-- Ambient continuity at every allowed pair, obtained using local persistence.
Off-domain choices for the representative are immaterial. -/
lemma continuousAt_flow (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    {q : ℝ × E} (hq : q ∈ flowDomain F) :
    ContinuousAt (fun r : ℝ × E => flow F r.1 r.2) q := by
  have hx := flow_ivp F hF hq.1
  obtain ⟨a, b, h0, ht, hJ⟩ := Ch05.OpenDomain.compact_enclosure
    (flowInterval F q.2) hx.2.1 hq.2
  obtain ⟨ρ, L, hρ, hL, hK, hdom, hc⟩ := compact_control F hF hq.1
    ⟨h0.1.le, h0.2.le⟩ hJ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hn : ∀ᶠ r : ℝ × E in 𝓝 q,
      Real.exp (L*(b-a))*‖r.2-q.2‖ < min (ρ/2) (ε/2) :=
    ((continuous_const.mul ((continuous_snd.sub continuous_const).norm)).tendsto q)
      (Iio_mem_nhds (by simpa using lt_min (half_pos hρ) (half_pos hε)))
  have htn : ∀ᶠ r : ℝ × E in 𝓝 q, r.1 ∈ Ioo a b :=
    continuous_fst.tendsto q (Ioo_mem_nhds ht.1 ht.2)
  have hxcont : ContinuousAt (fun t => flow F t q.2) q.1 :=
    hx.1.1.continuousOn.continuousAt ((flowInterval F q.2).isOpen.mem_nhds hq.2)
  have hxn : ∀ᶠ r : ℝ × E in 𝓝 q, ‖flow F r.1 q.2-flow F q.1 q.2‖ < ε/2 :=
    (((hxcont.comp continuous_fst.continuousAt).sub continuousAt_const).norm).eventually
      (Iio_mem_nhds (by simpa using half_pos hε))
  filter_upwards [hn, htn, hxn] with r hr hrt hrx
  have he := (hc r.2 (hr.trans_le (min_le_left _ _))).2.2 r.1 ⟨hrt.1.le, hrt.2.le⟩
  rw [dist_eq_norm]
  exact (norm_sub_le_norm_sub_add_norm_sub (flow F r.1 r.2)
    (flow F r.1 q.2) (flow F q.1 q.2)).trans_lt
      (add_lt_add (he.trans_lt (hr.trans_le (min_le_right _ _))) hrx) |>.trans_eq
      (by ring)

lemma continuousOn_flow (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain) :
    ContinuousOn (fun q : ℝ × E => flow F q.1 q.2) (flowDomain F) :=
  fun _ hq => (continuousAt_flow F hF hq).continuousWithinAt

omit [FiniteDimensional ℝ E] in
/-- Uniform first-order Taylor control on the compact reference tube.
The mean value inequality supplies the estimate without a modulus choice. -/
lemma uniform_taylor (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    {ξ : E} {a b ρ : ℝ} (hρ : 0 < ρ)
    (hK : IsCompact (closedTube (fun t => flow F t ξ) a b ρ))
    (hdom : closedTube (fun t => flow F t ξ) a b ρ ⊆ F.toODE.domain)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc a b, ∀ y : E, ‖y-flow F t ξ‖ < δ →
      ‖F.eval y-F.eval (flow F t ξ)-coefficient F ξ t (y-flow F t ξ)‖ ≤
        ε*‖y-flow F t ξ‖ := by
  have hD : ContinuousOn (fun q : ℝ × E => fderiv ℝ F.eval q.2)
      (closedTube (fun t => flow F t ξ) a b ρ) :=
    (hF.continuousOn_fderiv_of_isOpen F.isOpen_domain le_rfl).comp
      continuousOn_snd (fun q hq => hdom hq)
  obtain ⟨d, hd, hdc⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hK.uniformContinuousOn_of_continuous hD) ε hε
  refine ⟨min ρ d, lt_min hρ hd, ?_⟩
  intro t ht y hy
  let B := closedBall (flow F t ξ) (min ρ d)
  have hBK : ∀ z ∈ B, (t,z) ∈ closedTube (fun t => flow F t ξ) a b ρ := by
    intro z hz
    exact ⟨ht, (mem_closedBall_iff_norm.mp hz).trans (min_le_left _ _)⟩
  have hbase : (t,flow F t ξ) ∈ closedTube (fun t => flow F t ξ) a b ρ :=
    ⟨ht, by simp; exact hρ.le⟩
  have hbound : ∀ z ∈ B, ‖fderiv ℝ F.eval z-coefficient F ξ t‖ ≤ ε := by
    intro z hz
    have hdist : dist (t,z) (t,flow F t ξ) ≤ d := by
      simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ dist z (flow F t ξ))] using
        (mem_closedBall.mp hz).trans (min_le_right ρ d)
    simpa only [dist_eq_norm, coefficient, AutonomousODE.eval] using (hdc (t,z) (hBK z hz) (t,flow F t ξ) hbase hdist)
  have hder : ∀ z ∈ B, HasFDerivWithinAt
      (fun w => F.eval w-coefficient F ξ t w)
      (fderiv ℝ F.eval z-coefficient F ξ t) B z := by
    intro z hz
    have hfz := (hF.contDiffAt (F.isOpen_domain.mem_nhds (hdom (hBK z hz)))).differentiableAt_one
    exact (hfz.hasFDerivAt.sub (coefficient F ξ t).hasFDerivAt).hasFDerivWithinAt
  have hm := (convex_closedBall (flow F t ξ) (min ρ d)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hder hbound (mem_closedBall_self (le_of_lt (lt_min hρ hd)))
    (show y ∈ B from mem_closedBall_iff_norm.mpr hy.le)
  convert hm using 1
  simp only [map_sub]
  congr 1
  abel

lemma variation_differential (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {ξ : E} (hξ : ξ ∈ F.domain)
    {a b : ℝ} (h0 : 0 ∈ Icc a b) (hJ : Icc a b ⊆ (flowInterval F ξ).carrier)
    {Y : ℝ → E →L[ℝ] E} (hY : IsVariation F ξ a b Y) :
    Y 0 = ContinuousLinearMap.id ℝ E ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt Y ((coefficient F ξ t).comp (Y t)) (Icc a b) t := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hA := (ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn
    (continuousOn_coefficient F hF hξ hJ)
  have he : LinearVolterra.IsIntegralSolution a b 0
      (fun t => ContinuousLinearMap.compL ℝ E E E (coefficient F ξ t)) (fun _ => 0)
      (ContinuousLinearMap.id ℝ E) Y := by
    simpa [LinearVolterra.IsIntegralSolution, IsVariation, ContinuousLinearMap.compL_apply] using hY
  have hd := (LinearVolterra.differential_equivalence a b 0 _ (fun _ => 0)
    (ContinuousLinearMap.id ℝ E) Y h0 hA continuousOn_const).mp he
  simpa only [LinearVolterra.IsDifferentialSolution, Function.comp_apply, ContinuousLinearMap.compL_apply, add_zero]
    using hd.2

/-- The nonlinear error is bounded by the forcing remainder in a linear
inhomogeneous equation, for either orientation of time. -/
lemma variation_error_bound (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {ξ η : E}
    (hξ : ξ ∈ F.domain) (hη : η ∈ F.domain) {a b : ℝ} (h0 : 0 ∈ Icc a b)
    (hJξ : Icc a b ⊆ (flowInterval F ξ).carrier)
    (hJη : Icc a b ⊆ (flowInterval F η).carrier)
    {Y : ℝ → E →L[ℝ] E} (hY : IsVariation F ξ a b Y)
    {K M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hA : ∀ t ∈ Icc a b, ‖coefficient F ξ t‖ ≤ K)
    (hR : ∀ t ∈ Icc a b,
      ‖F.eval (flow F t η)-F.eval (flow F t ξ)-
        coefficient F ξ t (flow F t η-flow F t ξ)‖ ≤ M) :
    ∀ t ∈ Icc a b,
      ‖flow F t η-flow F t ξ-Y t (η-ξ)‖ ≤
        M * Specs.D13Unified.Ch05.Gronwall.EValue K |t| := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hx := flow_ivp F hF hξ
  have hy := flow_ivp F hF hη
  have hYd := variation_differential F hF hξ h0 hJξ hY
  let e : ℝ → E := fun t => flow F t η-flow F t ξ-Y t (η-ξ)
  let g : ℝ → E := fun t => F.eval (flow F t η)-F.eval (flow F t ξ)-
    coefficient F ξ t (Y t (η-ξ))
  have hxc := hx.1.1.continuousOn.mono hJξ
  have hyc := hy.1.1.continuousOn.mono hJη
  have hec : ContinuousOn e (Icc a b) := (hyc.sub hxc).sub (hY.1.clm_apply continuousOn_const)
  have hfc := hF.continuousOn
  have hgc : ContinuousOn g (Icc a b) :=
    ((hfc.comp hyc (fun t ht => hy.1.2.1 t (hJη ht))).sub
      (hfc.comp hxc (fun t ht => hx.1.2.1 t (hJξ ht)))).sub
      ((continuousOn_coefficient F hF hξ hJξ).clm_apply (hY.1.clm_apply continuousOn_const))
  have hd : ∀ t ∈ Icc a b, HasDerivWithinAt e (g t) (Icc a b) t := by
    intro t ht
    have hdξ := (hx.1.2.2 t (hJξ ht)).hasDerivWithinAt.mono hJξ
    have hdη := (hy.1.2.2 t (hJη ht)).hasDerivWithinAt.mono hJη
    have hdy := (hYd.2 t ht).clm_apply (hasDerivWithinAt_const t (Icc a b) (η-ξ))
    convert (hdη.sub hdξ).sub hdy using 1
    simp [g, ContinuousLinearMap.comp_apply]
  have he0 : e 0 = 0 := by simp [e, hx.2.2, hy.2.2, hYd.1]
  have heq : ∀ t ∈ Icc a b, e t = 0 + ∫ r in (0:ℝ)..t, g r := by
    intro t ht
    rw [integral_eq_sub_on_interval ordConnected_Icc hec hgc hd h0 ht, he0, sub_zero, zero_add]
  have hgb : ∀ t ∈ Icc a b, ‖g t‖ ≤ K*‖e t‖+M := by
    intro t ht
    have hg : g t = coefficient F ξ t (e t) +
        (F.eval (flow F t η)-F.eval (flow F t ξ)-
          coefficient F ξ t (flow F t η-flow F t ξ)) := by
      dsimp [e, g]; simp only [map_sub]; abel
    rw [hg]
    exact (norm_add_le _ _).trans (add_le_add
      (((coefficient F ξ t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA t ht) (norm_nonneg _)))
      (hR t ht))
  have hb := LinearVolterra.norm_bound_of_integral h0 hec hK hM heq hgb
  simpa only [e, norm_zero, zero_mul, zero_add, sub_zero] using hb

/-- Identification of the independently constructed variation with the state
Fréchet derivative, uniformly controlled on every compact time interval. -/
theorem state_derivative : Specs.D13Unified.Ch06.StateDerivative.StateDerivativeExpected.{u} := by
  intro E _ _ _ F hF ξ hξ a b h0 hJ Y hY t ht
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hAc := continuousOn_coefficient F hF hξ hJ
  obtain ⟨K, hKA⟩ := isCompact_Icc.exists_bound_of_continuousOn hAc
  have hK : 0 ≤ K := (norm_nonneg _).trans (hKA 0 h0)
  obtain ⟨ρ, L, hρ, hL, hQ, hdom, hc⟩ := compact_control F hF hξ h0 hJ
  let C := Real.exp (L*(b-a))
  let B := (b-a)*Real.exp (K*(b-a))
  have hC : 0 < C := Real.exp_pos _
  have hB : 0 ≤ B := mul_nonneg (sub_nonneg.mpr (h0.1.trans h0.2)) (Real.exp_pos _).le
  have hE : Specs.D13Unified.Ch05.Gronwall.EValue K |t| ≤ B :=
    LinearVolterra.E_le hK (abs_nonneg _) (by simpa using LinearVolterra.time_length_le h0 ht)
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  let c := ε / (C*(B+1))
  have hcpos : 0 < c := div_pos hε (mul_pos hC (by positivity))
  have hce : c*C*(B+1) = ε := by dsimp [c]; field_simp
  have hcb : c*C*B ≤ ε := by nlinarith [mul_pos hcpos hC]
  obtain ⟨δ, hδ, hTaylor⟩ := uniform_taylor F hF hρ hQ hdom hcpos
  have hn : ∀ᶠ η : E in 𝓝 ξ, C*‖η-ξ‖ < min (ρ/2) δ :=
    ((continuous_const.mul ((continuous_id.sub continuous_const).norm)).tendsto ξ)
      (Iio_mem_nhds (by simpa using lt_min (half_pos hρ) hδ))
  filter_upwards [hn] with η hη
  have hp := hc η (hη.trans_le (min_le_left _ _))
  have hM : 0 ≤ c*C*‖η-ξ‖ := mul_nonneg (mul_pos hcpos hC).le (norm_nonneg _)
  have hrem : ∀ r ∈ Icc a b,
      ‖F.eval (flow F r η)-F.eval (flow F r ξ)-
        coefficient F ξ r (flow F r η-flow F r ξ)‖ ≤ c*C*‖η-ξ‖ := by
    intro r hr
    have hsmall := (hp.2.2 r hr).trans_lt (hη.trans_le (min_le_right _ _))
    exact (hTaylor r hr (flow F r η) hsmall).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hp.2.2 r hr) hcpos.le)
  have he := variation_error_bound F hF hξ hp.1 h0 hJ hp.2.1 hY hK hM hKA hrem t ht
  exact he.trans ((mul_le_mul_of_nonneg_left hE hM).trans (by
    nlinarith [mul_le_mul_of_nonneg_right hcb (norm_nonneg (η-ξ))]))

/-- The compact family of variations is jointly continuous. The proof uses
uniform dependence of linear equations in the operator Banach space. -/
theorem local_joint_variation : Specs.D13Unified.Ch06.StateDerivative.LocalJointVariation.{u} := by
  classical
  intro E _ _ _ F hF ξ hξ a b h0 hJ
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨ρ, L, hρ, hL, hK, hdom, hc⟩ := compact_control F hF hξ h0 hJ
  let V : Set E := {η | Real.exp (L*(b-a))*‖η-ξ‖ < ρ/2}
  have hVo : IsOpen V := isOpen_lt
    (continuous_const.mul (continuous_id.sub continuous_const).norm) continuous_const
  have hVξ : ξ ∈ V := by dsimp [V]; simpa using half_pos hρ
  have hVad (p : V) : p.val ∈ F.domain := (hc p.val p.property).1
  have hVJ (p : V) : Icc a b ⊆ (flowInterval F p.val).carrier := (hc p.val p.property).2.1
  choose Y hY hY0 hYd hu using fun p : V =>
    variational_existence F hF p.val (hVad p) a b h0 (hVJ p)
  let A (p : V) (t : ℝ) : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    ContinuousLinearMap.compL ℝ E E E (coefficient F p.val t)
  have hAc (p : V) : ContinuousOn (A p) (Icc a b) :=
    (ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn
      (continuousOn_coefficient F hF (hVad p) (hVJ p))
  have hsol (p : V) : LinearVolterra.IsIntegralSolution a b 0 (A p) (fun _ => 0)
      (ContinuousLinearMap.id ℝ E) (Y p) := by
    simpa [LinearVolterra.IsIntegralSolution, IsVariation, A, ContinuousLinearMap.compL_apply]
      using hY p
  have hflow : Continuous (fun q : V × Icc a b => flow F q.2 q.1.val) := by
    rw [continuous_iff_continuousAt]
    intro q
    have hp : ContinuousAt (fun r : V × Icc a b => (r.2.val,r.1.val)) q :=
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst)).continuousAt
    have hf := continuousAt_flow F hF (show (q.2.val,q.1.val) ∈ flowDomain F from
      ⟨hVad q.1, hVJ q.1 q.2.property⟩)
    exact ContinuousAt.comp (g := fun r : ℝ × E => flow F r.1 r.2) (f := fun r : V × Icc a b => (r.2.val,r.1.val)) hf hp
  have hcoeff : Continuous (fun q : V × Icc a b => coefficient F q.1.val q.2.val) :=
    (hF.continuousOn_fderiv_of_isOpen F.isOpen_domain le_rfl).comp_continuous hflow
      (fun q => (flow_ivp F hF (hVad q.1)).1.2.1 q.2.val (hVJ q.1 q.2.property))
  let AA (p : V) : C(Icc a b, (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E)) :=
    ⟨fun t => A p t.val, (hAc p).domRestrict⟩
  have hAA : Continuous AA := ContinuousMap.continuous_of_continuous_uncurry AA
    ((ContinuousLinearMap.compL ℝ E E E).continuous.comp hcoeff)
  let YY (p : V) : C(Icc a b, E →L[ℝ] E) := ⟨fun t => Y p t.val, (hY p).1.domRestrict⟩
  have hYY : Continuous YY := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hlimA : TendstoUniformlyOn A (A p) (𝓝 p) (Icc a b) :=
      (ContinuousOn.tendsto_domRestrict_iff_tendstoUniformlyOn (hAc p) hAc).mp
        hAA.continuousAt
    have hlimY := LinearVolterra.tendstoUniformlyOn_solutions h0 hAc
      (fun _ => continuousOn_const) (hAc p) continuousOn_const hsol (hsol p)
      hlimA (tendsto_const_nhds.tendstoUniformlyOn_const (Icc a b)) tendsto_const_nhds
    exact (ContinuousOn.tendsto_domRestrict_iff_tendstoUniformlyOn
      (hY p).1 (fun p => (hY p).1)).mpr hlimY
  have hYjoint : Continuous (fun q : V × Icc a b => Y q.1 q.2.val) :=
    continuous_eval.comp ((hYY.comp continuous_fst).prodMk continuous_snd)
  let Z (η : E) (t : ℝ) : E →L[ℝ] E := if h : η ∈ V then Y ⟨η,h⟩ t else 0
  refine ⟨V, hVo, hVξ, fun η hη => hVad ⟨η,hη⟩,
    fun η hη => hVJ ⟨η,hη⟩, Z, ?_, ?_⟩
  · intro η hη
    simpa only [Z, dite_eq_left hη] using hY ⟨η,hη⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    have hmap : Continuous (fun q : (Icc a b ×ˢ V) =>
        ((⟨q.val.2,q.property.2⟩, ⟨q.val.1,q.property.1⟩) : V × Icc a b)) :=
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_fst.comp continuous_subtype_val).subtype_mk _)
    convert hYjoint.comp hmap using 1
    ext q
    simp [Z, q.property.2]

/-- The canonical derivative represents the compact variational solution.
The independent construction above establishes that it exists before this
identification is made. -/
lemma derivative_isVariation (F : AutonomousODE E) (hF : ContDiffOn ℝ 1 F.eval F.domain)
    {ξ : E} (hξ : ξ ∈ F.domain) {a b : ℝ} (h0 : 0 ∈ Icc a b)
    (hJ : Icc a b ⊆ (flowInterval F ξ).carrier) :
    IsVariation F ξ a b (fun t => fderiv ℝ (fun η => flow F t η) ξ) := by
  obtain ⟨Y, hY, _⟩ := variational_existence F hF ξ hξ a b h0 hJ
  have heq : EqOn (fun t => fderiv ℝ (fun η => flow F t η) ξ) Y (Icc a b) :=
    fun t ht => (state_derivative F hF ξ hξ a b h0 hJ Y hY t ht).fderiv
  refine ⟨hY.1.congr (fun t ht => heq ht), ?_⟩
  intro t ht
  rw [heq ht, hY.2 t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  exact congrArg (fun M => (coefficient F ξ r).comp M)
    (heq (ordConnected_Icc.uIcc_subset h0 ht hr)).symm

/-- Full maximal-domain state derivative, continuous locally jointly in time
and state and characterized uniquely by its first variational equation. -/
theorem maximal_domain_derivative :
    Specs.D13Unified.Ch06.StateDerivative.MaximalDomainDerivative.{u} := by
  intro E _ _ _ F hF
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hdiff (q : ℝ × E) (hq : q ∈ flowDomain F) :
      HasFDerivAt (fun η => flow F q.1 η) (fderiv ℝ (fun η => flow F q.1 η) q.2) q.2 := by
    have hx := flow_ivp F hF hq.1
    obtain ⟨a, b, h0, ht, hJ⟩ := Ch05.OpenDomain.compact_enclosure
      (flowInterval F q.2) hx.2.1 hq.2
    have h0' : 0 ∈ Icc a b := ⟨h0.1.le,h0.2.le⟩
    have hv := derivative_isVariation F hF hq.1 h0' hJ
    exact state_derivative F hF q.2 hq.1 a b h0' hJ _ hv q.1 ⟨ht.1.le,ht.2.le⟩
  refine ⟨hdiff, ?_, ?_⟩
  · intro q hq
    have hx := flow_ivp F hF hq.1
    obtain ⟨a, b, h0, ht, hJ⟩ := Ch05.OpenDomain.compact_enclosure
      (flowInterval F q.2) hx.2.1 hq.2
    have h0' : 0 ∈ Icc a b := ⟨h0.1.le,h0.2.le⟩
    obtain ⟨V, hVo, hVq, hVad, hVJ, Y, hY, hYc⟩ :=
      local_joint_variation F hF q.2 hq.1 a b h0' hJ
    have hnhds : Icc a b ×ˢ V ∈ 𝓝 q := prod_mem_nhds
      (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self) (hVo.mem_nhds hVq)
    have heq : (fun r : ℝ × E => fderiv ℝ (fun η => flow F r.1 η) r.2) =ᶠ[𝓝 q]
        (fun r : ℝ × E => Y r.2 r.1) := by
      filter_upwards [hnhds] with r hr
      exact (state_derivative F hF r.2 (hVad hr.2) a b h0' (hVJ r.2 hr.2)
        (Y r.2) (hY r.2 hr.2) r.1 hr.1).fderiv
    exact ((hYc.continuousAt hnhds).congr_of_eventuallyEq heq).continuousWithinAt
  · intro ξ hξ
    have hx := flow_ivp F hF hξ
    have hcompact (t : ℝ) (ht : t ∈ (flowInterval F ξ).carrier) :=
      Ch05.OpenDomain.compact_enclosure (flowInterval F ξ) hx.2.1 ht
    have hinit : fderiv ℝ (fun η => flow F 0 η) ξ = ContinuousLinearMap.id ℝ E := by
      obtain ⟨a, b, h0, ht, hJ⟩ := hcompact 0 hx.2.1
      exact (variation_differential F hF hξ ⟨h0.1.le,h0.2.le⟩ hJ
        (derivative_isVariation F hF hξ ⟨h0.1.le,h0.2.le⟩ hJ)).1
    refine ⟨hinit, ?_, ?_⟩
    · intro t ht
      obtain ⟨a, b, h0, ht', hJ⟩ := hcompact t ht
      have hd := (variation_differential F hF hξ ⟨h0.1.le,h0.2.le⟩ hJ
        (derivative_isVariation F hF hξ ⟨h0.1.le,h0.2.le⟩ hJ)).2 t ⟨ht'.1.le,ht'.2.le⟩
      exact hd.hasDerivAt (mem_of_superset (Ioo_mem_nhds ht'.1 ht'.2) Ioo_subset_Icc_self)
    · intro Z hZ hZ0 hZd t ht
      obtain ⟨a, b, h0, ht', hJ⟩ := hcompact t ht
      have h0' : 0 ∈ Icc a b := ⟨h0.1.le,h0.2.le⟩
      have hZc := hZ.mono hJ
      have hg : ContinuousOn (fun r => (coefficient F ξ r).comp (Z r)) (Icc a b) :=
        (continuousOn_coefficient F hF hξ hJ).clm_comp hZc
      have hZv : IsVariation F ξ a b Z := by
        refine ⟨hZc, ?_⟩
        intro r hr
        rw [integral_eq_sub_on_interval ordConnected_Icc hZc hg
          (fun r hr => (hZd r (hJ hr)).hasDerivWithinAt) h0' hr, hZ0]
        exact (add_sub_cancel (ContinuousLinearMap.id ℝ E) (Z r)).symm
      exact (state_derivative F hF ξ hξ a b h0' hJ Z hZv t
        ⟨ht'.1.le,ht'.2.le⟩).fderiv.symm

end D13Unified.Ch06.StateDerivative
